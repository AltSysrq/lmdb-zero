// Copyright 2016 FullContact, Inc
// Copyright 2017, 2018 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cmp::{Ord, Ordering};
use std::ffi::CString;
use std::mem;
use std::ptr;
use libc::c_int;

use ffi;
use supercow::Supercow;

use env::{self, Environment};
use error::{Error, Result};
use mdb_vals::*;
use traits::*;
use tx::TxHandle;

/// Flags used when opening databases.
pub mod db {
    use ffi;
    use libc;

    bitflags! {
        /// Flags used when opening databases.
        pub struct Flags : libc::c_uint {
            /// Keys are strings to be compared in reverse order, from the end
            /// of the strings to the beginning. By default, Keys are treated
            /// as strings and compared from beginning to end.
            ///
            /// NOTE: This is *not* reverse sort, but rather right-to-left
            /// comparison.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"), &lmdb::DatabaseOptions::new(
            ///     lmdb::db::REVERSEKEY | lmdb::db::CREATE)).unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   let f = lmdb::put::Flags::empty();
            ///   access.put(&db, "Germany", "Berlin", f).unwrap();
            ///   access.put(&db, "Latvia", "Rīga", f).unwrap();
            ///   access.put(&db, "France", "Paris", f).unwrap();
            ///
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   // The keys are compared as if we had input "aivtaL", "ecnarF",
            ///   // and "ynamreG", so "Latvia" comes first and "Germany" comes
            ///   // last.
            ///   assert_eq!(("Latvia", "Rīga"), cursor.first(&access).unwrap());
            ///   assert_eq!(("Germany", "Berlin"), cursor.last(&access).unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const REVERSEKEY = ffi::MDB_REVERSEKEY;
            /// Duplicate keys may be used in the database. (Or, from another
            /// perspective, keys may have multiple data items, stored in
            /// sorted order.) By default keys must be unique and may have only
            /// a single data item.
            ///
            /// ## Example
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("example"), &lmdb::DatabaseOptions::new(
            ///     lmdb::db::DUPSORT | lmdb::db::CREATE)).unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   let f = lmdb::put::Flags::empty();
            ///   access.put(&db, "Fruit", "Orange", f).unwrap();
            ///   access.put(&db, "Fruit", "Apple", f).unwrap();
            ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
            ///
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   assert_eq!(("Fruit", "Apple"),
            ///              cursor.seek_k_both(&access, "Fruit").unwrap());
            ///   assert_eq!(("Fruit", "Orange"), cursor.next(&access).unwrap());
            ///   assert_eq!(("Veggie", "Carrot"), cursor.next(&access).unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const DUPSORT = ffi::MDB_DUPSORT;
            /// Keys are binary integers in native byte order, either
            /// `libc::c_uint` or `libc::size_t`, and will be sorted as such.
            /// The keys must all be of the same size.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// use lmdb::unaligned as u;
            ///
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"), &lmdb::DatabaseOptions::new(
            ///     lmdb::db::INTEGERKEY | lmdb::db::CREATE)).unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   let f = lmdb::put::Flags::empty();
            ///   // Write the keys in native byte order.
            ///   // Note that on little-endian systems this means a
            ///   // byte-by-byte comparison would not order the keys the way
            ///   // one might expect.
            ///   access.put(&db, &42u32, "Fourty-two", f).unwrap();
            ///   access.put(&db, &65536u32, "65'536", f).unwrap();
            ///   access.put(&db, &0u32, "Zero", f).unwrap();
            ///
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   // But because we used `INTEGERKEY`, they are in fact sorted
            ///   // ascending by integer value.
            ///   assert_eq!((u(&0u32), "Zero"), cursor.first(&access).unwrap());
            ///   assert_eq!((u(&42u32), "Fourty-two"), cursor.next(&access).unwrap());
            ///   assert_eq!((u(&65536u32), "65'536"), cursor.next(&access).unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const INTEGERKEY = ffi::MDB_INTEGERKEY;
            /// This flag may only be used in combination with `DUPSORT`. This
            /// option tells the library that the data items for this database
            /// are all the same size, which allows further optimizations in
            /// storage and retrieval. When all data items are the same size,
            /// the `get_multiple` and `next_multiple` cursor operations may be
            /// used to retrieve multiple items at once.
            ///
            /// ## Notes
            ///
            /// There are no runtime checks that values are actually the same
            /// size; failing to uphold this constraint may result in
            /// unpredictable behaviour.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// use lmdb::Unaligned as U;
            /// use lmdb::LmdbResultExt;
            ///
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"), &lmdb::DatabaseOptions::new(
            ///     lmdb::db::DUPSORT | lmdb::db::DUPFIXED |
            ///     lmdb::db::INTEGERDUP | lmdb::db::CREATE))
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   let f = lmdb::put::Flags::empty();
            ///   // Map strings to their constituent chars
            ///   for s in &["foo", "bar", "xyzzy"] {
            ///     for c in s.chars() {
            ///       access.put(&db, *s, &c, f).unwrap();
            ///     }
            ///   }
            ///
            ///   // Read in all the chars of "xyzzy" in sorted order via
            ///   // cursoring.
            ///   // Note that we have to read `u32`s because `char`s are not
            ///   // directly convertable from byte arrays.
            ///   let mut xyzzy: Vec<u32> = Vec::new();
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   cursor.seek_k::<str,U<u32>>(&access, "xyzzy").unwrap();
            ///   loop {
            ///     let chars = if xyzzy.is_empty() {
            ///       // First page.
            ///       // Note that in this example we probably get everything
            ///       // on the first page, but with more values we'd need to
            ///       // use `next_multiple` to get the rest.
            ///       cursor.get_multiple::<[U<u32>]>(&access).unwrap()
            ///     } else {
            ///       // .to_opt() to turn NOTFOUND into None
            ///       match cursor.next_multiple::<[U<u32>]>(&access).to_opt() {
            ///         // Ok if there's still more for the current key
            ///         Ok(Some(c)) => c,
            ///         // NOTFOUND error (=> None) at end of key
            ///         Ok(None) => break,
            ///         // Handle other errors
            ///         Err(e) => panic!("LMDB error: {}", e),
            ///       }
            ///     };
            ///     for ch in chars {
            ///       xyzzy.push(ch.get());
            ///     }
            ///   }
            ///   // Now we've read in all the values in sorted order.
            ///   assert_eq!(&['x' as u32, 'y' as u32, 'z' as u32],
            ///              &xyzzy[..]);
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const DUPFIXED = ffi::MDB_DUPFIXED;
            /// This option specifies that duplicate data items are binary
            /// integers, similar to `INTEGERKEY` keys.
            const INTEGERDUP = ffi::MDB_INTEGERDUP;
            /// This option specifies that duplicate data items should be
            /// compared as strings in reverse order.
            ///
            /// NOTE: As with `REVERSEKEY`, this indicates a right-to-left
            /// comparison, *not* an order reversal.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"), &lmdb::DatabaseOptions::new(
            ///     lmdb::db::DUPSORT | lmdb::db::REVERSEDUP |
            ///     lmdb::db::CREATE)).unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   let f = lmdb::put::Flags::empty();
            ///   access.put(&db, "Colorado", "Denver", f).unwrap();
            ///   access.put(&db, "Colorado", "Golden", f).unwrap();
            ///   access.put(&db, "Colorado", "Lakewood", f).unwrap();
            ///
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   // doowekaL, nedloG, revneD
            ///   assert_eq!(("Colorado", "Lakewood"), cursor.first(&access).unwrap());
            ///   assert_eq!(("Colorado", "Golden"), cursor.next(&access).unwrap());
            ///   assert_eq!(("Colorado", "Denver"), cursor.next(&access).unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const REVERSEDUP = ffi::MDB_REVERSEDUP;
            /// Create the named database if it doesn't exist. This option is
            /// not allowed in a read-only environment.
            const CREATE = ffi::MDB_CREATE;
        }
    }
}

#[derive(Debug)]
struct DbHandle<'a> {
    env: Supercow<'a, Environment>,
    dbi: ffi::MDB_dbi,
    close_on_drop: bool,
}

impl<'a> Drop for DbHandle<'a> {
    fn drop(&mut self) {
        if self.close_on_drop {
            env::dbi_close(&self.env, self.dbi);
        }
    }
}

/// A handle on an LMDB database within an environment.
///
/// Note that in many respects the RAII aspect of this struct is more a matter
/// of convenience than correctness. In particular, if holding a read
/// transaction open, it is possible to obtain a handle to a database created
/// after that transaction started, but this handle will not point to anything
/// within that transaction.
///
/// The library does, however, guarantee that there will be at most one
/// `Database` object with the same dbi and environment per process.
///
/// ## Lifetime
///
/// A `Database` in borrowed mode must be strictly outlived by its
/// `Environment`.
///
/// `'a` is covariant: given two lifetimes `'x` and `'y` where `'x: 'y`, a
/// `&Database<'x>` will implicitly coerce to `&Database<'y>`.
///
/// ```rust,norun
/// # #![allow(dead_code)]
/// # extern crate lmdb_zero as lmdb;
/// # fn main() { }
/// #
/// fn convariance<'x, 'y>(db: &lmdb::Database<'x>)
/// where 'x: 'y {
///   let _db2: &lmdb::Database<'y> = db;
/// }
/// ```
///
/// Because of this property, if you need to hold onto an `&lmdb::Database` and
/// must explicitly name both lifetimes, it is usually best to use the same
/// lifetime for both the reference and the parameter, eg `&'x lmdb::Database<'x>`.
///
/// ## Ownership Modes
///
/// All three ownership modes are fully supported. Most examples use borrowed
/// mode, which is used by simply passing an `&'env Environment` to `open`.
///
/// ### Owned Mode
///
/// Owned mode is useful when your application only uses one `Database`; this
/// alleviates the need to track both the `Environment` and the `Database`.
///
/// ```
/// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
/// fn setup() -> lmdb::Database<'static> {
///   // N.B. Unneeded type and lifetime annotations included for clarity.
///   let env: lmdb::Environment = create_env();
///   // Move `env` into the new `Database` because we only want to use the
///   // default database. Since it owns the `Environment`, its lifetime
///   // parameter is simply `'static`.
///   let db: lmdb::Database<'static> = lmdb::Database::open(
///     env, None, &lmdb::DatabaseOptions::defaults()).unwrap();
///   // And since it owns the `Environment`, we can even return it without
///   // worrying about `env`.
///   db
/// }
///
/// # fn main() {
/// let db = setup();
/// // Do stuff with `db`...
///
/// // When `db` is dropped, so is the inner `Environment`.
/// # }
/// ```
///
/// ### Shared Mode
///
/// Shared mode allows to have the `Database` hold on to the `Environment` via
/// an `Arc` instead of a bare reference. This has all the benefits of owned
/// mode and none of the drawbacks, but makes it harder to determine when
/// exactly the `Environment` gets dropped since this only happens after all
/// referents are (dynamically) dropped.
///
/// Without resorting to `unsafe`, shared mode is also the only way to define a
/// structure which holds both the `Environment` itself and its child
/// `Database` values.
///
/// ```
/// # #![allow(dead_code)]
/// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
/// use std::sync::Arc;
///
/// struct ApplicationContext {
///   env: Arc<lmdb::Environment>,
///   // You could of course also put these under `Arc`s as well, for example
///   // if using shared mode with transactions and/or cursors.
///   dict: lmdb::Database<'static>,
///   freq: lmdb::Database<'static>,
/// }
///
/// impl ApplicationContext {
///   fn into_env(self) -> Arc<lmdb::Environment> { self.env }
/// }
///
/// # fn main() {
/// let env = Arc::new(create_env());
/// let dict = lmdb::Database::open(
///   env.clone(), Some("dict"),
///   &lmdb::DatabaseOptions::create_map::<str>()).unwrap();
/// let freq = lmdb::Database::open(
///   env.clone(), Some("freq"),
///   &lmdb::DatabaseOptions::create_map::<str>()).unwrap();
///
/// let context = ApplicationContext {
///   env: env,
///   dict: dict,
///   freq: freq,
/// };
///
/// // Pass `context` around the application freely...
///
/// // We could just let `ApplicationContext` drop, but if we want to be
/// // absolutely sure we know when the `Environment` drops (by panicking if
/// // it doesn't do so when we want), we can disassemble the struct and check
/// // manually.
/// let env = context.into_env(); // Databases get dropped
/// Arc::try_unwrap(env).unwrap(); // Regain ownership of `Environment`,
///                                // then drop it.
/// # }
/// ```
#[derive(Debug)]
pub struct Database<'a> {
    db: DbHandle<'a>,
}

/// Describes the options used for creating or opening a database.
#[derive(Clone,Debug)]
pub struct DatabaseOptions {
    /// The integer flags to pass to LMDB
    pub flags: db::Flags,
    key_cmp: Option<ffi::MDB_cmp_func>,
    val_cmp: Option<ffi::MDB_cmp_func>,
}

impl DatabaseOptions {
    /// Creates a new `DatabaseOptions` with the given flags, using natural key
    /// and value ordering.
    pub fn new(flags: db::Flags) -> DatabaseOptions {
        DatabaseOptions {
            flags: flags,
            key_cmp: None,
            val_cmp: None,
        }
    }

    /// Synonym for `DatabaseOptions::new(db::Flags::empty())`.
    ///
    /// Note that this does not even have `db::CREATE` set. This is most useful
    /// when opening the anonymous default database.
    pub fn defaults() -> DatabaseOptions {
        DatabaseOptions::new(db::Flags::empty())
    }

    /// Sorts keys in the database by interpreting them as `K` and using their
    /// comparison order. Keys which fail to convert are considered equal.
    ///
    /// The comparison function is called whenever it is necessary to compare a
    /// key specified by the application with a key currently stored in the
    /// database. If no comparison function is specified, and no special key
    /// flags were specified in the options, the keys are compared lexically,
    /// with shorter keys collating before longer keys.
    ///
    /// ## Warning
    ///
    /// This function must be called before any data access functions are used,
    /// otherwise data corruption may occur. The same comparison function must
    /// be used by every program accessing the database, every time the
    /// database is used.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// #[repr(C, packed)]
    /// #[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
    /// struct MyStruct {
    ///   x: i32,
    ///   y: i32,
    /// }
    /// unsafe impl lmdb::traits::LmdbRaw for MyStruct { }
    /// unsafe impl lmdb::traits::LmdbOrdKey for MyStruct { }
    ///
    /// fn my(x: i32, y: i32) -> MyStruct {
    ///   MyStruct { x: x, y: y }
    /// }
    ///
    /// # fn main() {
    /// # let env = create_env();
    /// let mut opts = lmdb::DatabaseOptions::new(lmdb::db::CREATE);
    /// opts.sort_keys_as::<MyStruct>();
    /// let db = lmdb::Database::open(&env, Some("example"), &opts).unwrap();
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, &my(0, 0), "origin", f).unwrap();
    ///   access.put(&db, &my(-1, 0), "x=-1", f).unwrap();
    ///   access.put(&db, &my(1, 0), "x=+1", f).unwrap();
    ///   access.put(&db, &my(0, -1), "y=-1", f).unwrap();
    ///
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   // The keys are sorted by the Rust-derived comparison. The default
    ///   // byte-string comparison would have resulted in (0,0), (0,-1),
    ///   // (1,0), (-1,0).
    ///   assert_eq!((&my(-1, 0), "x=-1"), cursor.first(&access).unwrap());
    ///   assert_eq!((&my(0, -1), "y=-1"), cursor.next(&access).unwrap());
    ///   assert_eq!((&my(0, 0), "origin"), cursor.next(&access).unwrap());
    ///   assert_eq!((&my(1, 0), "x=+1"), cursor.next(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    pub fn sort_keys_as<K : LmdbOrdKey + ?Sized>(&mut self) {
        self.key_cmp = Some(DatabaseOptions::entry_cmp_as::<K>);
    }

    /// Sorts duplicate values in the database by interpreting them as `V` and
    /// using their comparison order. Values which fail to convert are
    /// considered equal.
    ///
    /// This comparison function is called whenever it is necessary to compare
    /// a data item specified by the application with a data item currently
    /// stored in the database. This function only takes effect if the database
    /// iss opened with the `DUPSORT` flag. If no comparison function is
    /// specified, and no special key flags were specified in the flags of
    /// these options, the data items are compared lexically, with shorter
    /// items collating before longer items.
    ///
    /// ## Warning
    ///
    /// This function must be called before any data access functions are used,
    /// otherwise data corruption may occur. The same comparison function must
    /// be used by every program accessing the database, every time the
    /// database is used.
    pub fn sort_values_as<V : LmdbOrdKey + ?Sized>(&mut self) {
        self.val_cmp = Some(DatabaseOptions::entry_cmp_as::<V>);
    }

    /// Concisely creates a `DatabaseOptions` to configure a database to have a
    /// 1:1 mapping using the given key type.
    ///
    /// The flags always have `db::CREATE` set. If `K` is understood by LMDB as
    /// an integer, `db::INTEGERKEY` is set. Otherwise, unless `K` sorts
    /// properly via byte-string comparison, `sort_keys_as` is called to
    /// configure the database to use `K`'s `Ord` implementation.
    pub fn create_map<K : LmdbOrdKey + ?Sized>() -> Self {
        let mut this = DatabaseOptions::new(db::CREATE);
        if K::ordered_as_integer() {
            this.flags |= db::INTEGERKEY;
        } else if !K::ordered_by_bytes() {
            this.sort_keys_as::<K>();
        }
        this
    }

    /// Concisely creates a `DatabaseOptions` to configure a database to have a
    /// 1:M mapping using the given key and unsized value types.
    ///
    /// The flags are configured as described with `create_map` with
    /// `db::DUPSORT` added. If `V` is understood by LMDB as an integer,
    /// `INTEGERDUP` is set. Otherwise, if `V` is not byte-string comparable,
    /// `sort_values_as` is used to order values by `V`'s `Ord`
    /// implementation.
    pub fn create_multimap_unsized<K : LmdbOrdKey + ?Sized,
                                   V : LmdbOrdKey + ?Sized>
        () -> Self
    {
        let mut this = DatabaseOptions::create_map::<K>();
        this.flags |= db::DUPSORT;
        if V::ordered_as_integer() {
            this.flags |= db::INTEGERDUP;
        } else if !V::ordered_by_bytes() {
            this.sort_values_as::<V>();
        }
        this
    }

    /// Concisely creates a `DatabaseOptions` to configure a database to have a
    /// 1:M mapping using the given key and fixed-size value types.
    ///
    /// This is the same as `create_multimap_unsized`, except that `DUPFIXED`
    /// is additionally set unconditionally.
    pub fn create_multimap<K : LmdbOrdKey + ?Sized,
                           V : LmdbOrdKey + Sized>
        () -> Self
    {
        let mut this = DatabaseOptions::create_multimap_unsized::<K, V>();
        this.flags |= db::DUPFIXED;
        this
    }

    extern fn entry_cmp_as<V : LmdbOrdKey + ?Sized>(
        ap: *const ffi::MDB_val, bp: *const ffi::MDB_val) -> c_int
    {
        match unsafe {
            V::from_lmdb_bytes(mdb_val_as_bytes(&ap, &*ap)).cmp(
                &V::from_lmdb_bytes(mdb_val_as_bytes(&bp, &*bp)))
        } {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
}

impl<'a> Database<'a> {
    /// Open a database in the environment.
    ///
    /// A database handle denotes the name and parameters of a database,
    /// independently of whether such a database exists. The database handle is
    /// implicitly closed when the `Database` object is dropped.
    ///
    /// To use named databases (with `name != None`),
    /// `EnvBuilder::set_maxdbs()` must have been called to reserve space for
    /// the extra databases. Database names are keys in the unnamed database,
    /// and may be read but not written.
    ///
    /// Transaction-local databases are not supported because the resulting
    /// ownership semantics are not expressible in rust. This call implicitly
    /// creates a write transaction and uses it to create the database, then
    /// commits it on success.
    ///
    /// One may not open the same database handle multiple times. Attempting to
    /// do so will result in the `Error::Reopened` error.
    ///
    /// Beware that if the underlying `MDB_env` is being shared (for example,
    /// with native code via `Environment::borrow_raw`), using this method to
    /// open a `Database` can result in premature closing of the database
    /// handle since the `Database` is presumed to own the database handle, but
    /// LMDB will return a shared handle if the database is already open
    /// elsewhere. The [`disown()`](#method.disown) method can be used to
    /// ensure the `Database` does not assume ownership of the database
    /// handle.
    ///
    /// ## Examples
    ///
    /// ### Open the default database with default options
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # #[allow(unused_vars)]
    /// # fn main() {
    /// # let env = create_env();
    /// {
    ///   let db = lmdb::Database::open(
    ///     &env, None, &lmdb::DatabaseOptions::defaults()).unwrap();
    ///   // Do stuff with `db`
    /// } // The `db` handle is released
    /// # }
    /// ```
    ///
    /// ### Open a named database, creating it if it doesn't exist
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # #[allow(unused_vars)]
    /// # fn main() {
    /// # let env = create_env();
    /// // NOT SHOWN: Call `EnvBuilder::set_maxdbs()` with a value greater than
    /// // one so that there is space for the named database(s).
    /// {
    ///   let db = lmdb::Database::open(
    ///     &env, Some("example-db"), &lmdb::DatabaseOptions::new(
    ///       lmdb::db::CREATE)).unwrap();
    ///   // Do stuff with `db`
    /// } // The `db` handle is released
    /// # }
    /// ```
    ///
    /// ### Trying to open the same database more than once
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # #[allow(unused_vars)]
    /// # fn main() {
    /// # let env = create_env();
    /// {
    ///   let db = lmdb::Database::open(
    ///     &env, None, &lmdb::DatabaseOptions::defaults()).unwrap();
    ///   // Can't open the same database twice
    ///   assert!(lmdb::Database::open(
    ///     &env, None, &lmdb::DatabaseOptions::defaults()).is_err());
    /// }
    /// # }
    /// ```
    ///
    /// ### Open a database on a read-only environment
    ///
    /// Databases can be opened in read-only environments as long as they
    /// already exist.
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let tdir = tempdir::TempDir::new_in(".", "lmdbzero").unwrap();
    /// # {
    /// #   let mut builder = lmdb::EnvBuilder::new().unwrap();
    /// #   builder.set_maxdbs(2).unwrap();
    /// #   let env = unsafe { builder.open(
    /// #     tdir.path().to_str().unwrap(),
    /// #     lmdb::open::Flags::empty(), 0o600).unwrap() };
    /// #   let db = lmdb::Database::open(
    /// #     &env, None, &lmdb::DatabaseOptions::defaults()).unwrap();
    /// # }
    /// # let env = {
    /// #   let mut builder = lmdb::EnvBuilder::new().unwrap();
    /// #   builder.set_maxdbs(2).unwrap();
    /// #   unsafe { builder.open(
    /// #     tdir.path().to_str().unwrap(),
    /// #     lmdb::open::RDONLY, 0o400).unwrap() }
    /// # };
    /// {
    ///   // Succeeds -- The DB already exists
    ///   let db = lmdb::Database::open(
    ///     &env, None,
    ///     &lmdb::DatabaseOptions::new(lmdb::db::Flags::empty())).unwrap();
    ///   // Fails -- Can't create a new one in read-only mode
    ///   assert!(lmdb::Database::open(
    ///     &env, Some("name"),
    ///     &lmdb::DatabaseOptions::new(lmdb::db::CREATE)).is_err());
    /// }
    /// # }
    /// ```
    pub fn open<E>(env: E, name: Option<&str>,
                   options: &DatabaseOptions)
                   -> Result<Database<'a>>
    where E : Into<Supercow<'a, Environment>> {
        let env: Supercow<'a, Environment> = env.into();

        let mut raw: ffi::MDB_dbi = 0;
        let name_cstr = match name {
            None => None,
            Some(s) => Some(try!(CString::new(s))),
        };
        let raw = unsafe {
            use env;
            // Locking the hash set here is also used to serialise calls to
            // `mdb_dbi_open()`, which are not permitted to be concurrent.
            let mut locked_dbis = env::env_open_dbis(&env).lock()
                .expect("open_dbis lock poisoned");

            let mut raw_tx: *mut ffi::MDB_txn = ptr::null_mut();
            let mut txn_flags = 0;
            if env.flags().unwrap().contains(env::open::RDONLY) {
                txn_flags = ffi::MDB_RDONLY;
            }
            lmdb_call!(ffi::mdb_txn_begin(
                env::env_ptr(&env), ptr::null_mut(), txn_flags, &mut raw_tx));
            let mut wrapped_tx = TxHandle(raw_tx); // For auto-closing etc
            lmdb_call!(ffi::mdb_dbi_open(
                raw_tx, name_cstr.as_ref().map_or(ptr::null(), |s| s.as_ptr()),
                options.flags.bits(), &mut raw));

            if !locked_dbis.insert(raw) {
                return Err(Error::Reopened)
            }

            if let Some(fun) = options.key_cmp {
                lmdb_call!(ffi::mdb_set_compare(raw_tx, raw, fun));
            }
            if let Some(fun) = options.val_cmp {
                lmdb_call!(ffi::mdb_set_dupsort(raw_tx, raw, fun));
            }

            try!(wrapped_tx.commit());
            raw
        };

        Ok(Database {
            db: DbHandle {
                env: env,
                dbi: raw,
                close_on_drop: true,
            }
        })
    }

    /// Wrap a raw `MDB_dbi` associated with this environment.
    ///
    /// This call assumes ownership of the `MDB_dbi`, and the resulting
    /// `Database` will close it on drop. If this is not desired, see
    /// [`borrow_raw()`](#method.borrow_raw) instead.
    ///
    /// ## Unsafety
    ///
    /// `raw` must reference a database currently open in `env`.
    ///
    /// The caller must ensure that nothing closes the handle until
    /// `into_raw()` is called and that nothing uses it after the `Database` is
    /// dropped normally.
    ///
    /// ## Panics
    ///
    /// Panics if `raw` is a handle already owned by `env`.
    pub unsafe fn from_raw<E>(env: E, raw: ffi::MDB_dbi) -> Self
    where E : Into<Supercow<'a, Environment>> {
        let env: Supercow<'a, Environment> = env.into();

        use env;
        {
            let mut locked_dbis = env::env_open_dbis(&env).lock()
                .expect("open_dbis lock poisoned");

            if !locked_dbis.insert(raw) {
                panic!("DBI {} already opened in this environment", raw);
            }
        }

        Database {
            db: DbHandle {
                env: env,
                dbi: raw,
                close_on_drop: true,
            }
        }
    }

    /// Wrap a raw `MDB_dbi` associated with this environment without taking
    /// ownership.
    ///
    /// This call does not assume ownership of `raw`, and as a result neither
    /// checks whether any other `Database`s exist with the same handle, nor
    /// records this particular handle in `env`'s list of owned databases.
    ///
    /// ## Unsafety
    ///
    /// `raw` must reference a database currently open in `env`.
    ///
    /// The caller must ensure that nothing closes the handle until the
    /// resulting `Database` is dropped.
    pub unsafe fn borrow_raw<E>(env: E, raw: ffi::MDB_dbi) -> Self
    where E : Into<Supercow<'a, Environment>> {
        Database {
            db: DbHandle {
                env: env.into(),
                dbi: raw,
                close_on_drop: false,
            }
        }
    }

    /// Deletes this database.
    ///
    /// This call implicitly creates a new write transaction to perform the
    /// operation, so that the lifetime of the database handle does not depend
    /// on the outcome. The database handle is closed implicitly by this
    /// operation.
    ///
    /// Note that the _other_ `mdb_drop` operation which simply clears the
    /// database is exposed through `WriteAccessor` and is transactional.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # #[allow(unused_vars)]
    /// # fn main() {
    /// # let env = create_env();
    /// // NOT SHOWN: Call `EnvBuilder::set_maxdbs()` with a value greater than
    /// // one so that there is space for the named database(s).
    /// {
    ///   let db = lmdb::Database::open(
    ///     &env, Some("example-db"), &lmdb::DatabaseOptions::new(
    ///       lmdb::db::CREATE)).unwrap();
    ///   // Do stuff with `db`
    ///
    ///   // Delete the database itself. This also consumes `db`.
    ///   db.delete().unwrap();
    ///
    ///   // We can now recreate the database if we so desire.
    ///   // Note that you should not use delete+open to clear a database; use
    ///   // `WriteAccessor::clear_db()` to do that.
    ///   let db = lmdb::Database::open(
    ///     &env, Some("example-db"), &lmdb::DatabaseOptions::new(
    ///       lmdb::db::CREATE)).unwrap();
    /// }
    /// # }
    /// ```
    pub fn delete(self) -> Result<()> {
        try!(env::dbi_delete(&self.db.env, self.db.dbi));
        mem::forget(self.db);
        Ok(())
    }

    /// Returns a reference to the `Environment` to which this `Database`
    /// belongs.
    ///
    /// This can be used to elide needing to pass both an `&Environment` and an
    /// `&Database` around, but is also useful for the use-case wherein the
    /// `Database` owns the `Environment`.
    ///
    /// Because this may borrow an `Environment` owned by this `Database`, the
    /// lifetime of the returned reference is dependent on self rather than
    /// being `'env`. (In fact, `'env` is usually `'static` if the
    /// `Environment` is owned by the `Database`, so returning `&'env Environment`
    /// is impossible anyway.)
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # #[allow(unused_vars)]
    /// # fn main() {
    /// let env: lmdb::Environment = create_env();
    /// // We only want one `Database`, so don't bother keeping both variables
    /// // around and instead let the `Database` own the `Environment`.
    /// let db = lmdb::Database::open(
    ///   env, None, &lmdb::DatabaseOptions::defaults()).unwrap();
    ///
    /// // `env` has been consumed, but we can still do useful things by
    /// // getting a reference to the inner value.
    /// let txn = lmdb::ReadTransaction::new(db.env()).unwrap();
    ///
    /// // Do stuff with `txn`, etc.
    /// # }
    /// ```
    #[inline]
    pub fn env(&self) -> &Environment {
        &*self.db.env
    }

    /// Checks that `other_env` is the same as the environment on this
    /// `Database`.
    ///
    /// If it matches, returns `Ok(())`; otherwise, returns `Err`.
    pub fn assert_same_env(&self, other_env: &Environment)
                           -> Result<()> {
        if &*self.db.env as *const Environment !=
            other_env as *const Environment
        {
            Err(Error::Mismatch)
        } else {
            Ok(())
        }
    }

    /// Returns the underlying integer handle for this database.
    ///
    /// ## Deprecated
    ///
    /// Renamed to `as_raw()` for consistency.
    #[deprecated(since = "0.4.4", note = "use as_raw() instead")]
    pub fn dbi(&self) -> ffi::MDB_dbi {
        self.db.dbi
    }

    /// Returns the underlying integer handle for this database.
    #[inline]
    pub fn as_raw(&self) -> ffi::MDB_dbi {
        self.db.dbi
    }

    /// Consume self, returning the underlying integer handle for this
    /// database.
    ///
    /// If this `Database` owns the database handle, it is not closed, but it
    /// is removed from the list of handles owned by the `Environment`.
    pub fn into_raw(mut self) -> ffi::MDB_dbi {
        self.disown();
        self.db.dbi
    }

    /// Prevent the underlying `MDB_dbi` handle from being closed when this
    /// `Database` is dropped.
    ///
    /// This is useful when sharing an `MDB_env` with a native library, as in
    /// such a context the `MDB_dbi` handles are also involuntarily shared.
    pub fn disown(&mut self) {
        use env;

        if self.db.close_on_drop {
            let mut locked_dbis = env::env_open_dbis(&self.db.env).lock()
                .expect("open_dbis lock poisoned");

            locked_dbis.remove(&self.db.dbi);
            self.db.close_on_drop = false;
        }
    }
}

#[cfg(test)]
mod test {
    use test_helpers::*;
    use dbi::*;
    use tx::*;

    #[test]
    fn disown_allows_sharing() {
        let env = create_env();
        let mut db1 = defdb(&env);
        db1.disown();
        let db2 = defdb(&env);

        let tx = WriteTransaction::new(&env).unwrap();
        tx.access().put(&db1, "foo", "bar", put::Flags::empty()).unwrap();
        tx.commit().unwrap();
        drop(db1);

        let tx = ReadTransaction::new(&env).unwrap();
        assert_eq!("bar", tx.access().get::<str,str>(&db2, "foo").unwrap());
    }

    #[test]
    fn borrow_raw_allows_sharing() {
        let env = create_env();
        let db1 = defdb(&env);
        let db2 = unsafe { Database::borrow_raw(&env, db1.as_raw()) };

        let tx = WriteTransaction::new(&env).unwrap();
        tx.access().put(&db2, "foo", "bar", put::Flags::empty()).unwrap();
        tx.commit().unwrap();
        drop(db2);

        let tx = ReadTransaction::new(&env).unwrap();
        assert_eq!("bar", tx.access().get::<str,str>(&db1, "foo").unwrap());
    }
}
