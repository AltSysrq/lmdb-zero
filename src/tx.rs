// Copyright 2016 FullContact, Inc
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cell::Cell;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr;
use libc::c_uint;

use ffi;
use ffi2;
use supercow::{Supercow, NonSyncSupercow};

use env::{self, Environment, Stat};
use dbi::{db, Database};
use error::{Error, Result};
use mdb_vals::*;
use traits::*;
use cursor::{self, Cursor, StaleCursor};

/// Flags used when calling the various `put` functions.
pub mod put {
    use ffi;
    use libc;

    bitflags! {
        /// Flags used when calling the various `put` functions.
        ///
        /// Note that `RESERVE` and `MULTIPLE` are not exposed in these flags
        /// because their memory ownership and/or parameter semantics are
        /// different. `CURRENT` is expressed separately on the cursor
        /// functions.
        pub struct Flags : libc::c_uint {
            /// Enter the new key/data pair only if it does not already appear
            /// in the database. This flag may only be specified if the
            /// database was opened with `DUPSORT`. The function will return
            /// `KEYEXIST` if the key/data pair already appears in the
            /// database.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"),
            ///   &lmdb::DatabaseOptions::create_multimap_unsized::<str,str>())
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
            ///   access.put(&db, "Fruit", "Orange", lmdb::put::Flags::empty()).unwrap();
            ///   // Duplicate, but that's OK by default
            ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
            ///   // `NODUPDATA` blocks adding an identical item
            ///   assert!(access.put(&db, "Fruit", "Apple", lmdb::put::NODUPDATA).is_err());
            ///   // But doesn't affect pairs not already present
            ///   access.put(&db, "Fruit", "Durian", lmdb::put::NODUPDATA).unwrap();
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            ///
            /// When used on a cursor, the cursor is positioned at the
            /// conflicting key/value pair if this results in a `KEYEXIST`
            /// error.
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"),
            ///   &lmdb::DatabaseOptions::create_multimap_unsized::<str,str>())
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
            ///   access.put(&db, "Fruit", "Orange", lmdb::put::Flags::empty()).unwrap();
            ///   access.put(&db, "Fruit", "Durian", lmdb::put::Flags::empty()).unwrap();
            ///
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   assert_eq!(Err(lmdb::Error::Code(lmdb::error::KEYEXIST)),
            ///              cursor.put(&mut access, "Fruit", "Durian",
            ///                         lmdb::put::NODUPDATA));
            ///   assert_eq!(("Fruit", "Durian"), cursor.get_current(&access).unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const NODUPDATA = ffi::MDB_NODUPDATA;
            /// Enter the new key/data pair only if the key does not already
            /// appear in the database. The function will return `KEYEXIST` if
            /// the key already appears in the database, even if the database
            /// supports duplicates (`DUPSORT`).
            ///
            /// ## Examples
            ///
            /// ### In a 1:1 database
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, None, &lmdb::DatabaseOptions::defaults())
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
            ///   // By default, collisions overwrite the old value
            ///   access.put(&db, "Fruit", "Orange", lmdb::put::Flags::empty()).unwrap();
            ///   assert_eq!("Orange", access.get::<str,str>(&db, "Fruit").unwrap());
            ///   // But `NOOVERWRITE` prevents that
            ///   assert!(access.put(&db, "Fruit", "Durian", lmdb::put::NOOVERWRITE).is_err());
            ///   assert_eq!("Orange", access.get::<str,str>(&db, "Fruit").unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            ///
            /// ### In a `DUPSORT` database
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"),
            ///   &lmdb::DatabaseOptions::create_multimap_unsized::<str,str>())
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   // Ordinarily, we can add multiple items per key
            ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
            ///   access.put(&db, "Fruit", "Orange", lmdb::put::Flags::empty()).unwrap();
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   cursor.seek_k::<str,str>(&access, "Fruit").unwrap();
            ///   assert_eq!(2, cursor.count().unwrap());
            ///
            ///   // But this can be prevented with `NOOVERWRITE`
            ///   access.put(&db, "Veggie", "Carrot", lmdb::put::NOOVERWRITE).unwrap();
            ///   assert!(access.put(&db, "Veggie", "Squash", lmdb::put::NOOVERWRITE).is_err());
            ///   cursor.seek_k::<str,str>(&access, "Veggie").unwrap();
            ///   assert_eq!(1, cursor.count().unwrap());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            // TODO: "The data parameter will be set to point to the existing
            // item." We should provide functionality to support that.
            const NOOVERWRITE = ffi::MDB_NOOVERWRITE;
            /// Append the given key/data pair to the end of the database. This
            /// option allows fast bulk loading when keys are already known to
            /// be in the correct order. Loading unsorted keys with this flag
            /// will cause a `KEYEXIST` error.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, None, &lmdb::DatabaseOptions::defaults())
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   // Load values in ascending order
            ///   access.put(&db, "France", "Paris", lmdb::put::APPEND).unwrap();
            ///   access.put(&db, "Germany", "Berlin", lmdb::put::APPEND).unwrap();
            ///   access.put(&db, "Latvia", "Rīga", lmdb::put::APPEND).unwrap();
            ///   // Error if you violate ordering
            ///   assert!(access.put(&db, "Armenia", "Yerevan", lmdb::put::APPEND)
            ///           .is_err());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const APPEND = ffi::MDB_APPEND;
            /// As with `APPEND` above, but for sorted dup data.
            const APPENDDUP = ffi::MDB_APPENDDUP;
        }
    }
}

/// Flags used when deleting items.
pub mod del {
    use ffi;
    use libc;

    bitflags! {
        /// Flags used when deleting items via cursors.
        pub struct Flags : libc::c_uint {
            /// Delete all of the data items for the current key instead of
            /// just the current item. This flag may only be specified if the
            /// database was opened with `DUPSORT`.
            ///
            /// ## Example
            ///
            /// ```
            /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
            /// # fn main() {
            /// # let env = create_env();
            /// let db = lmdb::Database::open(
            ///   &env, Some("reversed"),
            ///   &lmdb::DatabaseOptions::create_multimap_unsized::<str,str>())
            ///   .unwrap();
            /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
            /// {
            ///   let mut access = txn.access();
            ///   let f = lmdb::put::Flags::empty();
            ///   access.put(&db, "Fruit", "Apple", f).unwrap();
            ///   access.put(&db, "Fruit", "Orange", f).unwrap();
            ///   access.put(&db, "Fruit", "Durian", f).unwrap();
            ///
            ///   let mut cursor = txn.cursor(&db).unwrap();
            ///   cursor.seek_kv("Fruit", "Durian").unwrap();
            ///   // By default, only the current item is deleted.
            ///   cursor.del(&mut access, lmdb::del::Flags::empty()).unwrap();
            ///   cursor.seek_k::<str,str>(&access, "Fruit").unwrap();
            ///   assert_eq!(2, cursor.count().unwrap());
            ///   // But with `NODUPDATA`, they will all go away
            ///   cursor.del(&mut access, lmdb::del::NODUPDATA).unwrap();
            ///   assert!(cursor.seek_k::<str,str>(&access, "Fruit").is_err());
            /// }
            /// txn.commit().unwrap();
            /// # }
            /// ```
            const NODUPDATA = ffi::MDB_NODUPDATA;
        }
    }
}

// This is internal, but used by other parts of the library
#[derive(Debug)]
pub struct TxHandle(pub *mut ffi::MDB_txn);

impl Drop for TxHandle {
    fn drop(&mut self) {
        if !self.0.is_null() {
            unsafe {
                ffi::mdb_txn_abort(self.0);
            }
            self.0 = ptr::null_mut();
        }
    }
}

impl TxHandle {
    pub unsafe fn commit(&mut self) -> Result<()> {
        let txn_p = mem::replace(&mut self.0, ptr::null_mut());
        lmdb_call!(ffi::mdb_txn_commit(txn_p));
        Ok(())
    }
}

/// Base functionality for an LMDB transaction.
///
/// The type is "const" in a similar usage to the modifier in C: One cannot use
/// it to make any modifications, but also cannot rely on it actually being
/// read-only. `ConstTransaction`s are used to write code that can operate in
/// either kind of transaction.
///
/// Unlike most other LMDB wrappers, transactions here are (indirectly) the
/// things in control of accessing data behind cursors. This is in order to
/// correctly express memory semantics: Moving a cursor does not invalidate
/// memory obtained from the cursor; however, any mutation through the same
/// transaction does. We therefore model accesses to data in the environment as
/// borrows of the transaction and the database themselves (possibly mutable on
/// the latter), which allows the borrow checker to ensure that all references
/// are dropped before doing a structural modification.
///
/// Note that due to limitations in the Rust borrow checker, one actually needs
/// to use the `*Accessor` structs to access data. Any transaction will yield
/// at most one accessor, which is implemented with a runtime check that should
/// in the vast majority of cases get optimised out.
///
/// Mutability of a transaction reference does not indicate mutability of the
/// underlying database, but rather exclusivity for enforcement of child
/// transaction semantics.
///
/// ## Ownership
///
/// Transactions support all three ownership modes (but owned mode is not
/// useful). See `ReadTransaction` and `WriteTransaction` for details.
///
/// ## Lifetime
///
/// A `ConstTransaction` must be strictly outlived by its `Environment`.
///
/// `'env` is covariant: given two lifetimes `'x` and `'y` where `'x: 'y`, a
/// `&ConstTransaction<'x>` will implicitly coerce to `&ConstTransaction<'y>`.
///
/// ```rust,norun
/// # #![allow(dead_code)]
/// # extern crate lmdb_zero as lmdb;
/// # fn main() { }
/// #
/// fn convariance<'x, 'y>(db: &lmdb::ConstTransaction<'x>)
/// where 'x: 'y {
///   let _db2: &lmdb::ConstTransaction<'y> = db;
/// }
/// ```
///
/// Because of this property, if you need to hold onto an
/// `&lmdb::ConstTransaction` and must explicitly name both lifetimes,
/// it is usually best to use the same lifetime for both the reference and the
/// parameter, eg `&'x lmdb::ConstTransaction<'x>`.
#[derive(Debug)]
pub struct ConstTransaction<'env> {
    env: NonSyncSupercow<'env, Environment>,
    tx: TxHandle,
    has_yielded_accessor: Cell<bool>,
}

/// A read-only LMDB transaction.
///
/// In addition to all operations valid on `ConstTransaction`, a
/// `ReadTransaction` can additionally operate on cursors with a lifetime
/// scoped to the environment instead of the transaction.
///
/// ## Ownership
///
/// `ReadTransaction`s can be created with all three ownership modes (but owned
/// mode is not useful).
///
/// ### Example — Shared mode
///
/// ```
/// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
/// use std::sync::Arc;
///
/// # fn main() {
/// let env = Arc::new(create_env());
/// let db = Arc::new(lmdb::Database::open(
///   env.clone(), None, &lmdb::DatabaseOptions::defaults()).unwrap());
///
/// // Type and lifetime annotated explicitly for clarity
/// let txn: lmdb::ReadTransaction<'static> = lmdb::ReadTransaction::new(
///   env.clone()).unwrap();
///
/// // Do stuff with `txn`...
/// # drop(txn); drop(db);
/// # }
/// ```
///
/// ## Lifetime
///
/// All notes for `ConstTransaction` apply.
#[derive(Debug)]
// This MUST be a newtype struct and MUST NOT `impl Drop`
pub struct ReadTransaction<'env>(ConstTransaction<'env>);
/// A read-write LMDB transaction.
///
/// In addition to all operations valid on `ConstTransaction`, it is also
/// possible to perform writes to the underlying databases.
///
///
/// ## Ownership
///
/// `WriteTransaction`s can be created with all three ownership modes (but
/// owned mode is not useful).
///
/// ### Example — Shared mode
///
/// ```
/// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
/// use std::sync::Arc;
///
/// # fn main() {
/// let env = Arc::new(create_env());
/// let db = Arc::new(lmdb::Database::open(
///   env.clone(), None, &lmdb::DatabaseOptions::defaults()).unwrap());
///
/// // Type and lifetime annotated explicitly for clarity
/// let txn: lmdb::WriteTransaction<'static> = lmdb::WriteTransaction::new(
///   env.clone()).unwrap();
///
/// // Do stuff with `txn`...
///
/// txn.commit().unwrap();
/// # }
/// ```
///
/// ## Lifetime
///
/// All notes for `ConstTransaction` apply.
#[derive(Debug)]
// This MUST be a newtype struct and MUST NOT `impl Drop`
pub struct WriteTransaction<'env>(ConstTransaction<'env>);

/// A read-only LMDB transaction that has been reset.
///
/// It can be renewed by calling `ResetTransaction::renew()`.
///
/// ## Lifetime
///
/// All notes for `ReadTransaction` apply.
#[derive(Debug)]
pub struct ResetTransaction<'env>(ReadTransaction<'env>);

/// A read-only data accessor obtained from a `ConstTransaction`.
///
/// There is no corresponding `ReadAccessor`, since there are no additional
/// operations one can do with a known-read-only accessor.
///
/// ## Lifetime
///
/// A `ConstAccessor` must be strictly outlived by its parent transaction. The
/// parent transaction cannot be destroyed (committed, etc) until the borrow
/// from the accessor ends. This in many cases requires adding an extra scope
/// (with bare `{ }` braces) in which to obtain the accessor, as can be seen in
/// many of the examples.
///
/// The lifitem of a reference to a `ConstAccessor` dictates the lifetime of
/// the data accessed via the accessor.
///
/// The `'txn` lifetime parameter is covariant. That is, given two lifetimes
/// `'x` and `'y` where `'x: 'y`, a `&ConstAccessor<'x>` can be implicitly
/// coerced into a `&ConstAccessor<'y>`.
///
/// ```rust,norun
/// # #![allow(dead_code)]
/// # extern crate lmdb_zero as lmdb;
/// # fn main() { }
/// #
/// fn convariance<'x, 'y>(db: &lmdb::ConstAccessor<'x>)
/// where 'x: 'y {
///   let _db2: &lmdb::ConstAccessor<'y> = db;
/// }
/// ```
///
/// Because of this property, if you need to hold onto an
/// `&lmdb::ConstAccessor` and must explicitly name both lifetimes, it
/// is usually best to use the same lifetime for both the reference and the
/// parameter, eg `&'x lmdb::ConstAccessor<'x>`.
#[derive(Debug)]
pub struct ConstAccessor<'txn>(&'txn ConstTransaction<'txn>);

/// ConstAccessor implements Drop trait so that if it gets
/// dropped, a new accessor can be safely obtained
impl<'txn> Drop for ConstAccessor<'txn> {
    fn drop(&mut self) {
        self.0.has_yielded_accessor.set(false)
    }
}

/// A read-write data accessor obtained from a `WriteTransaction`.
///
/// All operations that can be performed on `ConstAccessor` can also be
/// performed on `WriteAccessor`.
///
/// ## Lifetime
///
/// Nominally, `WriteAccessor` would behave the same as `ConstAccessor`.
///
/// However, there is never any useful reason to explicitly reference a
/// `&WriteAccessor` (ie, a shared reference). Instead, one talks about a
/// `&mut WriteAccessor`. The unfortunate consequence here is that the `'txn`
/// lifetime ends up being _invariant_; that is, the following code will not
/// compile:
///
/// ```rust,ignore
/// # #![allow(dead_code)]
/// # extern crate lmdb_zero as lmdb;
/// # fn main() { }
/// #
/// fn convariance<'x, 'y>(db: &mut lmdb::WriteAccessor<'x>)
/// where 'x: 'y {
///   let _db2: &mut lmdb::WriteAccessor<'y> = db; // ERROR!
/// }
/// ```
///
/// The compiler's error messages here tend to be unhelpful. In certain cases,
/// it will suggest changing the function declaration above to something like
/// `&'x mut lmdb::WriteAccessor<'x>`. Applying such a fix when it is suggested
/// _will appear to work_. But what happens is that you end up propagating
/// `&'txn mut lmdb::WriteAccessor<'txn>` the whole way up your call stack.
/// Since `'txn` is invariant, it is inferred to be exactly equal to the
/// lifetime of the transaction, and now you've declared that the borrow from
/// the transaction exists for the entire lifetime of the transaction. This
/// means that you cannot actually commit the transaction.
///
/// Instead, make sure you always have separate type parameters on the `&mut`
/// and the `WriteAccessor` itself. This can usually be accomplished by letting
/// lifetime elision run its course. If you must name both, generally go with
/// `&'access mut WriteAccessor<'txn>`. The `'access` lifetime is the lifetime
/// of any data you obtain via the accessor.
#[derive(Debug)]
pub struct WriteAccessor<'txn>(ConstAccessor<'txn>);

impl<'env> ConstTransaction<'env> {
    fn new<'outer: 'env, E>(env: E,
                            parent: Option<&'env mut ConstTransaction<'outer>>,
                            flags: c_uint) -> Result<Self>
    where E : Into<NonSyncSupercow<'env, Environment>> {
        let env : NonSyncSupercow<'env, Environment> = env.into();

        let mut rawtx: *mut ffi::MDB_txn = ptr::null_mut();
        unsafe {
            lmdb_call!(ffi::mdb_txn_begin(
                env::env_ptr(&env), parent.map_or(ptr::null_mut(), |p| p.tx.0),
                flags, &mut rawtx));
        }

        Ok(ConstTransaction {
            env: env,
            tx: TxHandle(rawtx),
            has_yielded_accessor: Cell::new(false),
        })
    }

    /// Returns an accessor used to manipulate data in this transaction.
    ///
    /// ## Ownership
    ///
    /// Unlike most other lmdb-zero APIs, accessors do not support shared
    /// ownership modes (e.g., where the accessor would hold on to a
    /// `Rc<ConstTransaction>`). If you need dynamically-managed lifetime,
    /// instead simply drop the accessor and get a new one the next time one is
    /// needed.
    ///
    /// ## Panics
    ///
    /// Panics if this function has already been called on this transaction and
    /// the returned value has not yet been dropped.
    ///
    /// ## Example
    ///
    /// ```rust,should_panic
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # #[allow(unused_vars)]
    /// # fn main() {
    /// # let env = create_env();
    /// let txn = lmdb::ReadTransaction::new(&env).unwrap();
    /// // Get access the first time
    /// let access = txn.access();
    ///
    /// // You can't get the accessor again in the same scope, since this
    /// // would create two references to the same logical memory and allow
    /// // creating aliased mutable references and so forth.
    /// let access2 = txn.access(); // PANIC!
    /// # }
    /// ```
    #[inline]
    pub fn access(&self) -> ConstAccessor {
        assert!(!self.has_yielded_accessor.get(),
                "Transaction accessor already returned");
        self.has_yielded_accessor.set(true);
        ConstAccessor(self)
    }

    /// Creates a new cursor scoped to this transaction, bound to the given
    /// database.
    ///
    /// This method is functionally equivalent to the method on `CreateCursor`
    /// and exists for convenience and backwards-compatibility.
    ///
    /// If you have an, e.g., `Rc<ReadTransaction>` and want to get a
    /// `Cursor<'static,'db>`, make sure you have the `CreateCursor` trait
    /// imported so that the needed alternate implementations of this method
    /// are available.
    #[inline]
    pub fn cursor<'txn, 'db, DB>(&'txn self, db: DB)
                                 -> Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        Cursor::construct(Supercow::borrowed(self), db.into())
    }

    /// Returns the internal id of this transaction.
    pub fn id(&self) -> usize {
        unsafe {
            ffi2::mdb_txn_id(self.tx.0)
        }
    }

    /// Retrieves statistics for a database.
    pub fn db_stat(&self, db: &Database) -> Result<Stat> {
        try!(db.assert_same_env(&self.env));

        unsafe {
            let mut raw: ffi::MDB_stat = mem::zeroed();
            lmdb_call!(ffi::mdb_stat(self.tx.0, db.as_raw(), &mut raw));
            Ok(raw.into())
        }
    }

    /// Retrieve the DB flags for a database handle.
    pub fn db_flags(&self, db: &Database) -> Result<db::Flags> {
        try!(db.assert_same_env(&self.env));

        let mut raw: c_uint = 0;
        unsafe {
            lmdb_call!(ffi::mdb_dbi_flags(self.tx.0, db.as_raw(), &mut raw));
        }
        Ok(db::Flags::from_bits_truncate(raw))
    }

    #[inline]
    fn assert_sensible_cursor(&self, cursor: &Cursor)
                              -> Result<()> {
        if self as *const ConstTransaction !=
            cursor::txn_ref(cursor) as *const ConstTransaction
        {
            Err(Error::Mismatch)
        } else {
            Ok(())
        }
    }
}

// Internally used by other parts of the crate
#[inline]
pub fn assert_sensible_cursor(access: &ConstAccessor, cursor: &Cursor)
                              -> Result<()> {
    access.0.assert_sensible_cursor(cursor)
}
#[inline]
pub fn assert_same_env(txn: &ConstTransaction, db: &Database)
                       -> Result<()> {
    db.assert_same_env(&txn.env)
}
#[inline]
pub fn assert_in_env(txn: &ConstTransaction, env: &Environment)
                     -> Result<()> {
    if env as *const Environment != &*txn.env as *const Environment {
        Err(Error::Mismatch)
    } else {
        Ok(())
    }
}
#[inline]
pub fn txptr(txn: &ConstTransaction) -> *mut ffi::MDB_txn {
    txn.tx.0
}

impl<'env> Deref for ReadTransaction<'env> {
    type Target = ConstTransaction<'env>;

    fn deref(&self) -> &ConstTransaction<'env> {
        &self.0
    }
}

impl<'env> DerefMut for ReadTransaction<'env> {
    fn deref_mut(&mut self) -> &mut ConstTransaction<'env> {
        &mut self.0
    }
}

impl<'env> ReadTransaction<'env> {
    /// Opens a new, read-only transaction within the given environment.
    ///
    /// ## Note
    ///
    /// A transaction and its cursors must only be used by a single thread
    /// (enforced by the rust compiler), and a thread may only have a single
    /// transaction at a time. If `NOTLS` is in use, this does not apply to
    /// read-only transactions. Attempting to open a read-only transaction
    /// while the current thread holds a read-write transaction will deadlock.
    pub fn new<E>(env: E) -> Result<Self>
    where E : Into<NonSyncSupercow<'env, Environment>> {
        Ok(ReadTransaction(try!(ConstTransaction::new(
            env, None, ffi::MDB_RDONLY))))
    }

    /// Dissociates the given cursor from this transaction and its database,
    /// returning a `StaleCursor` which can be reused later.
    ///
    /// This only fails if `cursor` does not belong to this transaction.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = lmdb::Database::open(
    /// #   &env, None, &lmdb::DatabaseOptions::defaults())
    /// #   .unwrap();
    /// let mut saved_cursor;
    /// {
    ///   let txn = lmdb::ReadTransaction::new(&env).unwrap();
    ///   let cursor = txn.cursor(&db).unwrap();
    ///   // Do some stuff with `txn` and `cursor`
    ///
    ///   // We don't want to realloc `cursor` next time, so save it away
    ///   saved_cursor = txn.dissoc_cursor(cursor).unwrap();
    /// } // Read transaction goes away, but our saved cursor remains
    ///
    /// {
    ///   let txn = lmdb::ReadTransaction::new(&env).unwrap();
    ///   // Rebind the old cursor. It continues operating on `db`.
    ///   let cursor = txn.assoc_cursor(saved_cursor).unwrap();
    ///   // Do stuff with txn, cursor
    ///
    ///   // We can save the cursor away again
    ///   saved_cursor = txn.dissoc_cursor(cursor).unwrap();
    /// }
    /// # }
    /// ```
    ///
    /// ## Example — Shared ownership mode
    ///
    /// Cursors can also be dissociated and reassociated with transactions with
    /// shared ownership mode. This can also include changing the ownership
    /// mode. To be able to use shared ownership mode, make sure that the
    /// `AssocCursor` trait is imported or else you will simply borrow the
    /// inner transaction instead of taking a copy of the `Rc`, etc.
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// use std::sync::Arc;
    ///
    /// use lmdb::traits::{AssocCursor, CreateCursor};
    ///
    /// # fn main() {
    /// // N.B. Unnecessary type and lifetime annotations included for clarity
    /// let env: Arc<lmdb::Environment> = Arc::new(create_env());
    /// let db: Arc<lmdb::Database<'static>> = Arc::new(lmdb::Database::open(
    ///   env.clone(), None, &lmdb::DatabaseOptions::defaults()).unwrap());
    ///
    /// let mut saved_cursor: lmdb::StaleCursor<'static>;
    /// {
    ///   // `Arc` is unnecessary in this trivial example, but let's pretend
    ///   // there was good use for this.
    ///   let txn: Arc<lmdb::ReadTransaction> = Arc::new(
    ///     lmdb::ReadTransaction::new(env.clone()).unwrap());
    ///   let cursor: lmdb::Cursor<'static, 'static> =
    ///     txn.cursor(db.clone()).unwrap();
    ///
    ///   // Do some stuff with `txn` and `cursor`
    ///
    ///   // We don't want to realloc `cursor` next time, so save it away
    ///   saved_cursor = txn.dissoc_cursor(cursor).unwrap();
    /// }
    ///
    /// {
    ///   let txn: Arc<lmdb::ReadTransaction<'static>> =
    ///     Arc::new(lmdb::ReadTransaction::new(env.clone()).unwrap());
    ///   // Rebind the old cursor. It continues operating on `db`.
    ///   let cursor: lmdb::Cursor<'static, 'static> =
    ///     txn.assoc_cursor(saved_cursor).unwrap();
    ///   // Do stuff with txn, cursor
    ///
    ///   // We can save the cursor away again
    ///   saved_cursor = txn.dissoc_cursor(cursor).unwrap();
    /// }
    /// # }
    /// ```
    pub fn dissoc_cursor<'txn,'db>(&self, cursor: Cursor<'txn,'db>)
                                   -> Result<StaleCursor<'db>>
    where 'env: 'db {
        try!(self.assert_sensible_cursor(&cursor));
        let env = Supercow::clone_non_owned(&self.env)
            .expect("Cannot use owned `Environment` with `dissoc_cursor`");
        Ok(cursor::to_stale(cursor, env))
    }

    /// Associates a saved read-only with this transaction.
    ///
    /// The cursor will be rebound to this transaction, but will continue using
    /// the same database that it was previously.
    ///
    /// This method is functionally equivalent to the method on `AssocCursor`
    /// and exists for convenience and backwards-compatibility.
    ///
    /// If you have an, e.g., `Rc<ReadTransaction>` and want to get a
    /// `Cursor<'static,'db>`, make sure you have the `AssocCursor` trait
    /// imported so that the needed alternate implementations of this method
    /// are available.
    pub fn assoc_cursor<'txn,'db>(&'txn self, cursor: StaleCursor<'db>)
                                  -> Result<Cursor<'txn,'db>> {
        let self_as_const: &'txn ConstTransaction = &*self;
        Cursor::from_stale(cursor,
                           NonSyncSupercow::borrowed(&*self_as_const))
    }

    /// Resets this transaction, releasing most of its resources but allowing
    /// it to be quickly renewed if desired.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// let mut saved_txn;
    /// {
    ///   let txn = lmdb::ReadTransaction::new(&env).unwrap();
    ///   {
    ///     let access = txn.access();
    ///     // Do stuff with `txn`, `access`
    ///   }
    ///   // Save our transaction so we don't have to reallocate it next time,
    ///   // but we also don't keep locks around and will later move to the
    ///   // latest version of the environment.
    ///   saved_txn = txn.reset();
    /// }
    ///
    /// {
    ///   // Instead of creating a brand new transaction, renew the one we
    ///   // saved.
    ///   let txn = saved_txn.renew().unwrap();
    ///   {
    ///     let access = txn.access();
    ///     // Do stuff with `txn`, `access`
    ///   }
    ///
    ///   // We can save the transaction away again
    ///   saved_txn = txn.reset();
    /// }
    /// # }
    /// ```
    pub fn reset(self) -> ResetTransaction<'env> {
        unsafe { ffi::mdb_txn_reset(self.0.tx.0); }
        ResetTransaction(self)
    }
}

impl<'env> ResetTransaction<'env> {
    /// Renews this read-only transaction, making it available for more
    /// reading.
    pub fn renew(self) -> Result<ReadTransaction<'env>> {
        unsafe { lmdb_call!(ffi::mdb_txn_renew((self.0).0.tx.0)); }
        Ok(self.0)
    }
}

impl<'env> Deref for WriteTransaction<'env> {
    type Target = ConstTransaction<'env>;


    fn deref(&self) -> &ConstTransaction<'env> {
        &self.0
    }
}

impl<'env> DerefMut for WriteTransaction<'env> {
    fn deref_mut(&mut self) -> &mut ConstTransaction<'env> {
        &mut self.0
    }
}

impl<'env> WriteTransaction<'env> {
    /// Creates a new, read-write transaction in the given environment.
    ///
    /// ## Note
    ///
    /// A transaction and its cursors must only be used by a single thread
    /// (enforced by the rust compiler), and a thread may only have a single
    /// read-write transaction at a time (even if `NOTLS` is in use --- trying
    /// to start two top-level read-write transactions on the same thread will
    /// deadlock).
    pub fn new<E>(env: E) -> Result<Self>
    where E : Into<NonSyncSupercow<'env, Environment>> {
        Ok(WriteTransaction(try!(ConstTransaction::new(env, None, 0))))
    }

    /// Opens a new, read-write transaction as a child transaction of the given
    /// parent. While the new transaction exists, no operations may be
    /// performed on the parent or any of its cursors. (These bindings are
    /// actually stricter, and do not permit cursors or other references into
    /// the parent to coexist with the child transaction.)
    ///
    /// After this call, whether or not it succeeds, it is possible to call
    /// `access()` on the original transaction again one more time, since the
    /// Rust borrow rules guarantee the old accessor was destroyed by the
    /// caller already.
    ///
    /// ## Note
    ///
    /// A transaction and its cursors must only be used by a single thread
    /// (enforced by the rust compiler).
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// let db = lmdb::Database::open(
    ///   &env, None, &lmdb::DatabaseOptions::defaults()).unwrap();
    /// let mut txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// let f = lmdb::put::Flags::empty();
    /// {
    ///   let mut access = txn.access();
    ///   access.put(&db, "Germany", "Berlin", f).unwrap();
    ///   access.put(&db, "Latvia", "Rīga", f).unwrap();
    ///   access.put(&db, "France", "Paris", f).unwrap();
    /// }
    ///
    /// {
    ///   // Open a child transaction and do some more reading and writing.
    ///   let subtx = txn.child_tx().unwrap();
    ///   let mut access = subtx.access();
    ///   assert_eq!("Berlin", access.get::<str,str>(&db, "Germany").unwrap());
    ///   access.put(&db, "Germany", "Frankfurt", f).unwrap();
    ///   assert_eq!("Frankfurt", access.get::<str,str>(&db, "Germany").unwrap());
    ///   // Don't commit --- let the child transaction abort (roll back)
    /// }
    ///
    /// {
    ///   let mut access = txn.access();
    ///   // Now we can do some more reading and writing on the original
    ///   // transaction.
    ///   // The effect of the aborted child transaction are not visible.
    ///   access.put(&db, "United Kingdom", "London", f).unwrap();
    ///   assert_eq!("Berlin", access.get::<str,str>(&db, "Germany").unwrap());
    /// }
    ///
    /// {
    ///   // Another child.
    ///   let subtx = txn.child_tx().unwrap();
    ///   {
    ///     let mut access = subtx.access();
    ///     access.put(&db, "Spain", "Madrid", f).unwrap();
    ///   }
    ///   // Commit this one this time.
    ///   subtx.commit().unwrap();
    /// }
    ///
    /// {
    ///   // Now the changes from the child are visible to this transaction,
    ///   // but still not outside it.
    ///   let mut access = txn.access();
    ///   assert_eq!("Madrid", access.get::<str,str>(&db, "Spain").unwrap());
    /// }
    ///
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn child_tx<'a>(&'a mut self) -> Result<WriteTransaction<'a>>
    where 'env: 'a {
        let env = Supercow::share(&mut self.0.env);
        Ok(WriteTransaction(try!(ConstTransaction::new(
            env, Some(&mut*self), 0))))
    }

    /// Commits this write transaction.
    pub fn commit(mut self) -> Result<()> {
        unsafe {
            self.0.tx.commit()
        }
    }

    /// Returns a read/write accessor on this transaction.
    ///
    /// ## Panics
    ///
    /// Panics if an accessor has already been obtained from this transaction
    /// and not yet dropped.
    #[inline]
    pub fn access(&self) -> WriteAccessor {
        WriteAccessor(self.0.access())
    }
}

impl<'txn> ConstAccessor<'txn> {
    /// Get items from a database.
    ///
    /// This function retrieves key/data pairs from the database. A reference
    /// to the data associated with the given key is returned. If the database
    /// supports duplicate keys (`DUPSORT`) then the first data item for the
    /// key will be returned. Retrieval of other items requires the use of
    /// cursoring.
    ///
    /// The returned memory is valid until the next mutation through the
    /// transaction or the end of the transaction (both are enforced through
    /// the borrow checker).
    ///
    /// ## Errors
    ///
    /// This call may return errors for reasons other than the key not being
    /// found. The easiest way to handle "not found" is generally to use the
    /// `to_opt` method on `traits::LmdbResultExt` to promote the value into a
    /// `Result<Option<V>>`. Most important of these other errors is the
    /// possibility of the key being found, but the value not being convertible
    /// to a `&V`.
    #[inline]
    pub fn get<K : AsLmdbBytes + ?Sized, V : FromLmdbBytes + ?Sized>(
        &self, db: &Database, key: &K) -> Result<&V>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        unsafe {
            lmdb_call!(ffi::mdb_get(
                self.txptr(), db.as_raw(), &mut mv_key, &mut out_val));
        }

        from_val(self, &out_val)
    }

    fn txptr(&self) -> *mut ffi::MDB_txn {
        self.0.tx.0
    }

    fn env(&self) -> &Environment {
        &*self.0.env
    }
}

impl<'txn> Deref for WriteAccessor<'txn> {
    type Target = ConstAccessor<'txn>;

    fn deref(&self) -> &ConstAccessor<'txn> {
        &self.0
    }
}

impl<'txn> WriteAccessor<'txn> {
    /// Store items into a database.
    ///
    /// This function stores key/data pairs in the database. The default
    /// behavior is to enter the new key/data pair, replacing any previously
    /// existing key if duplicates are disallowed, or adding a duplicate data
    /// item if duplicates are allowed (`DUPSORT`).
    #[inline]
    pub fn put<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K, value: &V,
        flags: put::Flags) -> Result<()>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut mv_val = as_val(value);
        unsafe {
            lmdb_call!(ffi::mdb_put(
                self.txptr(), db.as_raw(), &mut mv_key, &mut mv_val,
                flags.bits()));
        }
        Ok(())
    }

    /// Store items into a database.
    ///
    /// This function stores key/data pairs in the database. The default
    /// behavior is to enter the new key/data pair, replacing any previously
    /// existing key if duplicates are disallowed, or adding a duplicate data
    /// item if duplicates are allowed (`DUPSORT`).
    ///
    /// Unlike `put()`, this does not take a value. Instead, it reserves space
    /// for the value (equal to the size of `V`) and then returns a mutable
    /// reference to it. Be aware that the `FromReservedLmdbBytes` conversion
    /// will be invoked on whatever memory happens to be at the destination
    /// location.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// #[repr(C, packed)]
    /// #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    /// struct MyStruct {
    ///   x: i32,
    ///   y: i32,
    /// }
    /// unsafe impl lmdb::traits::LmdbRaw for MyStruct { }
    ///
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = lmdb::Database::open(
    /// #   &env, None, &lmdb::DatabaseOptions::defaults())
    /// #   .unwrap();
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   {
    ///     let dst: &mut MyStruct = access.put_reserve(
    ///       &db, "foo", lmdb::put::Flags::empty()).unwrap();
    ///     // Writing to `dst` actually writes directly into the database.
    ///     dst.x = 42;
    ///     dst.y = 56;
    ///     // Drop `dst` so we can use `access` again
    ///   }
    ///   assert_eq!(&MyStruct { x: 42, y: 56 },
    ///              access.get(&db, "foo").unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    #[inline]
    pub fn put_reserve<K : AsLmdbBytes + ?Sized,
                       V : FromReservedLmdbBytes + Sized>(
        &mut self, db: &Database, key: &K, flags: put::Flags) -> Result<&mut V>
    {
        unsafe {
            self.put_reserve_unsized(db, key, mem::size_of::<V>(), flags)
        }
    }

    /// Store items into a database.
    ///
    /// This function stores key/data pairs in the database. The default
    /// behavior is to enter the new key/data pair, replacing any previously
    /// existing key if duplicates are disallowed, or adding a duplicate data
    /// item if duplicates are allowed (`DUPSORT`).
    ///
    /// Unlike `put()`, this does not take a value. Instead, it reserves space
    /// for the value (equal to an array of `count` objects of size `V`) and
    /// then returns a mutable reference to it. Be aware that the content of
    /// the returned slice is simply whatever happens to be in the destination
    /// memory at the time of this call.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = lmdb::Database::open(
    /// #   &env, None, &lmdb::DatabaseOptions::defaults())
    /// #   .unwrap();
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   {
    ///     let bytes: &mut [u8] = access.put_reserve_array(
    ///       &db, "foo", 4, lmdb::put::Flags::empty()).unwrap();
    ///     // More realistically, one could zero-copy data from a file/socket
    ///     // into `bytes`, for example.
    ///     bytes[0] = b'b'; bytes[1] = b'y';
    ///     bytes[2] = b't'; bytes[3] = b'e';
    ///   }
    ///   assert_eq!("byte", access.get::<str,str>(&db, "foo").unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    #[inline]
    pub fn put_reserve_array<K : AsLmdbBytes + ?Sized, V : LmdbRaw>(
        &mut self, db: &Database, key: &K, count: usize, flags: put::Flags)
        -> Result<&mut [V]>
    {
        unsafe {
            self.put_reserve_unsized(
                db, key, mem::size_of::<V>() * count, flags)
        }
    }

    /// Store items into a database.
    ///
    /// This function stores key/data pairs in the database. The default
    /// behavior is to enter the new key/data pair, replacing any previously
    /// existing key if duplicates are disallowed, or adding a duplicate data
    /// item if duplicates are allowed (`DUPSORT`).
    ///
    /// Unlike `put()`, this does not take a value. Instead, it reserves space
    /// equal to `size` bytes for the value and then returns a mutable
    /// reference to it. Be aware that the `FromReservedLmdbBytes` conversion
    /// will be invoked on whatever memory happens to be at the destination
    /// location.
    ///
    /// ## Unsafety
    ///
    /// The caller must ensure that `size` is a valid size for `V`.
    #[inline]
    pub unsafe fn put_reserve_unsized<K : AsLmdbBytes + ?Sized,
                                      V : FromReservedLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K, size: usize, flags: put::Flags)
        -> Result<&mut V>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        out_val.mv_size = size;
        lmdb_call!(ffi::mdb_put(
            self.txptr(), db.as_raw(), &mut mv_key, &mut out_val,
            flags.bits() | ffi::MDB_RESERVE));

        Ok(from_reserved(self, &out_val))
    }

    /// Delete items from a database by key.
    ///
    /// This function removes key/data pairs from the database. All values
    /// whose key matches `key` are deleted, including in the case of
    /// `DUPSORT`. This function will return `NOTFOUND` if the specified
    /// key is not in the database.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// let db = lmdb::Database::open(
    ///   &env, Some("example"),
    ///   &lmdb::DatabaseOptions::create_multimap_unsized::<str,str>())
    ///   .unwrap();
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
    ///   access.put(&db, "Fruit", "Orange", lmdb::put::Flags::empty()).unwrap();
    ///   assert_eq!("Apple", access.get::<str,str>(&db, "Fruit").unwrap());
    ///   access.del_key(&db, "Fruit").unwrap();
    ///   assert!(access.get::<str,str>(&db, "Fruit").is_err());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    #[inline]
    pub fn del_key<K : AsLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K) -> Result<()>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        unsafe {
            lmdb_call!(ffi::mdb_del(
                self.txptr(), db.as_raw(), &mut mv_key, ptr::null_mut()));
        }

        Ok(())
    }

    /// Delete items from a database by key and value.
    ///
    /// This function removes key/data pairs from the database. If the database
    /// does not support sorted duplicate data items (`DUPSORT`) the `val`
    /// parameter is ignored and this call behaves like `del()`. Otherwise, if
    /// the data item matching both `key` and `val` will be deleted. This
    /// function will return `NOTFOUND` if the specified key/data pair is not
    /// in the database.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// let db = lmdb::Database::open(
    ///   &env, Some("example"),
    ///   &lmdb::DatabaseOptions::create_multimap_unsized::<str,str>())
    ///   .unwrap();
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   access.put(&db, "Fruit", "Apple", lmdb::put::Flags::empty()).unwrap();
    ///   access.put(&db, "Fruit", "Orange", lmdb::put::Flags::empty()).unwrap();
    ///   assert_eq!("Apple", access.get::<str,str>(&db, "Fruit").unwrap());
    ///   access.del_item(&db, "Fruit", "Apple").unwrap();
    ///   assert_eq!("Orange", access.get::<str,str>(&db, "Fruit").unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    #[inline]
    pub fn del_item<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K, val: &V) -> Result<()>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut mv_val = as_val(val);
        unsafe {
            lmdb_call!(ffi::mdb_del(
                self.txptr(), db.as_raw(), &mut mv_key, &mut mv_val));
        }

        Ok(())
    }

    /// Completely clears the content of the given database.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = lmdb::Database::open(
    /// #   &env, None, &lmdb::DatabaseOptions::defaults())
    /// #   .unwrap();
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, "Germany", "Berlin", f).unwrap();
    ///   access.put(&db, "France", "Paris", f).unwrap();
    ///   access.put(&db, "Latvia", "Rīga", f).unwrap();
    ///   assert_eq!(3, txn.db_stat(&db).unwrap().entries);
    ///
    ///   access.clear_db(&db).unwrap();
    ///   assert_eq!(0, txn.db_stat(&db).unwrap().entries);
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn clear_db(&mut self, db: &Database) -> Result<()> {
        try!(db.assert_same_env(self.env()));
        unsafe {
            lmdb_call!(ffi::mdb_drop(self.txptr(), db.as_raw(), 0));
        }
        Ok(())
    }
}
