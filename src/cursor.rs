// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::marker::PhantomData;
use std::mem;
use std::ptr;
use libc::{self, c_uint, c_void};

use ffi;

use env::Environment;
use error::Result;
use mdb_vals::*;
use traits::*;
use tx::{put, del, ConstAccessor, ConstTransaction, WriteAccessor};
use tx::assert_sensible_cursor;

#[derive(Debug)]
struct CursorHandle(*mut ffi::MDB_cursor);
impl Drop for CursorHandle {
    fn drop(&mut self) {
        unsafe {
            ffi::mdb_cursor_close(self.0);
        }
    }
}

/// A cursor into an LMDB database.
///
/// Depending on the context, a cursor's lifetime may be scoped to a
/// transaction or to the whole environment. Its lifetime is also naturally
/// bound to the lifetime of the database it cursors into.
///
///
#[derive(Debug)]
pub struct Cursor<'txn,'db> {
    cursor: CursorHandle,
    txn: &'txn ConstTransaction<'txn>,
    _db: PhantomData<&'db ()>,
}

// Used by transactions to construct/query cursors
pub unsafe fn create_cursor<'txn, 'db>(raw: *mut ffi::MDB_cursor,
                                       txn: &'txn ConstTransaction<'txn>)
                                       -> Cursor<'txn, 'db> {
    Cursor {
        cursor: CursorHandle(raw),
        txn: txn,
        _db: PhantomData,
    }
}
pub fn txn_ref<'txn,'db>(cursor: &Cursor<'txn,'db>)
                         -> &'txn ConstTransaction<'txn> {
    cursor.txn
}

/// A read-only cursor which has been dissociated from its original
/// transaction, so that it can be rebound later.
///
/// A `StaleCursor` remains bound to the original database.
#[derive(Debug)]
pub struct StaleCursor<'db> {
    cursor: CursorHandle,
    env: &'db Environment,
    _db: PhantomData<&'db ()>,
}

// Internal
pub fn to_stale<'a,'db>(cursor: Cursor<'a,'db>, env: &'db Environment)
                        -> StaleCursor<'db> {
    StaleCursor {
        cursor: cursor.cursor,
        env: env,
        _db: PhantomData,
    }
}
pub fn from_stale<'txn,'db>(stale: StaleCursor<'db>,
                            txn: &'txn ConstTransaction<'txn>)
                            -> Cursor<'txn,'db> {
    Cursor {
        cursor: stale.cursor,
        txn: txn,
        _db: PhantomData,
    }
}
pub fn env_ref<'a,'db>(cursor: &'a StaleCursor<'db>)
                       -> &'a Environment {
    cursor.env
}
pub fn stale_cursor_ptr<'db>(cursor: &StaleCursor<'db>)
                             -> *mut ffi::MDB_cursor {
    cursor.cursor.0
}

macro_rules! cursor_get_0_kv {
    ($(#[$doc:meta])* fn $method:ident, $op:path) => {
        $(#[$doc])*
        pub fn $method<'access, K : FromLmdbBytes + ?Sized,
                       V : FromLmdbBytes + ?Sized>
            (&mut self, access: &'access ConstAccessor)
             -> Result<(&'access K, &'access V)>
        {
            self.get_0_kv(access, $op)
        }
    }
}

macro_rules! cursor_get_0_v {
    ($(#[$doc:meta])* fn $method:ident, $op:path) => {
        $(#[$doc])*
        pub fn $method<'access, V : FromLmdbBytes + ?Sized>
            (&mut self, access: &'access ConstAccessor)
             -> Result<(&'access V)>
        {
            self.get_0_v(access, $op)
        }
    }
}

impl<'txn,'db> Cursor<'txn,'db> {
    fn get_0_kv<'access, K : FromLmdbBytes + ?Sized,
                V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         op: c_uint) -> Result<(&'access K, &'access V)>
    {
        try!(assert_sensible_cursor(access, self));

        let mut out_key = EMPTY_VAL;
        let mut out_val = EMPTY_VAL;
        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut out_key, &mut out_val, op));
        }

        Ok((try!(from_val(access, &out_key)),
            try!(from_val(access, &out_val))))
    }

    fn get_0_v<'access, V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         op: c_uint) -> Result<&'access V>
    {
        try!(assert_sensible_cursor(access, self));

        let mut null_key = EMPTY_VAL;
        let mut out_val = EMPTY_VAL;
        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut null_key, &mut out_val, op));
        }

        from_val(access, &out_val)
    }

    fn get_kv_0<K: AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, key: &K, val: &V, op: c_uint) -> Result<()>
    {
        let mut mv_key = as_val(key);
        let mut mv_val = as_val(val);
        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut mv_key, &mut mv_val, op));
        }

        Ok(())
    }

    fn get_kv_v<'access, K : AsLmdbBytes + ?Sized,
                V : AsLmdbBytes + FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         key: &K, val: &V, op: c_uint) -> Result<&'access V>
    {
        try!(assert_sensible_cursor(access, self));

        let mut mv_key = as_val(key);
        let mut inout_val = as_val(val);

        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut mv_key, &mut inout_val, op));
        }

        from_val(access, &inout_val)
    }

    fn get_k_v<'access, K : AsLmdbBytes + ?Sized,
               V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         key: &K, op: c_uint) -> Result<&'access V>
    {
        try!(assert_sensible_cursor(access, self));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;

        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut mv_key, &mut out_val, op));
        }

        from_val(access, &out_val)
    }

    fn get_k_kv<'access, K : AsLmdbBytes + FromLmdbBytes + ?Sized,
                V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         key: &K, op: c_uint) -> Result<(&'access K, &'access V)>
    {
        try!(assert_sensible_cursor(access, self));

        let mut inout_key = as_val(key);
        let mut out_val = EMPTY_VAL;

        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut inout_key, &mut out_val, op));
        }

        Ok((try!(from_val(access, &inout_key)),
            try!(from_val(access, &out_val))))
    }

    cursor_get_0_kv! {
        /// Positions the cursor at the first key/value pair in the database
        /// and returns that pair.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_FIRST` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Germany", "Berlin", f).unwrap();
        ///   access.put(&db, "France", "Paris", f).unwrap();
        ///   access.put(&db, "Latvia", "Rīga", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("France", "Paris"), cursor.first(&access).unwrap());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn first, ffi::MDB_FIRST
    }

    cursor_get_0_v! {
        /// Positions the cursor at the first key/value pair whose key is equal
        /// to the current key, returning the value of that pair.
        ///
        /// This only makes sense on `DUPSORT` databases.
        ///
        /// This correspnods to the `mdb_cursor_get` function with the
        /// `MDB_FIRST_DUP` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Fruit", "Durian", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("Fruit", "Orange"), cursor.last(&access).unwrap());
        ///   assert_eq!("Apple", cursor.first_dup::<str>(&access).unwrap());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn first_dup, ffi::MDB_FIRST_DUP
    }

    /// Positions the cursor at the given (key,value) pair.
    ///
    /// This only makes sense on `DUPSORT` databases.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the
    /// `MDB_GET_BOTH` operation.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, "Fruit", "Apple", f).unwrap();
    ///   access.put(&db, "Fruit", "Orange", f).unwrap();
    ///   access.put(&db, "Fruit", "Durian", f).unwrap();
    ///   access.put(&db, "Animal", "Badger", f).unwrap();
    ///
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   cursor.seek_kv("Fruit", "Durian").unwrap();
    ///   assert_eq!(("Fruit", "Orange"), cursor.next(&access).unwrap());
    ///   assert!(cursor.seek_kv("Fruit", "Lychee").is_err());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn seek_kv<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, key: &K, val: &V) -> Result<()>
    {
        self.get_kv_0(key, val, ffi::MDB_GET_BOTH)
    }

    /// Positions the cursor at the given key and the "nearest" value to `val`,
    /// that is, the first (according to sorting) item whose key equals `key`
    /// and whose value is greater than or equal to `val`.
    ///
    /// The actual value found is returned.
    ///
    /// This only makes sense on `DUPSORT` databases.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the
    /// `MDB_GET_BOTH_RANGE` operation.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, "Animal", "Badger", f).unwrap();
    ///   access.put(&db, "Fruit", "Banana", f).unwrap();
    ///   access.put(&db, "Fruit", "Orange", f).unwrap();
    ///   access.put(&db, "Fruit", "Durian", f).unwrap();
    ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
    ///
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   assert_eq!("Durian", cursor.seek_k_nearest_v::<str,str>(
    ///     &access, "Fruit", "Durian").unwrap());
    ///   assert_eq!("Orange", cursor.seek_k_nearest_v::<str,str>(
    ///     &access, "Fruit", "Lychee").unwrap());
    ///   assert!(cursor.seek_k_nearest_v::<str,str>(
    ///     &access, "Fruit", "Watermelon").is_err());
    ///   assert_eq!("Banana", cursor.seek_k_nearest_v::<str,str>(
    ///     &access, "Fruit", "Apple").unwrap());
    ///   assert!(cursor.seek_k_nearest_v::<str,str>(
    ///     &access, "Plant", "Tree").is_err());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn seek_k_nearest_v<'access, K : AsLmdbBytes + ?Sized,
                            V : AsLmdbBytes + FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         key: &K, val: &V) -> Result<&'access V>
    {
        self.get_kv_v(access, key, val, ffi::MDB_GET_BOTH_RANGE)
    }

    cursor_get_0_kv! {
        /// Returns the current key/value pair under this cursor.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_CURRENT` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Germany", "Berlin", f).unwrap();
        ///   access.put(&db, "France", "Paris", f).unwrap();
        ///   access.put(&db, "Latvia", "Rīga", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   cursor.seek_k::<str,str>(&access, "Latvia").unwrap();
        ///   assert_eq!(("Latvia", "Rīga"), cursor.get_current(&access).unwrap());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn get_current, ffi::MDB_GET_CURRENT
    }

    cursor_get_0_v! {
        /// Returns as many items as possible with the current key from the
        /// current cursor position.
        ///
        /// The cursor is advanced so that `next_multiple()` returns the next
        /// group of items, if any. Note that this does _not_ return the actual
        /// key (which LMDB itself does not return, contrary to documentation).
        ///
        /// The easiest way to use this is for `V` to be a slice of `LmdbRaw`
        /// types.
        ///
        /// This only makes sense on `DUPSORT` databases with `DUPFIXED` set.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_GET_MULTIPLE` operation.
        ///
        /// See `lmdb_zero::db::DUPFIXED` for examples of usage.
        fn get_multiple, ffi::MDB_GET_MULTIPLE
    }

    cursor_get_0_v! {
        /// Continues fetching items from a cursor positioned by a call to
        /// `get_multiple()`.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_NEXT_MULTIPLE` operation.
        ///
        /// See `lmdb_zero::db::DUPFIXED` for examples of usage.
        fn next_multiple, ffi::MDB_NEXT_MULTIPLE
    }

    cursor_get_0_kv! {
        /// Positions the cursor at the last key/value pair in the database,
        /// and returns that pair.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_LAST` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Germany", "Berlin", f).unwrap();
        ///   access.put(&db, "France", "Paris", f).unwrap();
        ///   access.put(&db, "Latvia", "Rīga", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("Latvia", "Rīga"), cursor.last(&access).unwrap());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn last, ffi::MDB_LAST
    }

    cursor_get_0_v! {
        /// Positions the cursor at the last key/value pair whose key is equal
        /// to the current key.
        ///
        /// This only makes sense on `DUPSORT` databases.
        ///
        /// This correspnods to the `mdb_cursor_get` function with the
        /// `MDB_LAST_DUP` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Fruit", "Durian", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!("Apple", cursor.seek_k::<str,str>(&access, "Fruit").unwrap());
        ///   assert_eq!("Orange", cursor.last_dup::<str>(&access).unwrap());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn last_dup, ffi::MDB_LAST_DUP
    }

    cursor_get_0_kv! {
        /// Advances the cursor to the key/value pair following this one.
        ///
        /// If the current key has multiple values, this will remain on the
        /// same key unless it is already on the last value.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_NEXT` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("Animal", "Badger"), cursor.first(&access).unwrap());
        ///   assert_eq!(("Fruit", "Apple"), cursor.next(&access).unwrap());
        ///   assert_eq!(("Fruit", "Orange"), cursor.next(&access).unwrap());
        ///   assert_eq!(("Veggie", "Carrot"), cursor.next(&access).unwrap());
        ///   assert!(cursor.next::<str,str>(&access).is_err());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn next, ffi::MDB_NEXT
    }

    cursor_get_0_kv! {
        /// Advances the cursor to the next value in the current key.
        ///
        /// This only makes sense on `DUPSORT` databases. This call fails if
        /// there are no more values in the current key.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_NEXT_DUP` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!("Apple", cursor.seek_k::<str,str>(&access, "Fruit").unwrap());
        ///   assert_eq!(("Fruit", "Orange"), cursor.next_dup(&access).unwrap());
        ///   assert!(cursor.next_dup::<str,str>(&access).is_err());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn next_dup, ffi::MDB_NEXT_DUP
    }

    cursor_get_0_kv! {
        /// Advances the cursor to the first item of the key following the
        /// current key.
        ///
        /// This is permitted in all databases, but only behaves distinctly
        /// from `next()` in `DUPSORT` databases.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_NEXT_NODUP` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("Animal", "Badger"), cursor.first(&access).unwrap());
        ///   assert_eq!(("Fruit", "Apple"), cursor.next_nodup(&access).unwrap());
        ///   assert_eq!(("Veggie", "Carrot"), cursor.next_nodup(&access).unwrap());
        ///   assert!(cursor.next_nodup::<str,str>(&access).is_err());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn next_nodup, ffi::MDB_NEXT_NODUP
    }

    cursor_get_0_kv! {
        /// Retreats the cursor to the previous key/value pair.
        ///
        /// If the current key has multiple values, this will remain on the
        /// same key unless it is already on the first value.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_PREV` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("Veggie", "Carrot"), cursor.last(&access).unwrap());
        ///   assert_eq!(("Fruit", "Orange"), cursor.prev(&access).unwrap());
        ///   assert_eq!(("Fruit", "Apple"), cursor.prev(&access).unwrap());
        ///   assert_eq!(("Animal", "Badger"), cursor.prev(&access).unwrap());
        ///   assert!(cursor.prev::<str,str>(&access).is_err());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn prev, ffi::MDB_PREV
    }

    cursor_get_0_kv! {
        /// Retreats the cursor to the previous value in the current key.
        ///
        /// This only makes sense on `DUPSORT` databases. This call fails if
        /// there are no prior values in the current key.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_PREV_DUP` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!("Apple", cursor.seek_k::<str,str>(&access, "Fruit").unwrap());
        ///   assert_eq!(("Fruit", "Orange"), cursor.next_dup(&access).unwrap());
        ///   assert_eq!(("Fruit", "Apple"), cursor.prev_dup(&access).unwrap());
        ///   assert!(cursor.prev_dup::<str,str>(&access).is_err());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn prev_dup, ffi::MDB_PREV_DUP
    }

    cursor_get_0_kv! {
        /// Retreats the cursor to the final item of the previous key.
        ///
        /// This is permitted in all databases, but only behaves distinctly
        /// from `prev()` in `DUPSORT` databases.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_PREV_NODUP` operation.
        ///
        /// ## Example
        ///
        /// ```
        /// # include!("src/example_helpers.rs");
        /// # fn main() {
        /// # let env = create_env();
        /// # let db = dupdb(&env);
        /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
        /// {
        ///   let mut access = txn.access();
        ///   let f = lmdb::put::Flags::empty();
        ///   access.put(&db, "Fruit", "Apple", f).unwrap();
        ///   access.put(&db, "Fruit", "Orange", f).unwrap();
        ///   access.put(&db, "Animal", "Badger", f).unwrap();
        ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
        ///
        ///   let mut cursor = txn.cursor(&db).unwrap();
        ///   assert_eq!(("Veggie", "Carrot"), cursor.last(&access).unwrap());
        ///   assert_eq!(("Fruit", "Orange"), cursor.prev_nodup(&access).unwrap());
        ///   assert_eq!(("Animal", "Badger"), cursor.prev_nodup(&access).unwrap());
        ///   assert!(cursor.prev_nodup::<str,str>(&access).is_err());
        /// }
        /// txn.commit().unwrap();
        /// # }
        /// ```
        fn prev_nodup, ffi::MDB_PREV_NODUP
    }

    /// Positions the cursor at the first item of the given key.
    ///
    /// Returns the value of that item.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the `MDB_SET`
    /// operation.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, "Fruit", "Apple", f).unwrap();
    ///   access.put(&db, "Fruit", "Orange", f).unwrap();
    ///   access.put(&db, "Animal", "Badger", f).unwrap();
    ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
    ///
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   assert_eq!("Apple", cursor.seek_k::<str,str>(&access, "Fruit").unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn seek_k<'access, K : AsLmdbBytes + ?Sized,
                  V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor, key: &K)
        -> Result<&'access V>
    {
        self.get_k_v(access, key, ffi::MDB_SET)
    }

    /// Positions the cursor at the first item of the given key.
    ///
    /// Returns the key and value of that item.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the
    /// `MDB_SET_KEY` operation.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, "Fruit", "Apple", f).unwrap();
    ///   access.put(&db, "Fruit", "Orange", f).unwrap();
    ///   access.put(&db, "Animal", "Badger", f).unwrap();
    ///   access.put(&db, "Veggie", "Carrot", f).unwrap();
    ///
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   assert_eq!(("Fruit", "Apple"), cursor.seek_k_both(&access, "Fruit").unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn seek_k_both<'access, K : AsLmdbBytes + FromLmdbBytes + ?Sized,
                       V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor, key: &K)
         -> Result<(&'access K, &'access V)>
    {
        self.get_k_kv(access, key, ffi::MDB_SET_KEY)
    }

    /// Positions the cursor at the first item whose key is greater than or
    /// equal to `key`.
    ///
    /// Return the key and value of that item.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the
    /// `MDB_SET_RANGE` operation.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   access.put(&db, "Fruit", "Apple", f).unwrap();
    ///   access.put(&db, "Fruit", "Orange", f).unwrap();
    ///   access.put(&db, "Animal", "Badger", f).unwrap();
    ///
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   assert_eq!(("Fruit", "Apple"), cursor.seek_range_k(&access, "Fog").unwrap());
    ///   assert!(cursor.seek_range_k::<str,str>(&access, "Veggie").is_err());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn seek_range_k<'access, K : AsLmdbBytes + FromLmdbBytes + ?Sized,
                        V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor, key: &K)
         -> Result<(&'access K, &'access V)>
    {
        self.get_k_kv(access, key, ffi::MDB_SET_RANGE)
    }

    /// Writes a single value through this cursor.
    ///
    /// By default, any item with the same key (if not `DUPSORT`) or any
    /// exactly matching item (if `DUPSORT`) is replaced silently. `flags` can
    /// be used to override this.
    ///
    /// This does not inherently overwrite the current item. See `overwrite()`
    /// for that.
    ///
    /// The cursor is positioned at the new item, or on failure usually near
    /// it.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   cursor.put(&mut access, "Germany", "Berlin", f).unwrap();
    ///   assert_eq!(("Germany", "Berlin"), cursor.get_current(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn put<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, access: &mut WriteAccessor,
         key: &K, val: &V, flags: put::Flags) -> Result<()>
    {
        try!(assert_sensible_cursor(&*access, self));

        let mut mv_key = as_val(key);
        let mut mv_val = as_val(val);

        unsafe {
            lmdb_call!(ffi::mdb_cursor_put(
                self.cursor.0, &mut mv_key, &mut mv_val,
                flags.bits()));
        }

        Ok(())
    }

    /// Overwrites the current item referenced by the cursor.
    ///
    /// `key` must match the key of the current item. If the database is
    /// `DUPSORT`, `val` must still sort into the same position relative to the
    /// other items with the same key.
    ///
    /// This is intended to be used when the new data is the same size as the
    /// old. Otherwise it will simply perform a delete of the old record
    /// followed by an insert.
    ///
    /// The cursor is positioned at the new item, or on failure usually near
    /// it.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = defdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   cursor.put(&mut access, "Fourty-two", &42u32, f).unwrap();
    ///   cursor.overwrite(&mut access, "Fourty-two", &54u32, f).unwrap();
    ///   assert_eq!(("Fourty-two", &54u32), cursor.get_current(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn overwrite<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, access: &mut WriteAccessor,
         key: &K, val: &V, flags: put::Flags) -> Result<()>
    {
        try!(assert_sensible_cursor(&*access, self));

        let mut mv_key = as_val(key);
        let mut mv_val = as_val(val);

        unsafe {
            lmdb_call!(ffi::mdb_cursor_put(
                self.cursor.0, &mut mv_key, &mut mv_val,
                flags.bits() | ffi::MDB_CURRENT));
        }

        Ok(())
    }

    /// Reserves space for an entry with the given key and returns a pointer to
    /// that entry.
    ///
    /// The size of the entry is simply the size of `V`.
    ///
    /// This cannot be used on a `DUPSORT` database.
    ///
    /// The cursor is positioned at the new item, or on failure usually near
    /// it.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// #[repr(C)] #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    /// struct MyStruct {
    ///   x: i32,
    ///   y: i32,
    /// }
    /// unsafe impl lmdb::traits::LmdbRaw for MyStruct { }
    ///
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = defdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   {
    ///     let v: &mut MyStruct = cursor.reserve(&mut access, "foo", f).unwrap();
    ///     // Write directly into the database
    ///     v.x = 42;
    ///     v.y = 56;
    ///   }
    ///
    ///   assert_eq!(("foo", &MyStruct { x: 42, y: 56 }),
    ///              cursor.get_current(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn reserve<'access, K : AsLmdbBytes + ?Sized,
                   V : FromReservedLmdbBytes + Sized>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, flags: put::Flags) -> Result<&'access mut V>
    {
        unsafe {
            self.reserve_unsized(access, key, mem::size_of::<V>(), flags)
        }
    }

    /// Reserves space for an entry with the given key and returns a pointer to
    /// an array of values backing that entry.
    ///
    /// The size of the entry is simply the size of `V` times the desired
    /// number of elements.
    ///
    /// This cannot be used on a `DUPSORT` database. (Do not confuse with
    /// `put_multiple`, which does support `DUPSORT` but is not zero-copy.)
    ///
    /// The cursor is positioned at the new item, or on failure usually near
    /// it.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// #[repr(C)] #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    /// struct MyStruct {
    ///   x: i32,
    ///   y: i32,
    /// }
    /// unsafe impl lmdb::traits::LmdbRaw for MyStruct { }
    ///
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = defdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   {
    ///     let v: &mut [u8] = cursor.reserve_array(&mut access, "foo", 4, f).unwrap();
    ///     // Write directly into the database
    ///     v[0] = b'b'; v[1] = b'y'; v[2] = b't'; v[3] = b'e';
    ///   }
    ///
    ///   assert_eq!(("foo", "byte"), cursor.get_current(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn reserve_array<'access, K : AsLmdbBytes + ?Sized,
                         V : LmdbRaw>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, count: usize, flags: put::Flags)
         -> Result<&'access mut [V]>
    {
        unsafe {
            self.reserve_unsized(
                access, key, count * mem::size_of::<V>(), flags)
        }
    }

    /// Reserves space for an entry with the given key and returns a pointer to
    /// that entry.
    ///
    /// This cannot be used on a `DUPSORT` database.
    ///
    /// The cursor is positioned at the new item, or on failure usually near
    /// it.
    ///
    /// ## Unsafety
    ///
    /// The caller must ensure that `size` is a valid size for `V`.
    pub unsafe fn reserve_unsized<'access, K : AsLmdbBytes + ?Sized,
                                  V : FromReservedLmdbBytes + ?Sized>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, size: usize, flags: put::Flags) -> Result<&'access mut V>
    {
        try!(assert_sensible_cursor(&*access, self));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        out_val.mv_size = size;

        lmdb_call!(ffi::mdb_cursor_put(
            self.cursor.0, &mut mv_key, &mut out_val,
            flags.bits() | ffi::MDB_RESERVE));

        Ok(from_reserved(access, &out_val))
    }

    /// Returns a writable reference to the value belonging to the given key in
    /// the database.
    ///
    /// This has all the caveats of both `overwrite()` and `reserve()`.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = defdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   cursor.put(&mut access, "count", &1u32, f).unwrap();
    ///   {
    ///     let count: &mut u32 = cursor.overwrite_in_place(
    ///       &mut access, "count", f).unwrap();
    ///     // Directly edit the value in the database
    ///     *count += 1;
    ///   }
    ///   assert_eq!(("count", &2u32), cursor.get_current(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn overwrite_in_place<'access, K : AsLmdbBytes + ?Sized,
                              V : FromReservedLmdbBytes + Sized>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, flags: put::Flags) -> Result<&'access mut V>
    {
        unsafe {
            self.overwrite_in_place_unsized(
                access, key, mem::size_of::<V>(), flags)
        }
    }

    /// Returns a writable reference to the array of values belonging to the
    /// given key in the database.
    ///
    /// This has all the caveats of both `overwrite()` and `reserve_array()`.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = defdb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   cursor.put(&mut access, "foo", "bar", f).unwrap();
    ///   {
    ///     let data: &mut [u8] = cursor.overwrite_in_place_array(
    ///       &mut access, "foo", 3, f).unwrap();
    ///     // Directly edit the value in the database
    ///     data[2] = b'z';
    ///   }
    ///   assert_eq!(("foo", "baz"), cursor.get_current(&access).unwrap());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn overwrite_in_place_array<'access, K : AsLmdbBytes + ?Sized,
                                    V : LmdbRaw>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, count: usize, flags: put::Flags)
         -> Result<&'access mut [V]>
    {
        unsafe {
            self.overwrite_in_place_unsized(
                access, key, count * mem::size_of::<V>(), flags)
        }
    }

    /// Returns a writable reference to the value belonging to the given key in
    /// the database.
    ///
    /// This has all the caveats of both `overwrite()` and `reserve_unsized()`.
    ///
    /// ## Unsafety
    ///
    /// The caller must ensure `size` is a valid size of `V`.
    pub unsafe fn overwrite_in_place_unsized
        <'access, K : AsLmdbBytes + ?Sized, V : FromReservedLmdbBytes + ?Sized>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, size: usize, flags: put::Flags) -> Result<&'access mut V>
    {
        try!(assert_sensible_cursor(&*access, self));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        out_val.mv_size = size;

        lmdb_call!(ffi::mdb_cursor_put(
            self.cursor.0, &mut mv_key, &mut out_val,
            flags.bits() | ffi::MDB_RESERVE | ffi::MDB_CURRENT));

        Ok(from_reserved(access, &out_val))
    }

    /// Stores multiple data elements with the same key in a single request.
    ///
    /// This is only permitted for `DUPFIXED` databases.
    ///
    /// Note that `values` must be a slice of `LmdbRaw`, since this function
    /// needs to know the exact size of each individual item and must be able
    /// to directly reinterpret the slice as a byte array.
    ///
    /// On success, returns the number of items that were actually written.
    ///
    /// ## Warning
    ///
    /// `MDB_MULTIPLE` has historically been rather problematic. Using this
    /// function may result in erratic behaviour on many versions of LMDB.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!("src/example_helpers.rs");
    /// # fn main() {
    /// # let env = create_env();
    /// # let db = dupfixeddb(&env);
    /// let txn = lmdb::WriteTransaction::new(&env).unwrap();
    /// {
    ///   let mut access = txn.access();
    ///   let f = lmdb::put::Flags::empty();
    ///   let mut cursor = txn.cursor(&db).unwrap();
    ///   // XXX Whether this is supposed to be 4 or 3 is unclear.
    ///   assert_eq!(4, cursor.put_multiple(
    ///     &mut access, "bar", &[0u32, 1u32, 2u32, 1u32], f).unwrap());
    /// # // XXX I wanted a lot more assertions here, but I kept running into
    /// # // issues that I think but am not sure are bugs.
    ///
    ///   assert_eq!(("bar", &0u32), cursor.first(&access).unwrap());
    ///   assert_eq!(("bar", &1u32), cursor.next(&access).unwrap());
    ///   assert_eq!(("bar", &2u32), cursor.next(&access).unwrap());
    ///   assert!(cursor.next::<str,u32>(&access).is_err());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn put_multiple<K : AsLmdbBytes + ?Sized, V : LmdbRaw>
        (&mut self, access: &mut WriteAccessor,
         key: &K, values: &[V], flags: put::Flags)
         -> Result<usize>
    {
        try!(assert_sensible_cursor(&*access, self));

        // Some LMDB versions didn't (don't?) handle count=0 correctly
        if values.is_empty() {
            return Ok(0);
        }

        let mut mv_key = as_val(key);
        let mut mv_vals = [ ffi::MDB_val {
            mv_size: mem::size_of::<V>() as libc::size_t,
            mv_data: values.as_lmdb_bytes().as_ptr() as *mut c_void,
        }, ffi::MDB_val {
            mv_size: values.len() as libc::size_t,
            mv_data: ptr::null_mut(),
        }];

        unsafe {
            lmdb_call!(ffi::mdb_cursor_put(
                self.cursor.0, &mut mv_key, mv_vals.as_mut_ptr(),
                flags.bits() | ffi::MDB_MULTIPLE));
        }

        Ok(mv_vals[1].mv_size as usize)
    }

    /// Delete current key/value pair.
    ///
    /// By default, this deletes only the current pair. `flags` can be set to
    /// `NODUPDATA` for `DUPDATA` databases to delete everything with the
    /// current key.
    ///
    /// See `lmdb_zero::del::NODUPDATA` for examples on how `flags` can be used
    /// to control behaviour.
    pub fn delete(&mut self, access: &mut WriteAccessor,
                  flags: del::Flags) -> Result<()> {
        try!(assert_sensible_cursor(&*access, self));

        unsafe {
            lmdb_call!(ffi::mdb_cursor_del(self.cursor.0, flags.bits()));
        }

        Ok(())
    }

    /// Return count of duplicates for current key.
    ///
    /// This call is only valid on `DUPSORT` databases.
    pub fn count(&mut self) -> Result<usize> {
        let mut raw: libc::size_t = 0;
        unsafe {
            lmdb_call!(ffi::mdb_cursor_count(self.cursor.0, &mut raw));
        }
        Ok(raw as usize)
    }
}
