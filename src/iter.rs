// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::iter::Iterator;
use std::ops::{Deref, DerefMut};

use cursor::Cursor;
use error::Result;
use tx::ConstAccessor;
use traits::*;

/// A mutable value which is either owned or borrowed from an owning context.
///
/// This is very different from `Cow` in that one can mutate the shared
/// reference but cannot take ownership.
#[derive(Debug)]
#[allow(missing_docs)]
pub enum MaybeOwned<'a, T : 'a> {
    Owned(T),
    Borrowed(&'a mut T),
}

impl<'a, T : 'a> Deref for MaybeOwned<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match *self {
            MaybeOwned::Owned(ref t) => t,
            MaybeOwned::Borrowed(ref t) => *t,
        }
    }
}

impl<'a, T : 'a> DerefMut for MaybeOwned<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        match *self {
            MaybeOwned::Owned(ref mut t) => t,
            // `ref mut` is necessary so we can borrow the field out of the
            // enum.
            MaybeOwned::Borrowed(ref mut t) => *t,
        }
    }
}

/// An iterator over items returned by successive calls of some function on
/// `Cursor` until a `NOTFOUND` error is returned.
///
/// Special handling is afforded the first item in the iterator, since the
/// simple act of positioning the cursor produces the first item.
pub struct CursorIter<'a, 'access: 'a, 'txn: 'access, 'db: 'txn, T> {
    cursor: MaybeOwned<'a, Cursor<'txn,'db>>,
    access: &'access ConstAccessor<'txn>,
    head: Option<T>,
    next: fn (&mut Cursor<'txn,'db>, &'access ConstAccessor<'txn>)
              -> Result<T>,
}

impl<'a, 'access: 'a, 'txn: 'access, 'db: 'txn, T>
CursorIter<'a, 'access, 'txn, 'db, T> {
    /// Creates a cursor iterator from the given cursor and accessor.
    ///
    /// `head` is invoked immediately on `cursor` and `accessor` to position
    /// the cursor. The value it returns (if any) will be used as the first
    /// value produced by the cursor.
    ///
    /// Beyond the first item, `next` will be invoked on `cursor` and
    /// `accessor` to produce further items. Note that this is a plain function
    /// pointer and not a function object so that the type does not need to be
    /// encoded in the type of this iterator.
    ///
    /// ## Example
    ///
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
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
    ///   let mut iter = lmdb::CursorIter::new(
    ///     lmdb::MaybeOwned::Borrowed(&mut cursor), &*access,
    ///     |c, a| c.first(a), lmdb::Cursor::next::<str,str>).unwrap();
    ///   assert_eq!(("Animal", "Badger"), iter.next().unwrap().unwrap());
    ///   assert_eq!(("Fruit", "Apple"), iter.next().unwrap().unwrap());
    ///   assert_eq!(("Fruit", "Orange"), iter.next().unwrap().unwrap());
    ///   assert_eq!(("Veggie", "Carrot"), iter.next().unwrap().unwrap());
    ///   assert!(iter.next().is_none());
    /// }
    /// txn.commit().unwrap();
    /// # }
    /// ```
    pub fn new<H : FnOnce(&mut Cursor<'txn,'db>,
                          &'access ConstAccessor<'txn>)
                          -> Result<T>>
        (mut cursor: MaybeOwned<'a, Cursor<'txn,'db>>,
         access: &'access ConstAccessor<'txn>,
         head: H,
         next: fn (&mut Cursor<'txn,'db>, &'access ConstAccessor<'txn>)
                   -> Result<T>)
         -> Result<Self>
    {
        let head_val = try!(head(&mut*cursor, access).to_opt());
        Ok(CursorIter {
            cursor: cursor,
            access: access,
            head: head_val,
            next: next,
        })
    }
}

impl<'a, 'access: 'a, 'txn: 'access, 'db: 'txn, T> Iterator
for CursorIter<'a, 'access, 'txn, 'db, T> {
    type Item = Result<T>;

    fn next(&mut self) -> Option<Result<T>> {
        if let Some(head) = self.head.take() {
            Some(Ok(head))
        } else {
            match (self.next)(&mut*self.cursor, self.access).to_opt() {
                Ok(Some(v)) => Some(Ok(v)),
                Ok(None) => None,
                Err(err) => Some(Err(err.into())),
            }
        }
    }
}
