// Copyright 2016 FullContact, Inc
// Copyright 2017 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Module containing public traits.
//!
//! This exists as a separate module solely so that it can be wildcard imported
//! where necessary.

use std::char;
use std::cmp::Ord;
use std::ffi::CStr;
use std::mem;
use std::num::Wrapping;
use std::rc::Rc;
use std::slice;
use std::str;
use std::sync::Arc;

use supercow::Supercow;

use ::Ignore;
use cursor::{Cursor, StaleCursor};
use dbi::Database;
use tx::{ConstTransaction, ReadTransaction, WriteTransaction};

pub use error::{self, LmdbResultExt};

/// Extension trait for `Rc` and `Arc` that allows up-casting a reference to
/// `ReadTransaction` or `WriteTransaction` to `ConstTransaction`.
pub trait TxExt {
    #[allow(missing_docs)]
    type Const;
    /// Returns `self` as a handle to a `ConstTransaction` rather than the
    /// subtype that was passed in.
    ///
    /// This is still a shared handle to the same transaction.
    fn to_const(self) -> Self::Const;
}

impl<'a> TxExt for Rc<ReadTransaction<'a>> {
    type Const = Rc<ConstTransaction<'a>>;
    // This is safe, despite appearances. `ReadTransaction` (and below, also
    // `WriteTransaction`) are newtypes, which are guaranteed to have exactly
    // the same memory representation as the thing they wrap. Further, they
    // have no `impl Drop` of their own, so the resulting drop code is exactly
    // equal for both `Rc<ConstTransaction>` and `Rc<ReadTransaction>`.
    fn to_const(self) -> Self::Const { unsafe { mem::transmute(self) } }
}
impl<'a> TxExt for Rc<WriteTransaction<'a>> {
    type Const = Rc<ConstTransaction<'a>>;
    fn to_const(self) -> Self::Const { unsafe { mem::transmute(self) } }
}
impl<'a> TxExt for Arc<ReadTransaction<'a>> {
    type Const = Arc<ConstTransaction<'a>>;
    fn to_const(self) -> Self::Const { unsafe { mem::transmute(self) } }
}
impl<'a> TxExt for Arc<WriteTransaction<'a>> {
    type Const = Arc<ConstTransaction<'a>>;
    fn to_const(self) -> Self::Const { unsafe { mem::transmute(self) } }
}

/// Types of transaction references which can be used to construct `Cursor`s.
///
/// In most cases this is simply used as an extension trait (see the examples
/// on `Cursor`). However, it can also be used to abstract over things that can
/// be used to create `Cursor`s if so desired.
///
/// Implementations are provided for references to the three general
/// transaction types, as well as `Rc` and `Arc` directly wrapping either
/// concrete transaction type with a `'static` lifetime.
pub trait CreateCursor<'txn> {
    /// Create a cursor using `self` as the reference to the containing
    /// transaction and `db` as the database the cursor will read from and
    /// write into.
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>>;
}

impl<'txn, 'env: 'txn> CreateCursor<'txn> for &'txn ConstTransaction<'env> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        ConstTransaction::cursor(*self, db)
    }
}

impl<'txn, 'env: 'txn> CreateCursor<'txn> for &'txn ReadTransaction<'env> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        ConstTransaction::cursor(*self, db)
    }
}

impl<'txn, 'env: 'txn> CreateCursor<'txn> for &'txn WriteTransaction<'env> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        ConstTransaction::cursor(*self, db)
    }
}

impl<'txn> CreateCursor<'txn> for Rc<ReadTransaction<'static>> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        Cursor::construct(Supercow::shared(self.clone().to_const()),
                          db.into())
    }
}

impl<'txn> CreateCursor<'txn> for Arc<ReadTransaction<'static>> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        Cursor::construct(Supercow::shared(self.clone().to_const()),
                          db.into())
    }
}

impl<'txn> CreateCursor<'txn> for Rc<WriteTransaction<'static>> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        Cursor::construct(Supercow::shared(self.clone().to_const()),
                          db.into())
    }
}

impl<'txn> CreateCursor<'txn> for Arc<WriteTransaction<'static>> {
    #[inline]
    fn cursor<'db, DB>(&self, db: DB)
                       -> error::Result<Cursor<'txn,'db>>
    where DB : Into<Supercow<'db, Database<'db>>> {
        Cursor::construct(Supercow::shared(self.clone().to_const()),
                          db.into())
    }
}

/// Types of transaction references which can be used to renew `StaleCursor`s
/// into functional `Cursor`s.
///
/// In most cases this is simply used as an extension trait (see the examples
/// on `Cursor`). However, it can also be used to abstract over things that can
/// be used to create `Cursor`s if so desired.
///
/// Implementations are provided for normal references to `ReadTransaction` as
/// well as `Rc` and `Arc`. The latter two require the transaction's inner
/// lifetime to be `'static`.
pub trait AssocCursor<'txn> {
    /// Associates a saved read-only with this transaction.
    ///
    /// The cursor will be rebound to this transaction, but will continue using
    /// the same database that it was previously.
    fn assoc_cursor<'db>(&self, cursor: StaleCursor<'db>)
                         -> error::Result<Cursor<'txn,'db>>;
}

impl<'txn,'env: 'txn> AssocCursor<'txn> for &'txn ReadTransaction<'env> {
    fn assoc_cursor<'db>(&self, cursor: StaleCursor<'db>)
                         -> error::Result<Cursor<'txn,'db>> {
        ReadTransaction::assoc_cursor(*self, cursor)
    }
}

impl<'txn> AssocCursor<'txn> for Rc<ReadTransaction<'static>> {
    fn assoc_cursor<'db>(&self, cursor: StaleCursor<'db>)
                         -> error::Result<Cursor<'txn,'db>> {
        Cursor::from_stale(cursor, Supercow::shared(self.clone().to_const()))
    }
}

impl<'txn> AssocCursor<'txn> for Arc<ReadTransaction<'static>> {
    fn assoc_cursor<'db>(&self, cursor: StaleCursor<'db>)
                         -> error::Result<Cursor<'txn,'db>> {
        Cursor::from_stale(cursor, Supercow::shared(self.clone().to_const()))
    }
}

/// Translates a value into a byte slice to be stored in LMDB.
///
/// This is similar to `AsRef<[u8]>`, but is separate since there are
/// things one may wish to store in LMDB but not have implicitly coerce to
/// `&[u8]` in other contexts.
///
/// Blanket impls are provided for `LmdbRaw` and for slices of `LmdbRaw`
/// values. Ideally there'd be one for anything `AsRef<[u8]>`, but in Rust
/// 1.10 that's not possible due to coherence rules barring having
/// blanket implementations for both `LmdbRaw` and `AsRef<[u8]>`, so
/// currently it is provided only for `&str` and `&Vec<u8>`.
///
/// _This is not a general-purpose serialisation mechanism._ There is no
/// way to use this trait to store values in a format other than how they
/// are natively represented in memory. Doing this requires serialisation
/// into a byte array before passing it onto lmdb-zero.
pub trait AsLmdbBytes {
    /// Casts the given reference to a byte slice appropriate for storage
    /// in LMDB.
    fn as_lmdb_bytes(&self) -> &[u8];
}

/// Inverts `AsLmdbBytes`, producing a reference to a structure inside a
/// byte array.
///
/// Blanket implementations are provided for `LmdbRaw` and slices of
/// `LmdbRaw` things.
///
/// _This is not a general-purpose deserialisation mechanism._ There is no
/// way to use this trait to read values in any format other than how they
/// are natively represented in memory. The only control is that outright
/// invalid values can be rejected so as to avoid undefined behaviour from,
/// eg, constructing `&str`s with malformed content. Reading values not in
/// native format requires extracting the byte slice and using a separate
/// deserialisation mechanism.
pub trait FromLmdbBytes {
    /// Given a byte slice, return an instance of `Self` described, or
    /// `Err` with an error message if the given byte slice is not an
    /// appropriate value.
    fn from_lmdb_bytes(&[u8]) -> Result<&Self, String>;
}

/// Like `FromLmdbBytes`, but can be used with `put_reserve()` calls.
///
/// A blanket implementation is provided for anything which is `LmdbRaw`.
pub trait FromReservedLmdbBytes {
    /// Given a mutable byte slice containing arbitrary data, return an
    /// instance of `Self`.
    ///
    /// This is not allowed to fail, since there is no control over the
    /// original content of the slice.
    ///
    /// ## Unsafety
    ///
    /// This function is allowed to blindly assume that the byte slice is
    /// an appropriate size.
    unsafe fn from_reserved_lmdb_bytes(&mut [u8]) -> &mut Self;
}

/// Marker trait indicating a value is to be stored in LMDB by simply
/// copying it in.
///
/// This trait implies that one wants integers and such in native byte order
/// and doesn't care about inter-ABI portability of the values. There are a lot
/// of safety implications as well.
///
/// Implementing this trait provides blanket implementations of
/// `AsLmdbBytes`, `FromLmdbBytes`, and `FromReservedLmdbBytes`.
///
/// See also [`LmdbRawIfUnaligned`](trait.LmdbRawIfUnaligned.html) for types
/// that become `LmdbRaw` when wrapped with
/// [`Unaligned`](../struct.Unaligned.html). In particular, all integer and
/// floating-point types are `LmdbRawIfUnaligned`, except for `u8` and `i8`
/// which are also `LmdbRaw`.
///
/// ## Alignment
///
/// The `FromLmdbBytes` conversion fails if the alignment of the input data
/// does not satisfy the alignment of the type. This means that behaviour will
/// be unpredictable if the required alignment of the struct is greater than 1,
/// as conversions will pass or fail depending on where LMDB decides to place
/// the value.
///
/// If you run into this issue, there are several ways to work around it.
///
/// ### Use `Unaligned`
///
/// Instead of directly reading and writing the bare type, wrap it in
/// `lmdb_zero::Unaligned`. This adds no overhead in and of itself and removes
/// the alignment restriction, but heavily restricts what can be done with a
/// reference without copying it.
///
/// This is almost always the best option if your type fits in a register or
/// two.
///
/// ### Make your structure `#[repr(C, packed)]`
///
/// If this is a problem, you can make your structure `#[repr(packed)]` to give
/// it an alignment of 1 (but see also below about padding).
///
/// Note that it is possible to produce unsafe code using this approach even
/// without the use of `unsafe`. See [this rust
/// bug](https://github.com/rust-lang/rust/issues/27060).
///
/// ### Do it yourself
///
/// If you have unusual requirements, your best bet is to implement
/// `FromLmdbBytes` and friends manually as needed.
///
/// ## Unsafety
///
/// If the tagged type contains pointers of any kind, they will be stored in
/// and retrieved from the database, which has serious ramifications,
/// especially when the `FromReservedLmdbBytes` implementation is used. If the
/// type contains Rust references, this will almost certainly lead to undefined
/// behaviour.
///
/// Behaviour is undefined if there exist bit patterns of the same size of the
/// type which are not valid instances of that type unless the client code can
/// somehow guarantee that such bit patterns do not occur. If this is a
/// problem, implement `AsLmdbBytes` and `FromLmdbBytes` manually and check for
/// validity. Of particular note, `bool` and essentially all `enum` types are
/// not sensible for use with `LmdbRaw` (directly or within composites) because
/// they are only valid for particular bit patterns.
///
/// ## Warnings about inner padding
///
/// Use of this trait on a struct that is not `#[repr(packed)]` makes it
/// possible to observe the normally unobservable padding bytes inserted into
/// the structure to satisfy type alignment.
///
/// When simply using these structures as values in a non-`DUPSORT` database,
/// this simply means some arbitrary extra bytes get written with the values.
/// This is not going to be a problem unless you plan on sharing the databases
/// with untrusted third parties (which could leak sensitive information) or do
/// unusual things with type punning.
///
/// However, in any context where values need to be compared (ie, keys, and
/// values in `DUPSORT` databases), these padding bytes now count towards the
/// comparison by default. Since the padding contains unpredictable values, you
/// can easily end up with multiple "identical" keys that differ in their
/// padding bytes, fail to find values you know are in the database because of
/// differences in padding values, etc.
///
/// One way to deal with both problems is to use `#[repr(packed)]` (in addition
/// to `#[repr(C)]` which keeps the field order defined across Rust versions),
/// which simply eliminates the padding bytes altogether. Note that due to a
/// bug in the Rust compiler, [packed structures can lead to undefined
/// behaviour in "safe Rust"](https://github.com/rust-lang/rust/issues/27060).
/// Until that issue is fixed, you should be careful about using
/// `#[repr(packed)]` for this purpose unless all fields in the struct have the
/// same size or you understand the ABI(s) you care about well enough to know
/// whether misalignment will cause issues.
///
/// You can alternatively opt to live with the padding bytes, but additionally
/// implement `LmdbOrdKey` on the type, and then use
/// `DatabaseOptions::sort_keys_as` or `DatabaseOptions::sort_values_as`
/// appropriately to use the generated comparison function. As a result, the
/// padding bytes will be ignored for comparison purposes, but will nontheless
/// be written into the database and thus remain visible to puns and could leak
/// information.
///
/// ## Example
///
/// ```
/// use lmdb_zero::traits::*;
///
/// #[repr(C)]
/// #[derive(Clone,Copy,Debug)]
/// struct MyStruct {
///   foo: i16,
///   // See warning about alignment/padding above!
///   // On AMD64, for example, we get 6 padding bytes here.
///   bar: u64,
/// }
/// unsafe impl LmdbRaw for MyStruct { }
/// ```
pub unsafe trait LmdbRaw : Copy + Sized {
    /// Returns the name of this type to report in error messages.
    ///
    /// If not implemented, defaults to `"?"`.
    fn reported_type() -> String {
        "?".to_owned()
    }
}

/// Marker trait for types where `Unaligned<T>` is `LmdbRaw`.
///
/// This has all the implications as `LmdbRaw`, except that blanket
/// implementations around the bare type are not available. This forces the
/// client code to wrap the type in `Unaligned` to explicitly handle possible
/// misalignment.
///
/// All integer and floating-point types have this trait.
///
/// Note that `LmdbRawIfUnaligned` is not blanket-implemented for fixed-size
/// arrays, because currently doing so would preclude a blanket implementation
/// of `LmdbRaw` for fixed-size arrays. Since the latter is generally more
/// useful and is more consistent since variable-length slices can only
/// usefully interact with `LmdbRaw`, that approach was chosen.
///
/// All `LmdbRaw` types are `LmdbRawIfUnaligned`.
pub unsafe trait LmdbRawIfUnaligned : Copy + Sized {
    /// Returns the name of this type to report in error messages.
    ///
    /// If not implemented, defaults to `"?"`.
    fn reported_type() -> String {
        "?".to_owned()
    }
}

unsafe impl<T : LmdbRaw> LmdbRawIfUnaligned for T {
    fn reported_type() -> String {
        <T as LmdbRaw>::reported_type()
    }
}

/// Trait describing a value which can be used as an LMDB key by having LMDB
/// call into the value's `Ord` implementation.
///
/// ## Unsafety
///
/// Behaviour is undefined if the `FromLmdbBytes` or `Ord` implementations
/// panic.
pub unsafe trait LmdbOrdKey : FromLmdbBytes + Ord {
    /// Returns whether the default LMDB byte-by-byte comparison is correct for
    /// valid values of this type.
    ///
    /// Generally, one should not specifically use
    /// `DatabaseOptions::sort_values_as` and so forth for types where this is
    /// the case. This function exists to support generic code wishing to avoid
    /// the conversion overhead when the types happen to already be
    /// byte-comparable.
    ///
    /// Note that if this returns true, that does _not_ mean that byte
    /// comparison is exactly equivalent to `Ord`-based comparison. For
    /// example, invalid `str` instances sort before valid ones and are equal
    /// to each other, but byte comparison will intermingle them. Because of
    /// this, `DatabaseOptions::sort_values_as` and similar do not make
    /// decisions based on this value; it is the client code's responsibility
    /// to use this if so desired.
    ///
    /// ## Example
    /// ```
    /// # use lmdb_zero::traits::LmdbOrdKey;
    /// assert!(<u8 as LmdbOrdKey>::ordered_by_bytes());
    /// assert!(!<i8 as LmdbOrdKey>::ordered_by_bytes());
    /// assert!(<str as LmdbOrdKey>::ordered_by_bytes());
    /// assert!(<[u8] as LmdbOrdKey>::ordered_by_bytes());
    /// assert!(!<[i8] as LmdbOrdKey>::ordered_by_bytes());
    /// ```
    fn ordered_by_bytes() -> bool { false }

    /// Returns whether LMDB will correctly handle this value with the
    /// `INTEGERKEY` or `INTEGERDUP` flags.
    ///
    /// There's generally no reason to use `sort_keys_as` and so forth with
    /// values where this is true instead of using the appropriate flags. This
    /// function exists to support generic code which wants to make such
    /// decisions automatically.
    fn ordered_as_integer() -> bool { false }
}

/// Marker trait for types where `Unaligned<T>` is `LmdbOrdKey`.
///
/// All `LmdbOrdKey + LmdbRaw` are `LmdbOrdKeyIfUnaligned`.
///
/// ## Unsafety
///
/// Behaviour is undefined if the `FromLmdbBytes` or `Ord` implementations
/// panic.
pub unsafe trait LmdbOrdKeyIfUnaligned : LmdbRawIfUnaligned + Ord {
    /// Like `LmdbOrdKey::ordered_by_bytes()`
    fn ordered_by_bytes() -> bool { false }
    /// Like `LmdbOrdKey::ordered_as_integer()`
    fn ordered_as_integer() -> bool { false }
}

unsafe impl<T : LmdbRaw + LmdbOrdKey> LmdbOrdKeyIfUnaligned for T {
    fn ordered_by_bytes() -> bool {
        <T as LmdbOrdKey>::ordered_by_bytes()
    }

    fn ordered_as_integer() -> bool {
        <T as LmdbOrdKey>::ordered_as_integer()
    }
}

macro_rules! raw {
    ($typ:ident) => {
        unsafe impl LmdbRawIfUnaligned for $typ {
            fn reported_type() -> String {
                stringify!($typ).to_owned()
            }
        }
        impl AsLmdbBytes for $typ {
            fn as_lmdb_bytes(&self) -> &[u8] {
                unsafe {
                    slice::from_raw_parts(
                        self as *const $typ as *const u8,
                        mem::size_of::<$typ>())
                }
            }
        }
        impl AsLmdbBytes for [$typ] {
            fn as_lmdb_bytes(&self) -> &[u8] {
                unsafe {
                    slice::from_raw_parts(
                        self.as_ptr() as *const u8,
                        self.len() * mem::size_of::<$typ>())
                }
            }
        }
    };

    ($typ:ident, Ord) => {
        raw!($typ);
        unsafe impl LmdbOrdKeyIfUnaligned for $typ { }
    };

    ($typ:ident, Int) => {
        raw!($typ);
        unsafe impl LmdbOrdKeyIfUnaligned for $typ {
            fn ordered_as_integer() -> bool { true }
        }
    };
}

unsafe impl LmdbRaw for u8 {
    fn reported_type() -> String {
        "u8".to_owned()
    }
}
unsafe impl LmdbOrdKey for u8 {
    fn ordered_by_bytes() -> bool { true }
}
unsafe impl LmdbRaw for i8 {
    fn reported_type() -> String {
        "i8".to_owned()
    }
}
unsafe impl LmdbOrdKey for i8 { }
raw!(u16, Ord);
raw!(i16, Ord);
raw!(u32, Int);
raw!(i32, Ord);
raw!(u64, Ord);
raw!(i64, Ord);
raw!(f32);
raw!(f64);

macro_rules! raw_array {
    ($n:expr) => {
        unsafe impl<V : LmdbRaw> LmdbRaw for [V;$n] {
            fn reported_type() -> String {
                format!("[{};{}]", V::reported_type(), $n)
            }
        }
        unsafe impl<V : LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;$n] {
            fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
        }
    }
}
raw_array!(0);
raw_array!(1);
raw_array!(2);
raw_array!(3);
raw_array!(4);
raw_array!(5);
raw_array!(6);
raw_array!(7);
raw_array!(8);
raw_array!(9);
raw_array!(10);
raw_array!(11);
raw_array!(12);
raw_array!(13);
raw_array!(14);
raw_array!(15);
raw_array!(16);
raw_array!(17);
raw_array!(18);
raw_array!(19);
raw_array!(20);
raw_array!(21);
raw_array!(22);
raw_array!(23);
raw_array!(24);
raw_array!(25);
raw_array!(26);
raw_array!(27);
raw_array!(28);
raw_array!(29);
raw_array!(30);
raw_array!(31);
raw_array!(32);

unsafe impl<V: LmdbRawIfUnaligned> LmdbRawIfUnaligned for Wrapping<V> {
    fn reported_type() -> String {
        format!("Wrapping<{}>", V::reported_type())
    }
}
unsafe impl<V: LmdbOrdKeyIfUnaligned> LmdbOrdKeyIfUnaligned for Wrapping<V> {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}

unsafe impl LmdbRaw for () { }

impl<V : LmdbRaw> AsLmdbBytes for V {
    fn as_lmdb_bytes(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const V as *const u8, mem::size_of::<V>())
        }
    }
}

impl<V: LmdbRaw> FromLmdbBytes for V {
    fn from_lmdb_bytes(bytes: &[u8]) -> Result<&Self, String> {
        let size = mem::size_of::<V>();
        let align = mem::align_of::<V>();

        if bytes.len() != size {
            return Err(
                format!("Type {} is size {}, but byte array has size {}",
                        V::reported_type(), size, bytes.len()));
        }

        let misalign = (bytes.as_ptr() as usize) % align;
        if 0 != misalign {
            return Err(
                format!("Type {} requires alignment {}, but byte array \
                         at {:08x} is misaligned by {} bytes \
                         (see https://docs.rs/lmdb-zero/{}/\
                         lmdb_zero/traits/trait.LmdbRaw.html#alignment)",
                        V::reported_type(), align,
                        (bytes.as_ptr() as usize), misalign,
                        env!("CARGO_PKG_VERSION")));
        }

        Ok(unsafe {
            mem::transmute(bytes.as_ptr())
        })
    }
}

impl<V : LmdbRaw> FromReservedLmdbBytes for V {
    unsafe fn from_reserved_lmdb_bytes(bytes: &mut [u8]) -> &mut Self {
        mem::transmute(bytes.as_ptr())
    }
}

impl<V : LmdbRaw> AsLmdbBytes for [V] {
    fn as_lmdb_bytes(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self.as_ptr() as *const u8,
                self.len() * mem::size_of::<V>())
        }
    }
}

impl<V : LmdbRaw> FromLmdbBytes for [V] {
    fn from_lmdb_bytes(bytes: &[u8]) -> Result<&Self, String> {
        let size = mem::size_of::<V>();
        let align = mem::align_of::<V>();

        let size_mod = bytes.len() % size;
        if 0 != size_mod {
            return Err(
                format!("Type [{}] must have a size which is a multiple \
                         of {}, but byte array has size {} ({} trailing bytes)",
                        V::reported_type(), size, bytes.len(), size_mod));
        }

        let misalign = (bytes.as_ptr() as usize) % align;
        if 0 != misalign {
            return Err(
                format!("Type [{}] requires alignment {}, but byte array \
                         at {:08x} is misaligned by {} bytes \
                         (see https://docs.rs/lmdb-zero/{}/\
                         lmdb_zero/traits/trait.LmdbRaw.html#alignment)",
                        V::reported_type(), align,
                        (bytes.as_ptr() as usize), misalign,
                        env!("CARGO_PKG_VERSION")));
        }

        unsafe {
            Ok(slice::from_raw_parts(
                bytes.as_ptr() as *const V,
                bytes.len() / size))
        }
    }
}

impl<V : LmdbRaw> FromReservedLmdbBytes for [V] {
    unsafe fn from_reserved_lmdb_bytes(bytes: &mut [u8]) -> &mut Self {
        slice::from_raw_parts_mut(
            bytes.as_ptr() as *mut V,
            bytes.len() / mem::size_of::<V>())
    }
}

unsafe impl<V : LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}

impl AsLmdbBytes for CStr {
    /// Returns the raw content of the `CStr`, including the trailing NUL.
    fn as_lmdb_bytes(&self) -> &[u8] {
        self.to_bytes_with_nul()
    }
}

impl FromLmdbBytes for CStr {
    /// Directly converts the byte slice into a `CStr`, including a
    /// required trailing NUL.
    fn from_lmdb_bytes(bytes: &[u8]) -> Result<&Self, String> {
        CStr::from_bytes_with_nul(bytes).map_err(
            |_| "NUL byte in CString value".to_owned())
    }
}

unsafe impl LmdbOrdKey for CStr {
    fn ordered_by_bytes() -> bool { true }
}

impl AsLmdbBytes for str {
    fn as_lmdb_bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl FromLmdbBytes for str {
    fn from_lmdb_bytes(bytes: &[u8]) -> Result<&str, String> {
        str::from_utf8(bytes).map_err(
            |_| "String is not valid UTF-8".to_owned())
    }
}

unsafe impl LmdbOrdKey for str {
    fn ordered_by_bytes() -> bool { true }
}

impl<V : LmdbRaw> AsLmdbBytes for Vec<V> {
    fn as_lmdb_bytes(&self) -> &[u8] {
        &self[..].as_lmdb_bytes()
    }
}

static IGNORE: Ignore = Ignore;

impl FromLmdbBytes for Ignore {
    fn from_lmdb_bytes(_: &[u8]) -> Result<&Ignore, String> {
        Ok(&IGNORE)
    }
}

impl AsLmdbBytes for char {
    fn as_lmdb_bytes(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const char as *const u8,
                mem::size_of::<char>())
        }
    }
}

impl AsLmdbBytes for [char] {
    fn as_lmdb_bytes(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self.as_ptr() as *const u8,
                self.len() * mem::size_of::<char>())
        }
    }
}
