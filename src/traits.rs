// Copyright 2016 FullContact, Inc
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
use std::slice;
use std::str;
use libc;

use ::Ignore;

pub use error::LmdbResultExt;

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
    /// `None` if the given byte slice is not an appropriate value.
    fn from_lmdb_bytes(&[u8]) -> Option<&Self>;
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
/// All integer and floating-point types have this trait, as well as
/// fixed-width arrays of up to 32 `LmdbRaw` types, and the empty tuple.
/// (One cannot use `LmdbRaw` with tuples in general, as the physical
/// layout of tuples is not currently defined.)
///
/// ## Alignment
///
/// The `FromLmdbBytes` conversion fails if the alignment of the input data
/// does not satisfy the alignment of the type. This means that behaviour will
/// be unpredictable if the required alignment of the struct is greater than 1,
/// as conversions will pass or fail depending on where LMDB decides to place
/// the value. If this is a problem, you can make your structure
/// `#[repr(packed)]` to give it an alignment of 1 (but see also below).
/// Primitive types can be wrapped in `Unaligned` to achieve the same effect.
///
/// If you only intend to support architectures with lax alignments (eg,
/// AMD64), you can build `lmdb-zero` with the `lax_alignment` feature, which
/// eliminates this alignment test, but is not strictly safe.
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
pub unsafe trait LmdbRaw : Copy + Sized { }

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

unsafe impl LmdbRaw for u8 { }
unsafe impl LmdbOrdKey for u8 {
    fn ordered_by_bytes() -> bool { true }
}
unsafe impl LmdbRaw for i8 { }
unsafe impl LmdbOrdKey for i8 { }
unsafe impl LmdbRaw for u16 { }
unsafe impl LmdbOrdKey for u16 { }
unsafe impl LmdbRaw for i16 { }
unsafe impl LmdbOrdKey for i16 { }
unsafe impl LmdbRaw for u32 { }
unsafe impl LmdbOrdKey for u32 {
    fn ordered_as_integer() -> bool { true }
}
unsafe impl LmdbRaw for i32 { }
unsafe impl LmdbOrdKey for i32 { }
unsafe impl LmdbRaw for u64 { }
unsafe impl LmdbOrdKey for u64 {
    fn ordered_as_integer() -> bool {
        mem::size_of::<u64>() == mem::size_of::<libc::size_t>()
    }
}
unsafe impl LmdbRaw for i64 { }
unsafe impl LmdbOrdKey for i64 { }
unsafe impl LmdbRaw for f32 { }
unsafe impl LmdbRaw for f64 { }

unsafe impl<V: LmdbRaw> LmdbRaw for [V;0] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;0] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;1] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;1] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;2] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;2] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;3] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;3] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;4] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;4] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;5] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;5] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;6] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;6] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;7] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;7] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;8] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;8] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;9] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;9] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;10] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;10] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;11] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;11] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;12] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;12] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;13] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;13] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;14] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;14] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;15] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;15] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;16] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;16] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;17] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;17] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;18] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;18] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;19] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;19] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;20] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;20] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;21] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;21] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;22] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;22] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;23] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;23] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;24] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;24] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;25] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;25] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;26] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;26] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;27] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;27] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;28] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;28] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;29] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;29] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;30] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;30] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;31] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;31] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for [V;32] { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for [V;32] {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}
unsafe impl<V: LmdbRaw> LmdbRaw for Wrapping<V> { }
unsafe impl<V: LmdbOrdKey + LmdbRaw> LmdbOrdKey for Wrapping<V> {
    fn ordered_by_bytes() -> bool { V::ordered_by_bytes() }
}

unsafe impl LmdbRaw for () { }

#[cfg(lax_alignment)]
const ALIGN_LAX: bool = true;
#[cfg(not(lax_alignment))]
const ALIGN_LAX: bool = false;

impl<V : LmdbRaw> AsLmdbBytes for V {
    fn as_lmdb_bytes(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self as *const V as *const u8, mem::size_of::<V>())
        }
    }
}

impl<V: LmdbRaw> FromLmdbBytes for V {
    fn from_lmdb_bytes(bytes: &[u8]) -> Option<&Self> {
        if bytes.len() == mem::size_of::<V>() &&
            (ALIGN_LAX ||
             0 == (bytes.as_ptr() as usize) % mem::align_of::<V>())
        {
            Some(unsafe {
                mem::transmute(bytes.as_ptr())
            })
        } else {
            None
        }
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
    fn from_lmdb_bytes(bytes: &[u8]) -> Option<&Self> {
        if bytes.len() % mem::size_of::<V>() != 0 ||
            (!ALIGN_LAX &&
             0 != (bytes.as_ptr() as usize) % mem::align_of::<V>())
        {
            None
        } else {
            unsafe {
                Some(slice::from_raw_parts(
                    bytes.as_ptr() as *const V,
                    bytes.len() / mem::size_of::<V>()))
            }
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
    fn from_lmdb_bytes(bytes: &[u8]) -> Option<&Self> {
        CStr::from_bytes_with_nul(bytes).ok()
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
    fn from_lmdb_bytes(bytes: &[u8]) -> Option<&str> {
        str::from_utf8(bytes).ok()
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
    fn from_lmdb_bytes(_: &[u8]) -> Option<&Ignore> {
        Some(&IGNORE)
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
