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

use std::ffi::CStr;
use std::mem;
use std::slice;
use std::str;

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
/// _This is not a general-purpose deserialisation mechanism._ There is now
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
    /// the appropriate size.
    unsafe fn from_reserved_lmdb_bytes(&mut [u8]) -> &mut Self;
}

/// Marker trait indicating a value is to be stored in LMDB by simply
/// copying it in.
///
/// This implies that one wants integers and such in native byte order, and
/// that there are no pointers embedded in the values (or that the caller
/// takes responsibility for the ramifications of reading pointers back out
/// of a database), that either all possible bit patterns of that size
/// are valid, or that the caller takes responsibility for ensuring that
/// invalid bit patterns do not occur, and that the type has no alignment
/// requirements wider than a pointer.
///
/// Implementing this trait provides blanket implementations of
/// `AsLmdbBytes` and `FromLmdbBytes`.
///
/// All integer and floating-point types have this trait, as well as
/// fixed-width arrays of up to 32 `LmdbRaw` types, and the empty tuple.
/// (One cannot use `LmdbRaw` with tuples in general, as the physical
/// layout of tuples is not currently defined.)
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
///   bar: u64,
/// }
/// unsafe impl LmdbRaw for MyStruct { }
/// ```
pub unsafe trait LmdbRaw : Copy + Sized { }

unsafe impl LmdbRaw for bool { }
unsafe impl LmdbRaw for u8 { }
unsafe impl LmdbRaw for i8 { }
unsafe impl LmdbRaw for u16 { }
unsafe impl LmdbRaw for i16 { }
unsafe impl LmdbRaw for u32 { }
unsafe impl LmdbRaw for i32 { }
unsafe impl LmdbRaw for u64 { }
unsafe impl LmdbRaw for i64 { }
unsafe impl LmdbRaw for char { }
unsafe impl LmdbRaw for f32 { }
unsafe impl LmdbRaw for f64 { }

unsafe impl<V: LmdbRaw> LmdbRaw for [V;0] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;1] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;2] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;3] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;4] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;5] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;6] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;7] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;8] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;9] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;10] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;11] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;12] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;13] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;14] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;15] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;16] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;17] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;18] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;19] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;20] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;21] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;22] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;23] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;24] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;25] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;26] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;27] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;28] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;29] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;30] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;31] { }
unsafe impl<V: LmdbRaw> LmdbRaw for [V;32] { }

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
    fn from_lmdb_bytes(bytes: &[u8]) -> Option<&Self> {
        if bytes.len() == mem::size_of::<V>() {
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
        if bytes.len() % mem::size_of::<V>() != 0 {
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

impl<V : LmdbRaw> AsLmdbBytes for Vec<V> {
    fn as_lmdb_bytes(&self) -> &[u8] {
        &self[..].as_lmdb_bytes()
    }
}
