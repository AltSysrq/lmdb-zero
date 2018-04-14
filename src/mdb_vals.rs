// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Internal helpers for working with `MDB_val`s.

use std::mem;
use std::slice;
use libc::{self, c_void};

use ffi;

use error::{Error, Result};
use traits::*;

pub const EMPTY_VAL: ffi::MDB_val = ffi::MDB_val {
    mv_size: 0,
    mv_data: 0 as *mut c_void,
};

pub fn as_val<V : AsLmdbBytes + ?Sized>(v: &V) -> ffi::MDB_val {
    let bytes = v.as_lmdb_bytes();
    ffi::MDB_val {
        mv_size: bytes.len() as libc::size_t,
        mv_data: unsafe { mem::transmute(bytes.as_ptr()) },
    }
}

pub fn mdb_val_as_bytes<'a,O>(_o: &'a O, val: &ffi::MDB_val) -> &'a[u8] {
    debug_assert!(!val.mv_data.is_null(), "MDB_val ptr is NULL, size = {}",
                  val.mv_size);

    unsafe {
        slice::from_raw_parts(
            mem::transmute(val.mv_data), val.mv_size as usize)
    }
}

pub fn from_val<'a, O, V : FromLmdbBytes + ?Sized>(
    _owner: &'a O, val: &ffi::MDB_val) -> Result<&'a V>
{
    let bytes = mdb_val_as_bytes(_owner, val);
    V::from_lmdb_bytes(bytes).map_err(|s| Error::ValRejected(s))
}

pub unsafe fn from_reserved<'a, O, V : FromReservedLmdbBytes + ?Sized>(
    _owner: &'a O, val: &ffi::MDB_val) -> &'a mut V
{
    let bytes = slice::from_raw_parts_mut(
        mem::transmute(val.mv_data), val.mv_size as usize);
    V::from_reserved_lmdb_bytes(bytes)
}

