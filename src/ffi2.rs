// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Things missing from liblmdb-sys
// This module is private to lmdb-zero.

use libc::{c_char, c_int, c_uint, size_t};

use ffi;

pub const MDB_BAD_DBI: c_int = -30780;
pub const MDB_CP_COMPACT: c_uint = 1;

extern "C" {
    pub fn mdb_env_copy2(env: *mut ffi::MDB_env, path: *const c_char,
                         flags: c_uint) -> c_int;
    pub fn mdb_env_copyfd2(env: *mut ffi::MDB_env, fd: ffi::mdb_filehandle_t,
                           flags: c_uint) -> c_int;
    pub fn mdb_txn_id(txn: *mut ffi::MDB_txn) -> size_t;
}
