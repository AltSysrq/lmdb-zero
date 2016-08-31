// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error values and types returned by LMDB and this wrapper.

use std::error::Error as StdError;
use std::ffi::{CStr, NulError};
use std::fmt;
use std::result;
use libc::c_int;

use ffi;
use ffi2;

/// A string path was given which contains a `NUL` byte.
///
/// This is not a standard LMDB error code; it is produced by the FFI layer
/// here when translating rust strings to C strings.
pub const NULSTR: c_int = ffi2::MDB_LAST_ERRCODE + 1;
/// An attempt was made to open a database which is already open.
///
/// This is not a standard LMDB error code; LMDB in fact permits opening
/// the same database one time, and silently returns the same handle to it.
/// lmdb-zero detects such cases and returns this error instead.
pub const REOPENED: c_int = NULSTR + 1;
/// An attempt was made to use two items together which cannot be used
/// together.
///
/// For example, trying to use a cursor from one transaction to access data
/// in another.
///
/// This is not a standard LMDB error code, and arises due to some
/// functions needing to take redundant inputs to make borrow checking
/// work.
pub const MISMATCH: c_int = REOPENED + 1;
/// When retrieving a value, `FromLmdbBytes` returned `None`.
///
/// This is not a standard LMDB error code, but arises when reading types
/// from the database which have invalid values.
pub const VAL_REJECTED: c_int = MISMATCH + 1;
/// key/data pair already exists
pub const KEYEXIST: c_int = ffi::MDB_KEYEXIST;
/// key/data pair not found (EOF)
pub const NOTFOUND: c_int = ffi::MDB_NOTFOUND;
/// Requested page not found - this usually indicates corruption
pub const PAGE_NOTFOUND: c_int = ffi::MDB_PAGE_NOTFOUND;
/// Located page was wrong type
pub const CORRUPTED: c_int = ffi::MDB_CORRUPTED;
/// Update of meta page failed or environment had fatal error
pub const PANIC: c_int = ffi::MDB_PANIC;
/// Environment version mismatch
pub const VERSION_MISMATCH: c_int = ffi::MDB_VERSION_MISMATCH;
/// File is not a valid LMDB file
pub const INVALID: c_int = ffi::MDB_INVALID;
/// Environment mapsize reached
pub const MAP_FULL: c_int = ffi::MDB_MAP_FULL;
/// Environment maxdbs reached
pub const DBS_FULL: c_int = ffi::MDB_DBS_FULL;
/// Environment maxreaders reached
pub const READERS_FULL: c_int = ffi::MDB_READERS_FULL;
/// Too many TLS keys in use - Windows only
pub const TLS_FULL: c_int = ffi::MDB_TLS_FULL;
/// Txn has too many dirty pages
pub const TXN_FULL: c_int = ffi::MDB_TXN_FULL;
/// Cursor stack too deep - internal error
pub const CURSOR_FULL: c_int = ffi::MDB_CURSOR_FULL;
/// Page has not enough space - internal error
pub const PAGE_FULL: c_int = ffi::MDB_PAGE_FULL;
/// Database contents grew beyond environment mapsize
pub const MAP_RESIZED: c_int = ffi::MDB_MAP_RESIZED;
/// Operation and DB incompatible, or DB type changed. This can mean:
///
/// - The operation expects an `DUPSORT` / `DUPFIXED` database.
/// - Opening a named DB when the unnamed DB has `DUPSORT` / `INTEGERKEY`.
/// - Accessing a data record as a database, or vice versa.
/// - The database was dropped and recreated with different flags.
pub const INCOMPATIBLE: c_int = ffi::MDB_INCOMPATIBLE;
/// Invalid reuse of reader locktable slot
pub const BAD_RSLOT: c_int = ffi::MDB_BAD_RSLOT;
/// Transaction must abort, has a child, or is invalid
pub const BAD_TXN: c_int = ffi::MDB_BAD_TXN;
/// Unsupported size of key/DB name/data, or wrong `DUPFIXED` size
pub const BAD_VALSIZE: c_int = ffi::MDB_BAD_VALSIZE;
/// The specified DBI was changed unexpectedly
pub const BAD_DBI: c_int = ffi2::MDB_BAD_DBI;

/// Error type returned by LMDB.
#[derive(Clone,Copy,PartialEq,Eq,Hash)]
pub struct Error {
    /// The raw error code.
    ///
    /// This is generally expected to be a constant defined in the `errors`
    /// module if negative, or a raw platform error code if positive.
    pub code: c_int,
}

/// Result type returned for all calls that can fail.
pub type Result<T> = result::Result<T, Error>;

impl Error {
    fn strerror(&self) -> &'static str {
        unsafe {
            if NULSTR == self.code {
                "NUL byte in path"
            } else if REOPENED == self.code {
                "Attempt to reopen database"
            } else if MISMATCH == self.code {
                "Items from different env/database used together"
            } else if VAL_REJECTED == self.code {
                "Value conversion failed"
            } else {
                let raw = ffi::mdb_strerror(self.code);
                if raw.is_null() {
                    "(null)"
                } else {
                    CStr::from_ptr(raw).to_str().unwrap_or("(unknown)")
                }
            }
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "Error({}, '{}')", self.code, self.strerror())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{}", self.strerror())
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        self.strerror()
    }
}

impl From<NulError> for Error {
    fn from(_: NulError) -> Self {
        Error { code: NULSTR }
    }
}

/// Extension methods for LMDB results
pub trait LmdbResultExt {
    #[allow(missing_docs)]
    type Inner;

    /// Lift "not found" errors to `None`.
    ///
    /// If `Ok(val)`, return `Ok(Some(val))`. If `Err` but the code is
    /// `NOTFOUND`, return `Ok(None)`. Otherwise, return self.
    fn to_opt(self) -> Result<Option<Self::Inner>>;

    /// Suppress `KEYEXIST` errors.
    ///
    /// If this is `Err` and the code is `KEYEXIST`, switch to `Ok` with the
    /// given inner value.
    fn ignore_exists(self, inner: Self::Inner) -> Self;
}

impl<T> LmdbResultExt for Result<T> {
    type Inner = T;

    fn to_opt(self) -> Result<Option<T>> {
        match self {
            Ok(val) => Ok(Some(val)),
            Err(error) if NOTFOUND == error.code => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn ignore_exists(self, inner: T) -> Self {
        match self {
            Ok(val) => Ok(val),
            Err(error) if KEYEXIST == error.code => Ok(inner),
            Err(error) => Err(error),
        }
    }
}
