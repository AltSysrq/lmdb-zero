// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Near-zero-cost, mostly-safe idiomatic bindings to LMDB.
//!
//! This crate provides an interface to LMDB which as much as possible is not
//! abstracted from the model LMDB itself provides, except as necessary to
//! integrate with the borrow checker. This means that you don't get easy
//! iterators, but also that you can do almost anything with LMDB through these
//! bindings as you can through C.
//!
//! # Example
//!
//! ```
//! extern crate lmdb_zero as lmdb;
//! extern crate tempdir;
//!
//! # fn main() {
//! #   let tmp = tempdir::TempDir::new_in(".", "lmdbzero").unwrap();
//! #   example(tmp.path().to_str().unwrap());
//! # }
//! #
//! fn example(path: &str) {
//!   // Create the environment, that is, the file containing the database(s).
//!   // This is unsafe because you need to ensure certain things about the
//!   // host environment that these bindings can't help you with.
//!   let env = unsafe {
//!     lmdb::EnvBuilder::new().unwrap().open(
//!       path, lmdb::open::Flags::empty(), 0o600).unwrap()
//!   };
//!   // Open the default database.
//!   let db = lmdb::Database::open(
//!     &env, None, &lmdb::DatabaseOptions::new(lmdb::db::Flags::empty()))
//!     .unwrap();
//!   {
//!     // Write some data in a transaction
//!     let txn = lmdb::WriteTransaction::new(&env).unwrap();
//!     // An accessor is used to control memory access.
//!     // NB You can only get the accessor from the transaction once.
//!     {
//!       let mut access = txn.access();
//!       access.put(&db, "Germany", "Berlin", lmdb::put::Flags::empty()).unwrap();
//!       access.put(&db, "France", "Paris", lmdb::put::Flags::empty()).unwrap();
//!       access.put(&db, "Latvia", "Rīga", lmdb::put::Flags::empty()).unwrap();
//!     }
//!     // Commit the changes so they are visible to later transactions
//!     txn.commit().unwrap();
//!   }
//!
//!   {
//!     // Now let's read the data back
//!     let txn = lmdb::ReadTransaction::new(&env).unwrap();
//!     let access = txn.access();
//!
//!     // Get the capital of Latvia. Note that the string is *not* copied; the
//!     // reference actually points into the database memory, and is valid
//!     // until the transaction is dropped or the accessor is mutated.
//!     let capital_of_latvia: &str = access.get(&db, "Latvia").unwrap();
//!     assert_eq!("Rīga", capital_of_latvia);
//!
//!     // We can also use cursors to move over the contents of the database.
//!     let mut cursor = txn.cursor(&db).unwrap();
//!     assert_eq!(("France", "Paris"), cursor.first(&access).unwrap());
//!     assert_eq!(("Germany", "Berlin"), cursor.next(&access).unwrap());
//!     assert_eq!(("Latvia", "Rīga"), cursor.next(&access).unwrap());
//!     assert!(cursor.next::<str,str>(&access).is_err());
//!   }
//! }
//! ```
//!
//! # Anatomy of this crate
//!
//! `Environment` is the top-level structure. It is created with an
//! `EnvBuilder`. An `Environment` is a single file (by default in a
//! subdirectory) which stores the actual data of all the databases it
//! contains. It corresponds to an `MDB_env` in the C API.
//!
//! A `Database` is a single table of key/value pairs within an environment.
//! Each environment has a single anonymous database, and may contain a number
//! of named databases. Note that if you want to use named databases, you need
//! to use `EnvBuilder::set_maxdbs` before creating the `Environment` to make
//! room for the handles. A database can only have one `Database` handle per
//! environment at a time.
//!
//! All accesses to the data within an environment are done through
//! transactions. For this, there are the `ReadTransaction` and
//! `WriteTransaction` structs. Both of these deref to a `ConstTransaction`,
//! which provides most of the read-only functionality and can be used for
//! writing code that can run within either type of transaction. Note that read
//! transactions are far cheaper than write transactions.
//!
//! `ReadTransaction`s can be reused by using `reset()` to turn them into
//! `ResetTransaction`s and then `refresh()` to turn them into fresh
//! `ReadTransaction`s.
//!
//! One unusual property of this crate are the `ConstAccessor` and
//! `WriteAccessor` structs, which are obtained once from a transaction and
//! used to perform actual data manipulation. These are needed to work with the
//! borrow checker: Cursors have a lifetime bound by their transaction and thus
//! borrow it, so we need something else to permit borrowing mutable data. The
//! accessors reflect this borrowing: Reading from the database requires an
//! immutable borrow of the accessor, while writing (which may invalidate
//! pointers) requires a mutable borrow of the accessor, thus causing the
//! borrow checker to ensure that all read accesses are disposed before any
//! write.
//!
//! Finally, the `Cursor` struct can be created from a transaction to permit
//! more flexible access to a database. Each `Cursor` corresponds to a
//! `MDB_cursor`. Accessing data through a cursor requires borrowing
//! appropriately from the accessor of the transaction owning the cursor.
//!
//! If you want to define your own types to store in the database, see the
//! `lmdb_zero::traits` submodule.
//!
//! # Major Differences from the LMDB C API
//!
//! Databases cannot be created or destroyed within a transaction due to the
//! awkward memory management semantics. For similar reasons, opening a
//! database more than once is not permitted (though note that LMDB doesn't
//! strictly allow this either --- it just silently returns an existing
//! handle).
//!
//! Access to data within the environment is guarded by transaction-specific
//! "accessors", which must be used in conjunction with the cursor or
//! transaction. This is how these bindings integrate with the borrow checker.
//!
//! APIs which obtain a reference to the owner of an object are not supported.
//!
//! Various APIs which radically change behaviour (including memory semantics)
//! in response to flags are separated into different calls which each express
//! their memory semantics clearly.
//!
//! # Non-Zero Cost
//!
//! There are three general areas where this wrapper adds non-zero-cost
//! abstractions:
//!
//! - Opening and closing databases adds locking overhead, since in LMDB it is
//!   unsynchronised. This shouldn't have much impact since one rarely opens
//!   and closes databases at a very high rate.
//!
//! - There is additional overhead in tracking what database handles are
//!   currently open so that attempts to reopen one can be prevented.
//!
//! - Cursors and transactions track their owners separately. Additionally,
//!   when two are used in conjunction, a runtime test is required to ensure
//!   that they actually can be used together. This means that the handle
//!   values are slightly larger and some function calls have an extra (very
//!   predictable) branch if the optimiser does not optimise the branch away
//!   entirely.
//!
//! # Using Zero-Copy
//!
//! This crate is primarily focussed on supporting zero-copy on all operations
//! where this is possible. The examples above demonstrate one aspect of this:
//! the `&str`s returned when querying for items are pointers into the database
//! itself, valid as long as the accessor is.
//!
//! The main traits to look at are `lmdb_zero::traits::AsLmdbBytes` and
//! `lmdb_zero::traits::FromLmdbBytes`, which are used to cast between byte
//! arrays and the types to be stored in the database.
//! `lmdb_zero::traits::FromReservedLmdbBytes` is used if you want to use the
//! `reserve` methods (in which you write the key only to the database and get
//! a pointer to a value to fill in after the fact). If you have a
//! `#[repr(C)]`, `Copy` struct, you can also use `lmdb_zero::traits::LmdbRaw`
//! if you just want to shove the raw struct itself into the database. All of
//! these have caveats which can be found on the struct documentation.
//!
//! Be aware that using zero-copy to save anything more interesting than byte
//! strings means your databases will not be portable to other architectures.
//! This mainly concerns byte-order, but types like `usize` whose size varies
//! by platform can also cause problems.
//!
//! # Notes on Memory Safety
//!
//! It is not possible to use lmdb-zero without at least one unsafe block,
//! because doing anything with a memory-mapped file requires making
//! assumptions about the host environment. Lmdb-zero is not in a position to
//! decide these assumptions, and so they are passed up to the caller.
//!
//! However, if these assumptions are met, it should be impossible to cause
//! memory unsafety (eg, aliasing mutable references; dangling pointers; buffer
//! under/overflows) by use of lmdb-zero's safe API.

#![deny(missing_docs)]

extern crate lmdb_sys as ffi;
extern crate libc;
#[macro_use] extern crate bitflags;

use std::cell::Cell;
use std::cmp::{Ord, Ordering};
use std::collections::HashSet;
use std::error::Error as StdError;
use std::ffi::*;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::result;
use std::slice;
use std::sync::Mutex;
use libc::{c_char, c_int, c_uint, c_void};

pub use ffi::mode_t as FileMode;
// XXX Supposedly this is redefined to a pointer on Windows, but the FFI
// bindings don't define the type and just use c_int inline.
pub use libc::c_int as Fd;

macro_rules! lmdb_call {
    ($x:expr) => { {
        let code = $x;
        if 0 != code {
            return Err(Error { code: code });
        }
    } }
}

/// Container module for the predefined LMDB error codes.
pub mod error {
    use libc::c_int;

    use ffi;

    /// A string path was given which contains a `NUL` byte.
    ///
    /// This is not a standard LMDB error code; it is produced by the FFI layer
    /// here when translating rust strings to C strings.
    pub const NULSTR: c_int = ffi::MDB_LAST_ERRCODE + 1;
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
    pub const BAD_DBI: c_int = ffi::MDB_BAD_DBI;
}

/// Flags used when opening an LMDB environment.
pub mod open {
    use libc;
    use ffi;

    bitflags! {
        /// Flags used when opening an LMDB environment.
        pub flags Flags: libc::c_uint {
            /// Use a fixed address for the mmap region. This flag must be
            /// specified when creating the environment, and is stored
            /// persistently in the environment. If successful, the memory map
            /// will always reside at the same virtual address and pointers
            /// used to reference data items in the database will be constant
            /// across multiple invocations. This option may not always work,
            /// depending on how the operating system has allocated memory to
            /// shared libraries and other uses. The feature is highly
            /// experimental.
            const FIXEDMAP = ffi::MDB_FIXEDMAP,
            /// By default, LMDB creates its environment in a directory whose
            /// pathname is given in path, and creates its data and lock files
            /// under that directory. With this option, the `path` passed to
            /// `EnvBuilder::open` is used as-is for the database main data
            /// file. The database lock file is the path with "-lock" appended.
            const NOSUBDIR = ffi::MDB_NOSUBDIR,
            /// Open the environment in read-only mode. No write operations
            /// will be allowed. LMDB will still modify the lock file - except
            /// on read-only filesystems, where LMDB does not use locks.
            const RDONLY = ffi::MDB_RDONLY,
            /// Use a writeable memory map unless `RDONLY` is set. This is
            /// faster and uses fewer mallocs, but loses protection from
            /// application bugs like wild pointer writes and other bad updates
            /// into the database. Incompatible with nested transactions. Do
            /// not mix processes with and without `WRITEMAP` on the same
            /// environment. This can defeat durability (`Environment::sync`
            /// etc).
            const WRITEMAP = ffi::MDB_WRITEMAP,
            /// Flush system buffers to disk only once per transaction, omit
            /// the metadata flush. Defer that until the system flushes files
            /// to disk, or next non-`RDONLY` commit or `Environment::sync()`.
            /// This optimization maintains database integrity, but a system
            /// crash may undo the last committed transaction. I.e. it
            /// preserves the ACI (atomicity, consistency, isolation) but not D
            /// (durability) database property. This flag may be changed at any
            /// time using `Environment::set_flags()`.
            const NOMETASYNC = ffi::MDB_NOMETASYNC,
            /// Don't flush system buffers to disk when committing a
            /// transaction. This optimization means a system crash can corrupt
            /// the database or lose the last transactions if buffers are not
            /// yet flushed to disk. The risk is governed by how often the
            /// system flushes dirty buffers to disk and how often
            /// `Environment::sync()` is called. However, if the filesystem
            /// preserves write order and the `WRITEMAP` flag is not used,
            /// transactions exhibit ACI (atomicity, consistency, isolation)
            /// properties and only lose D (durability). I.e. database
            /// integrity is maintained, but a system crash may undo the final
            /// transactions. Note that `(NOSYNC | WRITEMAP)` leaves the system
            /// with no hint for when to write transactions to disk, unless
            /// `Environment::sync()` is called. `(MAPASYNC | WRITEMAP)` may be
            /// preferable. This flag may be changed at any time using
            /// `Environment::set_flags()`.
            const NOSYNC = ffi::MDB_NOSYNC,
            /// When using `WRITEMAP`, use asynchronous flushes to disk. As
            /// with `NOSYNC`, a system crash can then corrupt the database or
            /// lose the last transactions. Calling `Environment::sync()`
            /// ensures on-disk database integrity until next commit. This flag
            /// may be changed at any time using `Environment::set_flags()`.
            const MAPASYNC = ffi::MDB_MAPASYNC,
            /// Don't use Thread-Local Storage. Tie reader locktable slots to
            /// transaction objects instead of to threads. I.e.
            /// `Transaction::reset()` keeps the slot reseved for the
            /// transaction object. A thread may use parallel read-only
            /// transactions. A read-only transaction may span threads if the
            /// user synchronizes its use. Applications that multiplex many
            /// user threads over individual OS threads need this option. Such
            /// an application must also serialize the write transactions in an
            /// OS thread, since LMDB's write locking is unaware of the user
            /// threads.
            const NOTLS = ffi::MDB_NOTLS,
            /// Don't do any locking. If concurrent access is anticipated, the
            /// caller must manage all concurrency itself. For proper operation
            /// the caller must enforce single-writer semantics, and must
            /// ensure that no readers are using old transactions while a
            /// writer is active. The simplest approach is to use an exclusive
            /// lock so that no readers may be active at all when a writer
            /// begins.
            const NOLOCK = ffi::MDB_NOLOCK,
            /// Turn off readahead. Most operating systems perform readahead on
            /// read requests by default. This option turns it off if the OS
            /// supports it. Turning it off may help random read performance
            /// when the DB is larger than RAM and system RAM is full. The
            /// option is not implemented on Windows.
            const NORDAHEAD = ffi::MDB_NORDAHEAD,
            /// Don't initialize malloc'd memory before writing to unused
            /// spaces in the data file. By default, memory for pages written
            /// to the data file is obtained using malloc. While these pages
            /// may be reused in subsequent transactions, freshly malloc'd
            /// pages will be initialized to zeroes before use. This avoids
            /// persisting leftover data from other code (that used the heap
            /// and subsequently freed the memory) into the data file. Note
            /// that many other system libraries may allocate and free memory
            /// from the heap for arbitrary uses. E.g., stdio may use the heap
            /// for file I/O buffers. This initialization step has a modest
            /// performance cost so some applications may want to disable it
            /// using this flag. This option can be a problem for applications
            /// which handle sensitive data like passwords, and it makes memory
            /// checkers like Valgrind noisy. This flag is not needed with
            /// `WRITEMAP`, which writes directly to the mmap instead of using
            /// malloc for pages. The initialization is also skipped if
            /// `RESERVE` is used; the caller is expected to overwrite all of
            /// the memory that was reserved in that case. This flag may be
            /// changed at any time using `Environment::set_flags()`.
            const NOMEMINIT = ffi::MDB_NOMEMINIT,
        }
    }
}

/// Flags used when copying an LMDB environment.
pub mod copy {
    use ffi;
    use libc;

    bitflags! {
        /// Flags used when copying an LMDB environment.
        pub flags Flags : libc::c_uint {
            /// Perform compaction while copying: omit free pages and sequentially
            /// renumber all pages in output. This option consumes more CPU and
            /// runs more slowly than the default.
            const COMPACT = ffi::MDB_CP_COMPACT,
        }
    }
}

/// Flags used when opening databases.
pub mod db {
    use ffi;
    use libc;

    bitflags! {
        /// Flags used when opening databases.
        pub flags Flags : libc::c_uint {
            /// Keys are strings to be compared in reverse order, from the end
            /// of the strings to the beginning. By default, Keys are treated
            /// as strings and compared from beginning to end.
            const REVERSEKEY = ffi::MDB_REVERSEKEY,
            /// Duplicate keys may be used in the database. (Or, from another
            /// perspective, keys may have multiple data items, stored in
            /// sorted order.) By default keys must be unique and may have only
            /// a single data item.
            const DUPSORT = ffi::MDB_DUPSORT,
            /// Keys are binary integers in native byte order, either
            /// `libc::c_uint` or `libc::size_t`, and will be sorted as such.
            /// The keys must all be of the same size.
            const INTEGERKEY = ffi::MDB_INTEGERKEY,
            /// This flag may only be used in combination with `DUPSORT`. This
            /// option tells the library that the data items for this database
            /// are all the same size, which allows further optimizations in
            /// storage and retrieval. When all data items are the same size,
            /// the `get_multiple` and `next_multiple` cursor operations may be
            /// used to retrieve multiple items at once.
            const DUPFIXED = ffi::MDB_DUPFIXED,
            /// This option specifies that duplicate data items are binary
            /// integers, similar to `INTEGERKEY` keys.
            const INTEGERDUP = ffi::MDB_INTEGERDUP,
            /// This option specifies that duplicate data items should be
            /// compared as strings in reverse order.
            const REVERSEDUP = ffi::MDB_REVERSEDUP,
            /// Create the named database if it doesn't exist. This option is
            /// not allowed in a read-only environment.
            const CREATE = ffi::MDB_CREATE,
        }
    }
}

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
        pub flags Flags : libc::c_uint {
            /// Enter the new key/data pair only if it does not already appear
            /// in the database. This flag may only be specified if the
            /// database was opened with `DUPSORT`. The function will return
            /// `KEYEXIST` if the key/data pair already appears in the
            /// database.
            const NODUPDATA = ffi::MDB_NODUPDATA,
            /// Enter the new key/data pair only if the key does not already
            /// appear in the database. The function will return `KEYEXIST` if
            /// the key already appears in the database, even if the database
            /// supports duplicates (`DUPSORT`). The data parameter will be set
            /// to point to the existing item.
            const NOOVERWRITE = ffi::MDB_NOOVERWRITE,
            /// Append the given key/data pair to the end of the database. This
            /// option allows fast bulk loading when keys are already known to
            /// be in the correct order. Loading unsorted keys with this flag
            /// will cause a `KEYEXIST` error.
            const APPEND = ffi::MDB_APPEND,
            /// As with `APPEND` above, but for sorted dup data.
            const APPENDDUP = ffi::MDB_APPENDDUP,
        }
    }
}

/// Flags used when deleting items.
mod del {
    use ffi;
    use libc;

    bitflags! {
        /// Flags used when deleting items.
        pub flags Flags : libc::c_uint {
            /// Delete all of the data items for the current key instead of
            /// just the current item. This flag may only be specified if the
            /// database was opened with `DUPSORT`.
            const NODUPDATA = ffi::MDB_NODUPDATA,
        }
    }
}

/// Module containing public traits.
///
/// This exists as a separate module solely so that it can be wildcard imported
/// where necessary.
pub mod traits {
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
}
use self::traits::*;

const EMPTY_VAL: ffi::MDB_val = ffi::MDB_val {
    mv_size: 0,
    mv_data: 0 as *mut c_void,
};

fn as_val<V : AsLmdbBytes + ?Sized>(v: &V) -> ffi::MDB_val {
    let bytes = v.as_lmdb_bytes();
    ffi::MDB_val {
        mv_size: bytes.len() as libc::size_t,
        mv_data: unsafe { mem::transmute(bytes.as_ptr()) },
    }
}

fn mdb_val_as_bytes<'a,O>(_o: &'a O, val: &ffi::MDB_val) -> &'a[u8] {
    unsafe {
        slice::from_raw_parts(
            mem::transmute(val.mv_data), val.mv_size as usize)
    }
}

fn from_val<'a, O, V : FromLmdbBytes + ?Sized>(
    _owner: &'a O, val: &ffi::MDB_val) -> Result<&'a V>
{
    let bytes = mdb_val_as_bytes(_owner, val);
    V::from_lmdb_bytes(bytes).ok_or(Error { code: error::VAL_REJECTED })
}

unsafe fn from_reserved<'a, O, V : FromReservedLmdbBytes>(
    _owner: &'a O, val: &ffi::MDB_val) -> &'a mut V
{
    let bytes = slice::from_raw_parts_mut(
        mem::transmute(val.mv_data), val.mv_size as usize);
    V::from_reserved_lmdb_bytes(bytes)
}

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
            if error::NULSTR == self.code {
                "NUL byte in path"
            } else if error::REOPENED == self.code {
                "Attempt to reopen database"
            } else if error::MISMATCH == self.code {
                "Items from different env/database used together"
            } else if error::VAL_REJECTED == self.code {
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
        Error { code: error::NULSTR }
    }
}

#[derive(Debug)]
struct EnvHandle(*mut ffi::MDB_env);

unsafe impl Sync for EnvHandle { }
unsafe impl Send for EnvHandle { }
impl Drop for EnvHandle {
    fn drop(&mut self) {
        unsafe {
            ffi::mdb_env_close(self.0)
        }
    }
}

#[derive(Debug)]
struct DbHandle<'a> {
    env: &'a Environment,
    dbi: ffi::MDB_dbi,
}

impl<'a> Drop for DbHandle<'a> {
    fn drop(&mut self) {
        self.env.dbi_close(self.dbi);
    }
}

#[derive(Debug)]
struct TxHandle(*mut ffi::MDB_txn);

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
    unsafe fn commit(&mut self) -> Result<()> {
        lmdb_call!(ffi::mdb_txn_commit(self.0));
        self.0 = ptr::null_mut();
        Ok(())
    }
}

/// Handle on an uninitialised LMDB environment to allow configuring pre-open
/// options.
#[derive(Debug)]
pub struct EnvBuilder {
    env: EnvHandle,
}

impl EnvBuilder {
    /// Allocates a new, uninitialised environment.
    pub fn new() -> Result<Self> {
        let mut env: *mut ffi::MDB_env = ptr::null_mut();
        unsafe {
            lmdb_call!(ffi::mdb_env_create(&mut env));
            Ok(EnvBuilder { env: EnvHandle(env) })
        }
    }

    /// Set the size of the memory map to use for this environment.
    ///
    /// The size should be a multiple of the OS page size. The default is
    /// 10485760 bytes. The size of the memory map is also the maximum size of
    /// the database. The value should be chosen as large as possible, to
    /// accommodate future growth of the database.
    ///
    /// The new size takes effect immediately for the current process but will
    /// not be persisted to any others until a write transaction has been
    /// committed by the current process. Also, only mapsize increases are
    /// persisted into the environment.
    ///
    /// See also `Environment::set_mapsize()`.
    pub fn set_mapsize(&mut self, size: usize) -> Result<()> {
        unsafe {
            lmdb_call!(ffi::mdb_env_set_mapsize(
                self.env.0, size as libc::size_t));
        }

        Ok(())
    }

    /// Set the maximum number of threads/reader slots for the environment.
    ///
    /// This defines the number of slots in the lock table that is used to
    /// track readers in the the environment. The default is 126. Starting a
    /// read-only transaction normally ties a lock table slot to the current
    /// thread until the environment closes or the thread exits. If `NOTLS` is
    /// in use, starting a transaction instead ties the slot to the transaction
    /// object until it or the `Environment` object is destroyed.
    pub fn set_maxreaders(&mut self, readers: u32) -> Result<()> {
        unsafe {
            lmdb_call!(ffi::mdb_env_set_maxreaders(
                self.env.0, readers as libc::c_uint));
        }

        Ok(())
    }

    /// Set the maximum number of named databases for the environment.
    ///
    /// This function is only needed if multiple databases will be used in the
    /// environment. Simpler applications that use the environment as a single
    /// unnamed database can ignore this option.
    ///
    /// Currently a moderate number of slots are cheap but a huge number gets
    /// expensive: 7-120 words per transaction, and every mdb_dbi_open() does a
    /// linear search of the opened slots.
    pub fn set_maxdbs(&mut self, dbs: u32) -> Result<()> {
        unsafe {
            lmdb_call!(ffi::mdb_env_set_maxdbs(
                self.env.0, dbs as libc::c_uint));
        }

        Ok(())
    }

    /// Opens the file or directory at `path` with the given `flags` and, on
    /// UNIX, permissions given by `mode`.
    ///
    /// `path` is a `&str` for convenience, and must be convertable to a
    /// `CString`. The non-use of `&OsStr` or `AsRef<Path>` as normally used in
    /// `std` is deliberate, since the path must be convertable to a byte
    /// string. But as a result there is no way to address files whose names
    /// are not valid UTF-8 through this call.
    ///
    /// ## Unsafety
    ///
    /// It is the caller's responsibility to ensure that the underlying file
    /// will be used properly. Since LMDB is built on memory-mapping, these
    /// responsibilities run quite deep and vary based on `flags`.
    ///
    /// - The caller must ensure that no other process writes to the file in
    ///   any way except going through LMDB. If this is violated, segfaults can
    ///   occur, or immutable references can be observed to have their referent
    ///   mutated asynchronously.
    ///
    /// - If the caller uses flags which suppress locking, the caller must
    ///   additionally ensure that LMDB's locking requirements are upheld.
    ///
    /// - If the caller uses flags that result in the creation of a sparse
    ///   file, the caller must ensure there is actually sufficient disk space
    ///   for all pages of the file or else a segfault may occur.
    pub unsafe fn open(self, path: &str, flags: open::Flags,
                       mode: FileMode) -> Result<Environment> {
        let path_cstr = try!(CString::new(path));
        lmdb_call!(ffi::mdb_env_open(
            self.env.0, path_cstr.as_ptr(), flags.bits(), mode));
        Ok(Environment {
            env: self.env,
            open_dbis: Mutex::new(HashSet::new()),
        })
    }
}

/// An LMDB environment which has been opened to a file.
#[derive(Debug)]
pub struct Environment {
    env: EnvHandle,
    // Track what DBIs are currently in use, so that an open() call that tries
    // to duplicate one fails.
    open_dbis: Mutex<HashSet<ffi::MDB_dbi>>,
}

/// Statistics information about an environment.
#[derive(Debug,Clone,Copy)]
pub struct Stat {
    /// Size of a database page. This is currently the same for all databases.
    pub psize: u32,
    /// Depth (height) of the B-tree
    pub depth: u32,
    /// Number of internal (non-leaf) pages
    pub branch_pages: usize,
    /// Number of leaf pages
    pub leaf_pages: usize,
    /// Number of overflow pages
    pub overflow_pages: usize,
    /// Number of data items
    pub entries: usize,
}

impl From<ffi::MDB_stat> for Stat {
    fn from(raw: ffi::MDB_stat) -> Stat {
        Stat {
            psize: raw.ms_psize as u32,
            depth: raw.ms_depth as u32,
            branch_pages: raw.ms_branch_pages as usize,
            leaf_pages: raw.ms_leaf_pages as usize,
            overflow_pages: raw.ms_overflow_pages as usize,
            entries: raw.ms_entries as usize,
        }
    }
}

/// Configuration information about an environment.
#[derive(Debug,Clone,Copy)]
pub struct EnvInfo {
    /// Address of map, if fixed
    pub mapaddr: *const c_void,
    /// Size of the data memory map
    pub mapsize: usize,
    /// ID of the last used page
    pub last_pgno: usize,
    /// ID of the last committed transaction
    pub last_txnid: usize,
    /// max reader slots in the environment
    pub maxreaders: u32,
    /// max reader slots used in the environment
    pub numreaders: u32,
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
#[derive(Debug)]
pub struct Database<'a> {
    db: DbHandle<'a>,
}

impl Environment {
    /// Copy an LMDB environment to the specified path, with options.
    ///
    /// This function may be used to make a backup of an existing environment.
    /// No lockfile is created, since it gets recreated at need.
    ///
    /// ## Note
    ///
    /// This call can trigger significant file size growth if run in parallel
    /// with write transactions, because it employs a read-only transaction.
    /// See long-lived transactions under Caveats.
    ///
    /// ## Example
    ///
    /// ```
    /// extern crate tempdir;
    /// extern crate lmdb_zero as lmdb;
    ///
    /// # fn main() { unsafe { example(&lmdb::EnvBuilder::new().unwrap().open(
    /// #    tempdir::TempDir::new_in(".", "lmdbzero")
    /// #      .unwrap().path().to_str().unwrap(),
    /// #    lmdb::open::Flags::empty(), 0o600).unwrap()); } }
    /// fn example(env: &lmdb::Environment) {
    ///   let out = tempdir::TempDir::new_in(".", "lmdbcopy").unwrap();
    ///   env.copy(out.path().to_str().unwrap(),
    ///            lmdb::copy::COMPACT).unwrap();
    ///   // We could now open up an independent environment in `lmdbcopyXXXX`
    ///   // or upload it somewhere, eg, while `env` could continue being
    ///   // modified concurrently.
    /// }
    /// ```
    pub fn copy(&self, path: &str, flags: copy::Flags) -> Result<()> {
        let path_cstr = try!(CString::new(path));
        unsafe {
            lmdb_call!(ffi::mdb_env_copy2(
                self.env.0, path_cstr.as_ptr(), flags.bits()));
        }
        Ok(())
    }

    /// Copy an LMDB environment to the specified file descriptor, with options.
    ///
    /// This function may be used to make a backup of an existing environment.
    /// No lockfile is created, since it gets recreated at need. See
    /// `copy()` for further details.
    ///
    /// ## Note
    ///
    /// This call can trigger significant file size growth if run in parallel
    /// with write transactions, because it employs a read-only transaction.
    /// See long-lived transactions under Caveats.
    pub fn copyfd(&self, fd: Fd, flags: copy::Flags) -> Result<()> {
        unsafe {
            lmdb_call!(ffi::mdb_env_copyfd2(self.env.0, fd, flags.bits()));
        }
        Ok(())
    }

    /// Return statistics about the LMDB environment.
    pub fn stat(&self) -> Result<Stat> {
        let raw = unsafe {
            let mut raw = mem::zeroed::<ffi::MDB_stat>();
            lmdb_call!(ffi::mdb_env_stat(self.env.0, &mut raw));
            raw
        };
        Ok(raw.into())
    }

    /// Return information about the LMDB environment.
    pub fn info(&self) -> Result<EnvInfo> {
        let raw = unsafe {
            let mut raw = mem::zeroed::<ffi::MDB_envinfo>();
            lmdb_call!(ffi::mdb_env_info(self.env.0, &mut raw));
            raw
        };
        Ok(EnvInfo {
            mapaddr: raw.me_mapaddr as *const c_void,
            mapsize: raw.me_mapsize as usize,
            last_pgno: raw.me_last_pgno as usize,
            last_txnid: raw.me_last_txnid as usize,
            maxreaders: raw.me_maxreaders as u32,
            numreaders: raw.me_numreaders as u32,
        })
    }

    /// Flush the data buffers to disk.
    ///
    /// Data is always written to disk when transactions are committed, but the
    /// operating system may keep it buffered. LMDB always flushes the OS
    /// buffers upon commit as well, unless the environment was opened with
    /// `NOSYNC` or in part `NOMETASYNC`. This call is not valid if the
    /// environment was opened with `RDONLY`.
    ///
    /// If `force` is true, force a synchronous flush. Otherwise if the
    /// environment has the `NOSYNC` flag set the flushes will be omitted, and
    /// with `MAPASYNC` they will be asynchronous.
    pub fn sync(&self, force: bool) -> Result<()> {
        unsafe {
            lmdb_call!(ffi::mdb_env_sync(self.env.0, force as c_int));
        }
        Ok(())
    }

    /// Set environment flags.
    ///
    /// This may be used to set some flags in addition to those from
    /// `EnvBuilder::open()`, or to unset these flags. If several threads
    /// change the flags at the same time, the result is undefined.
    ///
    /// `flags` specifies the flags to edit, not the new status of all flags.
    /// If `onoff` is true, all flags in `flags` are set; otherwise, all flags
    /// in `flags` are cleared.
    ///
    /// ## Unsafety
    ///
    /// The caller must ensure that multiple threads do not call this
    /// concurrently with itself or with `get_flags()`. This cannot be
    /// accomplished by using `&mut self`, since any open databases necessarily
    /// have the environment borrowed already.
    pub unsafe fn set_flags(&self, flags: open::Flags,
                            onoff: bool) -> Result<()> {
        lmdb_call!(ffi::mdb_env_set_flags(
            self.env.0, flags.bits(), onoff as c_int));
        Ok(())
    }

    /// Get environment flags.
    pub fn flags(&self) -> Result<open::Flags> {
        let mut raw: c_uint = 0;
        unsafe {
            lmdb_call!(ffi::mdb_env_get_flags(self.env.0, &mut raw));
        }
        Ok(open::Flags::from_bits_truncate(raw))
    }

    /// Return the path that was used in `EnvBuilder::open()`.
    ///
    /// ## Panics
    ///
    /// Panics if LMDB returns success but sets the path to a NULL pointer.
    pub fn path(&self) -> Result<&CStr> {
        let mut raw: *const c_char = ptr::null();
        unsafe {
            lmdb_call!(ffi::mdb_env_get_path(self.env.0, &mut raw));
            if raw.is_null() {
                panic!("mdb_env_get_path() returned NULL pointer");
            }
            Ok(CStr::from_ptr(raw))
        }
    }

    /// Return the filedescriptor for the given environment.
    ///
    /// ## Unsafety
    ///
    /// The caller must ensure that the file descriptor is not used to subvert
    /// normal LMDB functionality, such as by writing to it or closing it.
    pub unsafe fn fd(&self) -> Result<Fd> {
        let mut raw: Fd = 0;
        lmdb_call!(ffi::mdb_env_get_fd(self.env.0, &mut raw));
        Ok(raw)
    }

    /// Set the size of the memory map to use for this environment.
    ///
    /// The size should be a multiple of the OS page size. The default is
    /// 10485760 bytes. The size of the memory map is also the maximum size of
    /// the database. The value should be chosen as large as possible, to
    /// accommodate future growth of the database.
    ///
    /// The new size takes effect immediately for the current process but will
    /// not be persisted to any others until a write transaction has been
    /// committed by the current process. Also, only mapsize increases are
    /// persisted into the environment.
    ///
    /// If the mapsize is increased by another process, and data has grown
    /// beyond the range of the current mapsize, starting a transaction will
    /// return `error::MAP_RESIZED`. This function may be called with a size of
    /// zero to adopt the new size.
    ///
    /// ## Unsafety
    ///
    /// This may only be called if no transactions are active in the current
    /// process. Note that the library does not check for this condition, the
    /// caller must ensure it explicitly.
    pub unsafe fn set_mapsize(&self, size: usize) -> Result<()> {
        lmdb_call!(ffi::mdb_env_set_mapsize(self.env.0, size));
        Ok(())
    }

    /// Get the maximum number of threads/reader slots for the environment.
    pub fn maxreaders(&self) -> Result<u32> {
        let mut raw: c_uint = 0;
        unsafe {
            lmdb_call!(ffi::mdb_env_get_maxreaders(self.env.0, &mut raw));
        }
        Ok(raw as u32)
    }

    /// Get the maximum size of keys and `DUPSORT` data we can write.
    ///
    /// Depends on the compile-time constant `MDB_MAXKEYSIZE` in LMDB. Default
    /// 511.
    pub fn maxkeysize(&self) -> u32 {
        unsafe {
            ffi::mdb_env_get_maxkeysize(self.env.0) as u32
        }
    }

    /// Check for stale entries in the reader lock table.
    ///
    /// Returns the number of stale slots that were cleared.
    pub fn reader_check(&self) -> Result<i32> {
        let mut raw: c_int = 0;
        unsafe {
            lmdb_call!(ffi::mdb_reader_check(self.env.0, &mut raw));
        }
        Ok(raw as i32)
    }

    fn dbi_close(&self, dbi: ffi::MDB_dbi) {
        // Hold the lock through the end of the function to also guard the
        // LMDB's unsynchronised DBI table.
        let mut locked_dbis = self.open_dbis.lock()
            .expect("open_dbis lock poisoned");
        assert!(locked_dbis.remove(&dbi),
                "closed dbi that wasn't open");

        unsafe {
            ffi::mdb_dbi_close(self.env.0, dbi);
        }
    }

    fn dbi_delete(&self, dbh: DbHandle) -> Result<()> {
        let dbi = dbh.dbi;

        // Hold the lock across the call to `mdb_drop()` to also guard its
        // unsynchronised DBI table.
        let mut locked_dbis = self.open_dbis.lock()
            .expect("open_dbis lock poisoned");
        unsafe {
            let mut raw_txn: *mut ffi::MDB_txn = ptr::null_mut();
            lmdb_call!(ffi::mdb_txn_begin(
                self.env.0, ptr::null_mut(), 0, &mut raw_txn));
            let mut txn = TxHandle(raw_txn);
            lmdb_call!(ffi::mdb_drop(raw_txn, dbi, 1 /* delete */));
            // Prevent the RAII wrapper from trying to close the handle again
            mem::forget(dbi);
            try!(txn.commit());
        }
        assert!(locked_dbis.remove(&dbi),
                "closed dbi that wasn't open");
        Ok(())
    }
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
    /// ## Unsafety
    ///
    /// Behaviour is undefined if the `FromLmdbBytes` or `Ord` implementation
    /// panics.
    pub unsafe fn sort_keys_as<K : FromLmdbBytes + Ord + ?Sized>(&mut self) {
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
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if the `FromLmdbBytes` or `Ord` implementation
    /// panics.
    pub unsafe fn sort_values_as<V : FromLmdbBytes + Ord + ?Sized>(&mut self) {
        self.val_cmp = Some(DatabaseOptions::entry_cmp_as::<V>);
    }

    extern fn entry_cmp_as<V : FromLmdbBytes + Ord + ?Sized>(
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
    /// do so will result in the `REOPENED` error.
    pub fn open(env: &'a Environment, name: Option<&str>,
                options: &DatabaseOptions)
                -> Result<Database<'a>> {
        let mut raw: ffi::MDB_dbi = 0;
        let name_cstr = match name {
            None => None,
            Some(s) => Some(try!(CString::new(s))),
        };
        let raw = unsafe {
            // Locking the hash set here is also used to serialise calls to
            // `mdb_dbi_open()`, which are not permitted to be concurrent.
            let mut locked_dbis = env.open_dbis.lock()
                .expect("open_dbis lock poisoned");

            let mut raw_tx: *mut ffi::MDB_txn = ptr::null_mut();
            lmdb_call!(ffi::mdb_txn_begin(
                env.env.0, ptr::null_mut(), 0, &mut raw_tx));
            let mut wrapped_tx = TxHandle(raw_tx); // For auto-closing etc
            lmdb_call!(ffi::mdb_dbi_open(
                raw_tx, name_cstr.map_or(ptr::null(), |s| s.as_ptr()),
                options.flags.bits(), &mut raw));

            if !locked_dbis.insert(raw) {
                return Err(Error { code: error::REOPENED });
            }

            if let Some(fun) = options.key_cmp {
                lmdb_call!(ffi::mdb_set_compare(
                    // XXX lmdb_sys's declaration of this function is incorrect
                    // due to the `MDB_cmp_func` typedef (which is a bare
                    // function in C) being translated as a pointer.
                    raw_tx, raw, mem::transmute(fun)));
            }
            if let Some(fun) = options.val_cmp {
                lmdb_call!(ffi::mdb_set_dupsort(
                    // XXX see above
                    raw_tx, raw, mem::transmute(fun)));
            }

            try!(wrapped_tx.commit());
            raw
        };

        Ok(Database {
            db: DbHandle {
                env: env,
                dbi: raw,
            }
        })
    }

    /// Deletes this database.
    ///
    /// This call implicitly creates a new write transaction to perform the
    /// operation, so that the lifetime of the database handle does not depend
    /// on the outcome. The database handle is closed implicitly by this
    /// operation.
    pub fn delete(self) -> Result<()> {
        self.db.env.dbi_delete(self.db)
    }

    fn assert_same_env(&self, other_env: &Environment)
                       -> Result<()> {
        if self.db.env as *const Environment !=
            other_env as *const Environment
        {
            Err(Error { code: error::MISMATCH })
        } else {
            Ok(())
        }
    }

    fn dbi(&self) -> ffi::MDB_dbi {
        self.db.dbi
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
#[derive(Debug)]
pub struct ConstTransaction<'env> {
    env: &'env Environment,
    tx: TxHandle,
    has_yielded_accessor: Cell<bool>,
}

/// A read-only LMDB transaction.
///
/// In addition to all operations valid on `ConstTransaction`, a
/// `ReadTransaction` can additionally operate on cursors with a lifetime
/// scoped to the environment instead of the transaction.
#[derive(Debug)]
pub struct ReadTransaction<'env>(ConstTransaction<'env>);
/// A read-write LMDB transaction.
///
/// In addition to all operations valid on `ConstTransaction`, it is also
/// possible to perform writes to the underlying databases.
#[derive(Debug)]
pub struct WriteTransaction<'env>(ConstTransaction<'env>);

/// A read-only LMDB transaction that has been reset.
///
/// It can be renewed by calling `ResetTransaction::renew()`.
#[derive(Debug)]
pub struct ResetTransaction<'env>(ReadTransaction<'env>);

/// A read-only data accessor obtained from a `ConstTransaction`.
///
/// There is no corresponding `ReadAccessor`, since there are no additional
/// operations one can do with a known-read-only accessor.
#[derive(Debug)]
pub struct ConstAccessor<'txn>(&'txn ConstTransaction<'txn>);
/// A read-write data accessor obtained from a `WriteTransaction`.
///
/// All operations that can be performed on `ConstAccessor` can also be
/// performed on `WriteAccessor`.
#[derive(Debug)]
pub struct WriteAccessor<'txn>(ConstAccessor<'txn>);

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

impl<'env> ConstTransaction<'env> {
    fn new(env: &'env Environment,
           parent: Option<&'env mut ConstTransaction<'env>>,
           flags: c_uint) -> Result<Self> {
        let mut rawtx: *mut ffi::MDB_txn = ptr::null_mut();
        unsafe {
            lmdb_call!(ffi::mdb_txn_begin(
                env.env.0, parent.map_or(
                    ptr::null_mut(), |p| p.tx.0),
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
    /// ## Panics
    ///
    /// Panics if this function has already been called on this transaction.
    pub fn access(&self) -> ConstAccessor {
        assert!(!self.has_yielded_accessor.get(),
                "Transaction accessor already returned");
        self.has_yielded_accessor.set(false);
        ConstAccessor(self)
    }

    /// Creates a new cursor scoped to this transaction, bound to the given
    /// database.
    pub fn cursor<'txn, 'db>(&'txn self, db: &'db Database)
                             -> Result<Cursor<'txn,'db>> {
        try!(db.assert_same_env(self.env));

        let mut raw: *mut ffi::MDB_cursor = ptr::null_mut();
        unsafe {
            lmdb_call!(ffi::mdb_cursor_open(self.tx.0, db.dbi(), &mut raw));
        }

        Ok(Cursor {
            cursor: CursorHandle(raw),
            txn: self,
            _db: PhantomData
        })
    }

    /// Returns the internal id of this transaction.
    pub fn id(&self) -> usize {
        unsafe {
            ffi::mdb_txn_id(self.tx.0)
        }
    }

    /// Retrieves statistics for a database.
    pub fn db_stat(&self, db: &Database) -> Result<Stat> {
        try!(db.assert_same_env(self.env));

        unsafe {
            let mut raw: ffi::MDB_stat = mem::zeroed();
            lmdb_call!(ffi::mdb_stat(self.tx.0, db.dbi(), &mut raw));
            Ok(raw.into())
        }
    }

    /// Retrieve the DB flags for a database handle.
    pub fn db_flags(&self, db: &Database) -> Result<db::Flags> {
        try!(db.assert_same_env(self.env));

        let mut raw: c_uint = 0;
        unsafe {
            lmdb_call!(ffi::mdb_dbi_flags(self.tx.0, db.dbi(), &mut raw));
        }
        Ok(db::Flags::from_bits_truncate(raw))
    }

    fn assert_sensible_cursor<'a>(&self, cursor: &Cursor<'env,'a>)
                                  -> Result<()> {
        if self as *const ConstTransaction<'env> !=
            cursor.txn as *const ConstTransaction<'env>
        {
            Err(Error { code: error::MISMATCH })
        } else {
            Ok(())
        }
    }
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
    pub fn new(env: &'env Environment) -> Result<Self> {
        Ok(ReadTransaction(try!(ConstTransaction::new(
            env, None, ffi::MDB_RDONLY))))
    }

    /// Opens a new, read-only transaction as a child transaction of the given
    /// parent. While the new transaction exists, no operations may be
    /// performed on the parent or any of its cursors. (These bindings are
    /// actually stricter, and do not permit cursors or other references into
    /// the parent to coexist with the child transaction.)
    ///
    /// ## Note
    ///
    /// A transaction and its cursors must only be used by a single thread
    /// (enforced by the rust compiler).
    pub fn new_child(parent: &'env mut ConstTransaction<'env>)
                     -> Result<Self> {
        Ok(ReadTransaction(try!(ConstTransaction::new(
            parent.env, Some(parent), ffi::MDB_RDONLY))))
    }

    /// Dissociates the given cursor from this transaction and its database,
    /// returning a `StaleCursor` which can be reused later.
    ///
    /// This only fails if `cursor` does not belong to this transaction.
    pub fn dissoc_cursor<'txn,'db>(&self, cursor: Cursor<'txn,'db>)
                                   -> Result<StaleCursor<'db>>
    where 'env: 'db {
        try!(self.assert_sensible_cursor(&cursor));
        Ok(StaleCursor {
            cursor: cursor.cursor,
            env: self.env,
            _db: PhantomData,
        })
    }

    /// Associates a saved read-only with this transaction.
    ///
    /// The cursor will be rebound to this transaction, but will continue using
    /// the same database that it was previously.
    pub fn assoc_cursor<'txn,'db>(&'txn self, cursor: StaleCursor<'db>)
                                  -> Result<Cursor<'txn,'db>> {
        if self.env as *const Environment != cursor.env as *const Environment {
            return Err(Error { code: error::MISMATCH });
        }

        unsafe {
            lmdb_call!(ffi::mdb_cursor_renew(self.tx.0, cursor.cursor.0));
        }
        Ok(Cursor {
            cursor: cursor.cursor,
            txn: self,
            _db: PhantomData,
        })
    }

    /// Resets this transaction, releasing most of its resources but allowing
    /// it to be quickly renewed if desired.
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
        self.0.has_yielded_accessor.set(false);
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
    pub fn new(env: &'env Environment) -> Result<Self> {
        Ok(WriteTransaction(try!(ConstTransaction::new(env, None, 0))))
    }

    /// Opens a new, read-write transaction as a child transaction of the given
    /// parent. While the new transaction exists, no operations may be
    /// performed on the parent or any of its cursors. (These bindings are
    /// actually stricter, and do not permit cursors or other references into
    /// the parent to coexist with the child transaction.)
    ///
    /// ## Note
    ///
    /// A transaction and its cursors must only be used by a single thread
    /// (enforced by the rust compiler).
    pub fn new_child(parent: &'env mut WriteTransaction<'env>)
                     -> Result<Self> {
        let env = parent.0.env;
        Ok(WriteTransaction(try!(ConstTransaction::new(
            env, Some(&mut*parent), 0))))
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
    /// Panics if called more than once on the same transaction.
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
    pub fn get<K : AsLmdbBytes + ?Sized, V : FromLmdbBytes + ?Sized>(
        &self, db: &Database, key: &K) -> Result<&V>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        unsafe {
            lmdb_call!(ffi::mdb_get(
                self.txptr(), db.dbi(), &mut mv_key, &mut out_val));
        }

        from_val(self, &out_val)
    }

    fn txptr(&self) -> *mut ffi::MDB_txn {
        self.0.tx.0
    }

    fn env(&self) -> &Environment {
        self.0.env
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
    pub fn put<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K, value: &V,
        flags: put::Flags) -> Result<()>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut mv_val = as_val(value);
        unsafe {
            lmdb_call!(ffi::mdb_put(
                self.txptr(), db.dbi(), &mut mv_key, &mut mv_val,
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
    pub fn put_reserve<K : AsLmdbBytes + ?Sized,
                       V : FromReservedLmdbBytes + Sized>(
        &mut self, db: &Database, key: &K, flags: put::Flags) -> Result<&mut V>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        out_val.mv_size = mem::size_of::<V>();
        unsafe {
            lmdb_call!(ffi::mdb_put(
                self.txptr(), db.dbi(), &mut mv_key, &mut out_val,
                flags.bits() | ffi::MDB_RESERVE));
        }

        unsafe {
            Ok(from_reserved(self, &out_val))
        }
    }

    /// Delete items from a database by key.
    ///
    /// This function removes key/data pairs from the database. All values
    /// whose key matches `key` are deleted, including in the case of
    /// `DUPSORT`. This function will return `NOTFOUND` if the specified
    /// key is not in the database.
    pub fn del_key<K : AsLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K) -> Result<()>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        unsafe {
            lmdb_call!(ffi::mdb_del(
                self.txptr(), db.dbi(), &mut mv_key, ptr::null_mut()));
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
    pub fn del_item<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>(
        &mut self, db: &Database, key: &K, val: &V) -> Result<()>
    {
        try!(db.assert_same_env(self.env()));

        let mut mv_key = as_val(key);
        let mut mv_val = as_val(val);
        unsafe {
            lmdb_call!(ffi::mdb_del(
                self.txptr(), db.dbi(), &mut mv_key, &mut mv_val));
        }

        Ok(())
    }

    /// Completely clears the content of the given database.
    pub fn clear_db(&mut self, db: &Database) -> Result<()> {
        try!(db.assert_same_env(self.env()));
        unsafe {
            lmdb_call!(ffi::mdb_drop(self.txptr(), db.dbi(), 0));
        }
        Ok(())
    }
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

impl<'txn,'db> Cursor<'txn,'db> {
    fn get_0_kv<'access, K : FromLmdbBytes + ?Sized,
                V : FromLmdbBytes + ?Sized>
        (&mut self, access: &'access ConstAccessor,
         op: c_uint) -> Result<(&'access K, &'access V)>
    {
        try!(access.0.assert_sensible_cursor(self));

        let mut out_key = EMPTY_VAL;
        let mut out_val = EMPTY_VAL;
        unsafe {
            lmdb_call!(ffi::mdb_cursor_get(
                self.cursor.0, &mut out_key, &mut out_val, op));
        }

        Ok((try!(from_val(access, &out_key)),
            try!(from_val(access, &out_val))))
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
        try!(access.0.assert_sensible_cursor(self));

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
        try!(access.0.assert_sensible_cursor(self));

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
        try!(access.0.assert_sensible_cursor(self));

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
        fn first, ffi::MDB_FIRST
    }

    cursor_get_0_kv! {
        /// Positions the cursor at the first key/value pair whose key is equal
        /// to the current key.
        ///
        /// This only makes sense on `DUPSORT` databases.
        ///
        /// This correspnods to the `mdb_cursor_get` function with the
        /// `MDB_FIRST_DUP` operation.
        fn first_dup, ffi::MDB_FIRST_DUP
    }

    /// Positions the cursor at the given (key,value) pair.
    ///
    /// This only makes sense on `DUPSORT` databases.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the
    /// `MDB_GET_BOTH` operation.
    pub fn seek_kv<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, key: &K, val: &V) -> Result<()>
    {
        self.get_kv_0(key, val, ffi::MDB_GET_BOTH)
    }

    /// Positions the cursor at the given key and the "nearest" value to `val`.
    ///
    /// The actual value found is returned.
    ///
    /// This only makes sense on `DUPSORT` databases.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the
    /// `MDB_GET_BOTH_RANGE` operation.
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
        fn get_current, ffi::MDB_GET_CURRENT
    }

    cursor_get_0_kv! {
        /// Returns the current key and as many items as possible with that key
        /// from the current cursor position.
        ///
        /// The cursor is advanced so that `next_multiple()` returns the next
        /// group of items, if any.
        ///
        /// The easiest way to use this is for `V` to be a slice of `LmdbRaw`
        /// types.
        ///
        /// This only makes sense on `DUPSORT` databases.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_GET_MULTIPLE` operation.
        fn get_multiple, ffi::MDB_GET_MULTIPLE
    }

    cursor_get_0_kv! {
        /// Continues fetching items from a cursor positioned by a call to
        /// `get_multiple()`.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_NEXT_MULTIPLE` operation.
        fn next_multiple, ffi::MDB_NEXT_MULTIPLE
    }

    cursor_get_0_kv! {
        /// Positions the cursor at the last key/value pair in the database,
        /// and returns that pair.
        ///
        /// This corresponds to the `mdb_cursor_get` function with the
        /// `MDB_LAST` operation.
        fn last, ffi::MDB_LAST
    }

    cursor_get_0_kv! {
        /// Positions the cursor at the last key/value pair whose key is equal
        /// to the current key.
        ///
        /// This only makes sense on `DUPSORT` databases.
        ///
        /// This correspnods to the `mdb_cursor_get` function with the
        /// `MDB_LAST_DUP` operation.
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
        fn nxt_dup, ffi::MDB_NEXT_DUP
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
        fn prev_nodup, ffi::MDB_PREV_NODUP
    }

    /// Positions the cursor at the first item of the given key.
    ///
    /// Returns the value of that item.
    ///
    /// This corresponds to the `mdb_cursor_get` function with the `MDB_SET`
    /// operation.
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
    pub fn put<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, access: &mut WriteAccessor,
         key: &K, val: &V, flags: put::Flags) -> Result<()>
    {
        try!((access.0).0.assert_sensible_cursor(self));

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
    pub fn overwrite<K : AsLmdbBytes + ?Sized, V : AsLmdbBytes + ?Sized>
        (&mut self, access: &mut WriteAccessor,
         key: &K, val: &V, flags: put::Flags) -> Result<()>
    {
        try!((access.0).0.assert_sensible_cursor(self));

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
    /// This cannot be used on a `DUPSORT` database.
    ///
    /// The cursor is positioned at the new item, or on failure usually near
    /// it.
    pub fn reserve<'access, K : AsLmdbBytes + ?Sized, V : FromReservedLmdbBytes>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, flags: put::Flags) -> Result<&'access mut V>
    {
        try!((access.0).0.assert_sensible_cursor(self));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        out_val.mv_size = mem::size_of::<V>();

        unsafe {
            lmdb_call!(ffi::mdb_cursor_put(
                self.cursor.0, &mut mv_key, &mut out_val,
                flags.bits() | ffi::MDB_RESERVE));

            Ok(from_reserved(access, &out_val))
        }
    }

    /// Returns a writable reference to the value belonging to the given key in
    /// the database.
    ///
    /// This has all the caveats of both `overwrite()` and `reserve()`.
    pub fn overwrite_in_place<'access, K : AsLmdbBytes + ?Sized,
                              V : FromReservedLmdbBytes>
        (&mut self, access: &'access mut WriteAccessor,
         key: &K, flags: put::Flags) -> Result<&'access mut V>
    {
        try!((access.0).0.assert_sensible_cursor(self));

        let mut mv_key = as_val(key);
        let mut out_val = EMPTY_VAL;
        out_val.mv_size = mem::size_of::<V>();

        unsafe {
            lmdb_call!(ffi::mdb_cursor_put(
                self.cursor.0, &mut mv_key, &mut out_val,
                flags.bits() | ffi::MDB_RESERVE | ffi::MDB_CURRENT));

            Ok(from_reserved(access, &out_val))
        }
    }

    /// Stores multiple data elements with the same key in a single request.
    ///
    /// This is only permitted for `DUPFIXED` databases.
    ///
    /// Note that `values` must be a slice of `LmdbRaw`, since this function
    /// needs to know the exact size of each individual item and must be able
    /// to directly reinterpret the slice as a byte array.
    ///
    /// On success, returns the number of items that were actually inserted.
    pub fn put_multiple<K : AsLmdbBytes + ?Sized, V : LmdbRaw>
        (&mut self, access: &mut WriteAccessor,
         key: &K, values: &[V], flags: put::Flags)
         -> Result<usize>
    {
        try!((access.0).0.assert_sensible_cursor(self));

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
                self.cursor.0, &mut mv_key, &mut mv_vals[0],
                flags.bits() | ffi::MDB_MULTIPLE));
        }

        Ok(mv_vals[1].mv_size as usize)
    }

    /// Delete current key/value pair.
    ///
    /// By default, this deletes only the current pair. `flags` can be set to
    /// `NODUPDATA` for `DUPDATA` databases to delete everything with the
    /// current key.
    pub fn delete(&mut self, access: &mut WriteAccessor,
                  flags: del::Flags) -> Result<()> {
        try!((access.0).0.assert_sensible_cursor(self));

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
