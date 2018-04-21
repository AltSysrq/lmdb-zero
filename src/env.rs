// Copyright 2016 FullContact, Inc
// Copyright 2017, 2018 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::HashSet;
use std::ffi::{CStr, CString};
use std::mem;
use std::ptr;
use std::sync::Mutex;
use libc::{self, c_char, c_int, c_uint, c_void};

use ffi;
use ffi2;
use tx::TxHandle;
use ::{Fd, FileMode, Result};

/// Flags used when opening an LMDB environment.
pub mod open {
    use libc;
    use ffi;

    bitflags! {
        /// Flags used when opening an LMDB environment.
        pub struct Flags : libc::c_uint {
            /// Use a fixed address for the mmap region. This flag must be
            /// specified when creating the environment, and is stored
            /// persistently in the environment. If successful, the memory map
            /// will always reside at the same virtual address and pointers
            /// used to reference data items in the database will be constant
            /// across multiple invocations. This option may not always work,
            /// depending on how the operating system has allocated memory to
            /// shared libraries and other uses. The feature is highly
            /// experimental.
            const FIXEDMAP = ffi::MDB_FIXEDMAP;
            /// By default, LMDB creates its environment in a directory whose
            /// pathname is given in path, and creates its data and lock files
            /// under that directory. With this option, the `path` passed to
            /// `EnvBuilder::open` is used as-is for the database main data
            /// file. The database lock file is the path with "-lock" appended.
            const NOSUBDIR = ffi::MDB_NOSUBDIR;
            /// Open the environment in read-only mode. No write operations
            /// will be allowed. LMDB will still modify the lock file - except
            /// on read-only filesystems, where LMDB does not use locks.
            const RDONLY = ffi::MDB_RDONLY;
            /// Use a writeable memory map unless `RDONLY` is set. This is
            /// faster and uses fewer mallocs, but loses protection from
            /// application bugs like wild pointer writes and other bad updates
            /// into the database. Incompatible with nested transactions. Do
            /// not mix processes with and without `WRITEMAP` on the same
            /// environment. This can defeat durability (`Environment::sync`
            /// etc).
            const WRITEMAP = ffi::MDB_WRITEMAP;
            /// Flush system buffers to disk only once per transaction, omit
            /// the metadata flush. Defer that until the system flushes files
            /// to disk, or next non-`RDONLY` commit or `Environment::sync()`.
            /// This optimization maintains database integrity, but a system
            /// crash may undo the last committed transaction. I.e. it
            /// preserves the ACI (atomicity, consistency, isolation) but not D
            /// (durability) database property. This flag may be changed at any
            /// time using `Environment::set_flags()`.
            const NOMETASYNC = ffi::MDB_NOMETASYNC;
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
            const NOSYNC = ffi::MDB_NOSYNC;
            /// When using `WRITEMAP`, use asynchronous flushes to disk. As
            /// with `NOSYNC`, a system crash can then corrupt the database or
            /// lose the last transactions. Calling `Environment::sync()`
            /// ensures on-disk database integrity until next commit. This flag
            /// may be changed at any time using `Environment::set_flags()`.
            const MAPASYNC = ffi::MDB_MAPASYNC;
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
            const NOTLS = ffi::MDB_NOTLS;
            /// Don't do any locking. If concurrent access is anticipated, the
            /// caller must manage all concurrency itself. For proper operation
            /// the caller must enforce single-writer semantics, and must
            /// ensure that no readers are using old transactions while a
            /// writer is active. The simplest approach is to use an exclusive
            /// lock so that no readers may be active at all when a writer
            /// begins.
            const NOLOCK = ffi::MDB_NOLOCK;
            /// Turn off readahead. Most operating systems perform readahead on
            /// read requests by default. This option turns it off if the OS
            /// supports it. Turning it off may help random read performance
            /// when the DB is larger than RAM and system RAM is full. The
            /// option is not implemented on Windows.
            const NORDAHEAD = ffi::MDB_NORDAHEAD;
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
            const NOMEMINIT = ffi::MDB_NOMEMINIT;
        }
    }
}

/// Flags used when copying an LMDB environment.
pub mod copy {
    use ffi2;
    use libc;

    bitflags! {
        /// Flags used when copying an LMDB environment.
        pub struct Flags : libc::c_uint {
            /// Perform compaction while copying: omit free pages and sequentially
            /// renumber all pages in output. This option consumes more CPU and
            /// runs more slowly than the default.
            const COMPACT = ffi2::MDB_CP_COMPACT;
        }
    }
}

#[derive(Debug)]
struct EnvHandle(*mut ffi::MDB_env, bool);

unsafe impl Sync for EnvHandle { }
unsafe impl Send for EnvHandle { }
impl Drop for EnvHandle {
    fn drop(&mut self) {
        if self.1 {
            unsafe {
                ffi::mdb_env_close(self.0)
            }
        }
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
            Ok(EnvBuilder { env: EnvHandle(env, true) })
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

impl Environment {
    /// Wrap a raw LMDB environment handle in an `Environment`.
    ///
    /// The `Environment` assumes ownership of the `MDB_env`. If you do not
    /// want this, see [`borrow_raw()`](#method.borrow_raw) instead.
    ///
    /// ## Unsafety
    ///
    /// `env` must point to a valid `MDB_env`.
    ///
    /// It is the caller's responsibility to ensure that nothing destroys the
    /// `MDB_env` before [`into_raw()`](#method.into_raw) is called, and that
    /// nothing attempts to use the `MDB_env` after `Environment` is dropped
    /// normally.
    ///
    /// It is safe for multiple `Environment`s bound to the same `MDB_env` to
    /// coexist (though the others would need to be created by `borrow_raw`).
    /// However, care must be taken when using databases since by default the
    /// `Environment` will assume ownership of those as well.
    pub unsafe fn from_raw(env: *mut ffi::MDB_env) -> Self {
        Environment {
            env: EnvHandle(env, true),
            open_dbis: Mutex::new(HashSet::new()),
        }
    }

    /// Wrap a raw LMDB environment handle in an `Environment` without taking
    /// ownership.
    ///
    /// The `Environment` does not assume ownership of the `MDB_env`, and will
    /// not destroy it when it is dropped. See [`from_raw()`](#method.from_raw)
    /// if taking ownership is desired.
    ///
    /// Note that this does not affect assumed ownership of `MDB_dbi` handles;
    /// databases opened by `Database::open` are still presumed owned.
    ///
    /// ## Unsafety
    ///
    /// `env` must point to a valid `MDB_env`.
    ///
    /// It is safe for multiple `Environment`s bound to the same `MDB_env` to
    /// coexist (though the others would need to be created by `borrow_raw`).
    /// However, care must be taken when using databases since by default the
    /// `Environment` will assume ownership of those as well.
    pub unsafe fn borrow_raw(env: *mut ffi::MDB_env) -> Self {
        Environment {
            env: EnvHandle(env, false),
            open_dbis: Mutex::new(HashSet::new()),
        }
    }

    /// Return the underlying `MDB_env` handle.
    ///
    /// ## Safety
    ///
    /// While this call is in and of itself safe, the caller must ensure that
    /// operations against the backing store do not violate Rust aliasing
    /// rules, and must not take any action that would cause the `MDB_env` to
    /// be destroyed prematurely, or to use it after this `Environment` is
    /// destroyed.
    pub fn as_raw(&self) -> *mut ffi::MDB_env {
        self.env.0
    }

    /// Consume this `Environment` and return the underlying handle.
    ///
    /// After this call, it is the caller's responsibility to ensure that the
    /// `MDB_env` is eventually destroyed, if it was actually owned by this
    /// `Environment` (compare [`from_raw`](#method.from_raw) and
    /// [`borrow_raw`](#method.borrow_raw)).
    ///
    /// ## Safety
    ///
    /// While this call is in and of itself safe, the caller must ensure that
    /// operations against the backing store do not violate Rust aliasing
    /// rules.
    pub fn into_raw(self) -> *mut ffi::MDB_env {
        let ret = self.env.0;
        mem::forget(self.env);
        ret
    }

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
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// let out = tempdir::TempDir::new_in(".", "lmdbcopy").unwrap();
    /// env.copy(out.path().to_str().unwrap(),
    ///          lmdb::copy::COMPACT).unwrap();
    /// // We could now open up an independent environment in `lmdbcopyXXXX`
    /// // or upload it somewhere, eg, while `env` could continue being
    /// // modified concurrently.
    /// # }
    /// ```
    pub fn copy(&self, path: &str, flags: copy::Flags) -> Result<()> {
        let path_cstr = try!(CString::new(path));
        unsafe {
            lmdb_call!(ffi2::mdb_env_copy2(
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
            lmdb_call!(ffi2::mdb_env_copyfd2(self.env.0, fd, flags.bits()));
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
    /// concurrently with itself or with `get_flags()`. This could not be
    /// accomplished by using `&mut self`, since any open databases necessarily
    /// have the environment borrowed already.
    ///
    /// ## Example
    /// ```
    /// # include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/example_helpers.rs"));
    /// # fn main() {
    /// # let env = create_env();
    /// unsafe {
    ///   // Enable the NOMETASYNC and MAPASYNC flags
    ///   env.set_flags(lmdb::open::NOMETASYNC | lmdb::open::MAPASYNC, true)
    ///     .unwrap();
    ///   assert!(env.flags().unwrap().contains(
    ///     lmdb::open::NOMETASYNC | lmdb::open::MAPASYNC));
    ///   // Turn MAPASYNC back off, leaving NOMETASYNC set
    ///   env.set_flags(lmdb::open::MAPASYNC, false).unwrap();
    ///   assert!(env.flags().unwrap().contains(lmdb::open::NOMETASYNC));
    ///   assert!(!env.flags().unwrap().contains(lmdb::open::MAPASYNC));
    /// }
    /// # }
    /// ```
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
        let mut raw: *mut c_char = ptr::null_mut();
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
    /// Depends on the compile-time constant `MDB_MAXKEYSIZE` in LMDB.
    /// Default 511.
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
}

// Internal API
pub fn dbi_close(this: &Environment, dbi: ffi::MDB_dbi) {
    // Hold the lock through the end of the function to also guard the
    // LMDB's unsynchronised DBI table.
    let mut locked_dbis = this.open_dbis.lock()
        .expect("open_dbis lock poisoned");
    assert!(locked_dbis.remove(&dbi),
            "closed dbi that wasn't open");

    unsafe {
        ffi::mdb_dbi_close(this.env.0, dbi);
    }
}

// Internal API
pub fn dbi_delete(this: &Environment, dbi: ffi::MDB_dbi) -> Result<()> {
    // Hold the lock across the call to `mdb_drop()` to also guard its
    // unsynchronised DBI table.
    let mut locked_dbis = this.open_dbis.lock()
        .expect("open_dbis lock poisoned");
    unsafe {
        let mut raw_txn: *mut ffi::MDB_txn = ptr::null_mut();
        lmdb_call!(ffi::mdb_txn_begin(
            this.env.0, ptr::null_mut(), 0, &mut raw_txn));
        let mut txn = TxHandle(raw_txn);
        lmdb_call!(ffi::mdb_drop(raw_txn, dbi, 1 /* delete */));
        try!(txn.commit());
    }
    assert!(locked_dbis.remove(&dbi),
            "closed dbi that wasn't open");
    Ok(())
}

// Internal API
pub fn env_ptr(this: &Environment) -> *mut ffi::MDB_env {
    this.env.0
}

// Internal API
pub fn env_open_dbis(this: &Environment) -> &Mutex<HashSet<ffi::MDB_dbi>> {
    &this.open_dbis
}

#[cfg(test)]
mod test {
    use test_helpers::*;
    use env::*;
    use tx::*;

    #[test]
    fn borrow_raw_doesnt_take_ownership() {
        let outer_env = create_env();
        {
            let inner_env = unsafe {
                Environment::borrow_raw(outer_env.as_raw())
            };
            let db = defdb(&inner_env);
            let tx = WriteTransaction::new(&inner_env).unwrap();
            tx.access().put(&db, "foo", "bar", put::Flags::empty()).unwrap();
            tx.commit().unwrap();
        }

        let db = defdb(&outer_env);
        let tx = ReadTransaction::new(&outer_env).unwrap();
        assert_eq!("bar", tx.access().get::<str,str>(&db, "foo").unwrap());
    }
}
