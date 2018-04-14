// Copyright 2016 FullContact, Inc
// Copyright 2017 Jason Lingle
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
//!     &env, None, &lmdb::DatabaseOptions::defaults())
//!     .unwrap();
//!   {
//!     // Write some data in a transaction
//!     let txn = lmdb::WriteTransaction::new(&env).unwrap();
//!     // An accessor is used to control memory access.
//!     // NB You can only have one live accessor from a particular transaction
//!     // at a time. Violating this results in a panic at runtime.
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
//! # Lifetimes and Ownership
//!
//! Lmdb-zero heavily uses lifetime parameters to allow user code to safely
//! retain handles into LMDB without extra runtime overhead.
//!
//! While this makes the library very flexible, it also makes it somewhat
//! harder to use when its types need to be referenced explicitly, for example
//! as struct members. The documentation for each type with lifetime parameters
//! therefore includes a short discussion of how the lifetimes are intended to
//! interact and how best to work with them.
//!
//! It is also possible to opt-out of compile-time lifetime tracking and
//! instead use `Arc` or `Rc` around various handles. In this case, all the
//! lifetime parameters simply become `'static`. See the next section for
//! details.
//!
//! ## Ownership Modes
//!
//! As of version 0.4.0, most APIs which construct a value which holds on to
//! some "parent" value (e.g., creating a `Database` within an `Environment`)
//! accept anything that can be converted into a [`Supercow`](https://docs.rs/supercow/0.1.0/supercow/).
//! Deep understanding of `Supercow` itself is not required to use `lmdb-zero`.
//! The only thing you need to know is that an `Into<Supercow<T>>` means that
//! you can pass in one of three classes of arguments:
//!
//! - `&T`. This is "borrowed mode". The majority of the documentation in this
//! crate uses borrowed mode. This is zero-overhead and is statically
//! verifiable (i.e., all usage is checked at compile-time), so it is
//! recommended that borrowed mode be used whenever reasonably possible. This
//! mode causes the "child" value to hold a normal reference to the parent,
//! which means that lifetimes must be tracked in the lifetime parameters. But
//! because of this, this mode can be inflexible; for example, you cannot use
//! safe Rust to create a `struct` holding both an `Environment` and its
//! `Database`s using borrowed mode.
//!
//! - `Arc<T>`. This is "shared mode". For `NonSyncSupercow`, `Rc<T>` may also
//! be used. The child will hold the `Arc` or `Rc`, thus ensuring the parent
//! lives at least as long as the child. Because of this, the related lifetime
//! parameters can simply be written as `'static`. It also means that
//! `Arc`/`Rc` references to the child and parent can be placed together in the
//! same struct with safe Rust. This comes at a cost: Constructing values in
//! shared mode incurs allocation; additionally, the ability to statically
//! verify the lifetime of the parent values is lost.
//!
//! - `T`. This is "owned mode". The parent is moved into the child value and
//! owned by the child from thereon. This is most useful when you only ever
//! want one child and don't care about retaining ownership of the parent. As
//! with shared mode, it also allows simply using `'static` as the relevant
//! lifetime parameters.
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
//! - Using ownership modes other than borrowed (i.e., mundane references)
//!   incurs extra allocations in addition to the overhead of inherent in that
//!   ownership mode.
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
//!
//! # Unavailable LMDB APIs
//!
//! - `mdb_env_copy`, `mdb_env_copyfd`: Only the `2`-suffixed versions that
//! take flags are exposed.
//!
//! - `mdb_env_set_userctx`, `mdb_env_get_userctx`: Not generally useful for
//! Rust; unclear how ownership would be expressed; would likely end up forcing
//! an almost-never-used generic arg on `Environment` on everyone.
//!
//! - `mdb_env_set_assert`: Does not seem useful enough to expose.
//!
//! - `mdb_txn_env`, `mdb_cursor_txn`, `mdb_cursor_dbi`: Would allow violating
//! borrow semantics.
//!
//! - `mdb_cmp`, `mdb_dcmp`: Doesn't seem useful; this would basically be a
//! reinterpret cast from the input values to whatever the table comparator
//! expects and then invoking the `Ord` implementation. If the types match,
//! this is strictly inferior to just using `Ord` directly; if they don't, it
//! at best is obfuscating, and at worst completely broken.
//!
//! - `mdb_set_relfunc`, `mdb_set_relctx`: Currently a noop in LMDB. Even if it
//! weren't, it is unlikely that there is any remotely safe or convenient way
//! to provide an interface to it.
//!
//! - `mdb_reader_list`: Doesn't seem useful enough to expose.

#![deny(missing_docs)]

extern crate liblmdb_sys as ffi;
extern crate libc;
extern crate supercow;
#[macro_use] extern crate bitflags;
#[cfg(test)] extern crate tempdir;

use std::ffi::CStr;

pub use ffi::mdb_mode_t as FileMode;
pub use ffi::mdb_filehandle_t as Fd;

macro_rules! lmdb_call {
    ($x:expr) => { {
        let code = $x;
        if 0 != code {
            return Err($crate::Error::Code(code));
        }
    } }
}

/// Returns the LMDB version as a string.
pub fn version_str() -> &'static str {
    let mut major: libc::c_int = 0;
    let mut minor: libc::c_int = 0;
    let mut rev: libc::c_int = 0;
    unsafe {
        CStr::from_ptr(ffi::mdb_version(&mut major, &mut minor, &mut rev))
            .to_str().unwrap_or("(invalid)")
    }
}

/// Returns the LMDB version as (major, minor, revision).
pub fn version() -> (i32, i32, i32) {
    let mut major: libc::c_int = 0;
    let mut minor: libc::c_int = 0;
    let mut rev: libc::c_int = 0;
    unsafe {
        ffi::mdb_version(&mut major, &mut minor, &mut rev);
    }
    (major as i32, minor as i32, rev as i32)
}

/// Empty type used to indicate "don't care" when reading values from LMDB.
///
/// `FromLmdbBytes` is implemented for this type by simply returning its only
/// value without inspecting anything.
pub struct Ignore;

mod mdb_vals;
mod ffi2;
#[cfg(test)] mod test_helpers;

pub mod error;
pub use error::{Error, LmdbResultExt, Result};

mod env;
pub use env::{open, copy, EnvBuilder, Environment, Stat, EnvInfo};

mod dbi;
pub use dbi::{db, Database, DatabaseOptions};

pub mod traits;
mod unaligned;
pub use unaligned::{Unaligned, unaligned};

mod tx;
pub use tx::{ConstTransaction, ReadTransaction, WriteTransaction};
pub use tx::ResetTransaction;
pub use tx::{ConstAccessor, WriteAccessor};
pub use tx::{put, del};

mod cursor;
pub use cursor::{StaleCursor, Cursor};

mod iter;
pub use iter::{CursorIter, MaybeOwned};
