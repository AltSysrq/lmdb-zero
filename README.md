# lmdb-zero

lmdb-zero is a near-zero-cost wrapper around [LMDB](http://lmdb.tech/) designed
to allow using the full range of features offered by LMDB while keeping it
reasonably easy to write safe programs.

[Documentation](https://api.fullcontact.com/v3/docs/rustdoc/lmdb_zero/index.html)

## Why _another_ LMDB library?

_There already exist the competing `lmdb` and `lmdb-rs` crates right now. Why
write a third?_

The main issue with the existing crates is that they try to abstract some
properties of LMDB away, and as a result are not able to expose some of LMDB's
functionality, and in some cases compromise safety.

`lmdb-zero` is instead as much as possible a 1:1 mapping of the raw API, mainly
providing RAII constructs and integration into Rust's borrow checker to ensure
safety.

## Features

- Zero-copy API. Reads return references into the memory-mapped file. Using
  `MDB_RESERVE` to allocate space in the file and directly write to it is
  supported.

- Cursors directly map to the same operations provided by LMDB, but in a
  typesafe manner.

- Nested transactions.

- Full integration with the borrow checker. Read references are checked to not
  outlive their transaction or overlap with a write in the same transaction.

- Cursors and read transactions can be reset and reused.

## Status

The API is complete but not necessarily completely stable; there may yet be
unsound parts of the API or the implementations.

This crate has not been tested on architectures with strong alignment
constraints. While the conversion API checks for correct alignment by default,
issues such as [#27060](https://github.com/rust-lang/rust/issues/27060) could
come up, and it is of course possible there are bugs in handling alignment
here.

## Changelog

*0.2.1*: Fix use-after-free when passing database name to `mdb_dbi_open`. Fix
 calling `mdb_txn_abort` after transaction commit fails.
 [#1](https://github.com/fullcontact/lmdb-zero/pull/1).

*0.2.0*: Switch from `lmdb-sys` to newer `liblmdb-sys`.

*0.1.0*: Initial release.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
