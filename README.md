# lmdb-zero

lmdb-zero is a near-zero-cost wrapper around [LMDB](http://lmdb.tech/) designed
to allow using the full range of features offered by LMDB while keeping it
reasonably easy to write safe programs.

## Why _another_ LMDB library?

_There already exist the competing `lmdb` and `lmdb-rs` crates right now. Why
write a third?_

The main issue with the existing crates is that they try to abstract some
properties of LMDB away, and as a result are not able to expose some of LMDB's
functionality, and in some cases compromise safety.

`lmdb-zero` is instead as much as possible a 1:1 mapping of the raw API, mainly
providing RAII constructs and integration into Rust's borrow checker to ensure
safety.
