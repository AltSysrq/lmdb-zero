// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This is not a lmdb-zero module. It's included by the doc tests to provide
// common functionality.

extern crate tempdir;
extern crate lmdb_zero as lmdb;

#[allow(dead_code)]
fn create_env() -> lmdb::Environment {
    unsafe {
        let mut builder = lmdb::EnvBuilder::new().unwrap();
        builder.set_maxdbs(2).unwrap();
        builder.open(
            tempdir::TempDir::new_in(".", "lmdbzero").unwrap()
                .path().to_str().unwrap(),
            lmdb::open::Flags::empty(), 0o600).unwrap()
    }
}

#[allow(dead_code)]
fn dupdb(env: &lmdb::Environment) -> lmdb::Database {
    lmdb::Database::open(env, Some("example"), &lmdb::DatabaseOptions::new(
        lmdb::db::CREATE | lmdb::db::DUPSORT)).unwrap()
}

#[allow(dead_code)]
fn dupfixeddb(env: &lmdb::Environment) -> lmdb::Database {
    lmdb::Database::open(env, Some("example"), &lmdb::DatabaseOptions::new(
        lmdb::db::CREATE | lmdb::db::DUPSORT | lmdb::db::DUPFIXED)).unwrap()
}

#[allow(dead_code)]
fn defdb(env: &lmdb::Environment) -> lmdb::Database {
    lmdb::Database::open(env, None, &lmdb::DatabaseOptions::defaults())
        .unwrap()
}
