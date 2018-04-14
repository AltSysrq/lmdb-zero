// Copyright 2016 FullContact, Inc
// Copyright 2018 Jason Lingle, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use tempdir;

use dbi;
use env;

pub fn create_env() -> env::Environment {
    unsafe {
        let mut builder = env::EnvBuilder::new().unwrap();
        builder.set_maxdbs(2).unwrap();
        builder.open(
            tempdir::TempDir::new_in(".", "lmdbzero").unwrap()
                .path().to_str().unwrap(),
            env::open::Flags::empty(), 0o600).unwrap()
    }
}

#[allow(dead_code)]
pub fn dupdb(env: &env::Environment) -> dbi::Database {
    dbi::Database::open(env, Some("example"), &dbi::DatabaseOptions::new(
        dbi::db::CREATE | dbi::db::DUPSORT)).unwrap()
}

#[allow(dead_code)]
pub fn dupfixeddb(env: &env::Environment) -> dbi::Database {
    dbi::Database::open(env, Some("example"), &dbi::DatabaseOptions::new(
        dbi::db::CREATE | dbi::db::DUPSORT | dbi::db::DUPFIXED)).unwrap()
}

#[allow(dead_code)]
pub fn defdb(env: &env::Environment) -> dbi::Database {
    dbi::Database::open(env, None, &dbi::DatabaseOptions::defaults())
        .unwrap()
}
