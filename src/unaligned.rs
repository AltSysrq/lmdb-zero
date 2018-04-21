// Copyright 2016 FullContact, Inc
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cmp;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops;

use traits::*;

/// Wrapper for arbitrary `Copy` types which lifts their alignment
/// restrictions.
///
/// This allows using values which have non-byte alignment but are otherwise
/// LMDB-safe (as defined by `LmdbRaw`) to be used with it. It obviously does
/// not make `T` itself packed, so the same discussion with respect to padding
/// in the `LmdbRaw` documentation applies here as well.
///
/// There is no way to get a reference to the contained value, as Rust
/// currently has no way to express that the reference may be misaligned. (See
/// also [https://github.com/rust-lang/rust/issues/27060](https://github.com/rust-lang/rust/issues/27060).)
///
/// ### Example
///
/// ```
/// use lmdb_zero as lmdb;
/// use lmdb_zero::Unaligned as U;
///
/// fn get_a_u64(env: &lmdb::Environment, db: &lmdb::Database,
///              key: &str) -> u64 {
///   let tx = lmdb::ReadTransaction::new(env).unwrap();
///   let access = tx.access();
///   access.get::<str, U<u64>>(db, key).unwrap().get()
/// }
/// ```
#[repr(packed)]
pub struct Unaligned<T : LmdbRawIfUnaligned>(T);

impl<T : LmdbRawIfUnaligned> Clone for Unaligned<T> {
    fn clone(&self) -> Self {
        Unaligned(self.0)
    }
}

impl<T : LmdbRawIfUnaligned> Copy for Unaligned<T> { }

unsafe impl<T : LmdbRawIfUnaligned> LmdbRaw for Unaligned<T> {
    fn reported_type() -> String {
        format!("Unaligned<{}>", T::reported_type())
    }
}

unsafe impl<T : LmdbRawIfUnaligned + LmdbOrdKeyIfUnaligned> LmdbOrdKey
for Unaligned<T> {
    fn ordered_by_bytes() -> bool { T::ordered_by_bytes() }
    fn ordered_as_integer() -> bool { T::ordered_as_integer() }
}

impl<T : LmdbRawIfUnaligned> Unaligned<T> {
    /// Wraps `t` in an `Unaligned` marker.
    pub fn new(t: T) -> Self {
        Unaligned(t)
    }

    /// Returns `t` as if it were wrapped by `Unaligned`.
    ///
    /// This is safe because any `&T` _is_ a valid `&Unaligned<T>`.
    pub fn of_ref(t: &T) -> &Self {
        unsafe { mem::transmute(t) }
    }

    /// Returns `t` as if it were wrapped by `Unaligned`.
    ///
    /// This is safe because any `&T` _is_ a valid `&Unaligned<T>`.
    pub fn of_mut(t: &mut T) -> &mut Self {
        unsafe { mem::transmute(t) }
    }

    /// Extracts the contained value.
    ///
    /// This is safe as the compiler has visibility into the fact that the
    /// contained value is misaligned and can copy appropriately.
    pub fn get(&self) -> T { self.0 }

    /// Replaces the contained value.
    pub fn set(&mut self, t: T) { self.0 = t; }
}

/// Synonym for `Unaligned::of_ref()`.
pub fn unaligned<T : LmdbRawIfUnaligned>(t: &T) -> &Unaligned<T> {
    Unaligned::of_ref(t)
}

// Since a future rust version may bar taking a reference to a member of a
// packed structure (and it's not entirely safe right now), manually implement
// everything to copy to a local variable and then delegate.

macro_rules! deleg_fmt {
    ($tr:ident) => {
        impl<T : LmdbRawIfUnaligned> fmt::$tr for Unaligned<T> where T : fmt::$tr {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                let inner = self.0;
                inner.fmt(fmt)
            }
        }
    }
}

deleg_fmt!(Binary);
deleg_fmt!(Debug);
deleg_fmt!(Display);
deleg_fmt!(LowerExp);
deleg_fmt!(LowerHex);
deleg_fmt!(Octal);
deleg_fmt!(Pointer);
deleg_fmt!(UpperExp);
deleg_fmt!(UpperHex);

impl<T : LmdbRawIfUnaligned + cmp::PartialEq<T>>
cmp::PartialEq<Unaligned<T>> for Unaligned<T> {
    fn eq(&self, other: &Self) -> bool {
        let (lhs, rhs) = (self.0, other.0);
        lhs.eq(&rhs)
    }
}
impl<T : LmdbRawIfUnaligned + cmp::Eq> cmp::Eq for Unaligned<T> { }
impl<T : LmdbRawIfUnaligned + cmp::PartialOrd<T>>
cmp::PartialOrd<Unaligned<T>> for Unaligned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        let (lhs, rhs) = (self.0, other.0);
        lhs.partial_cmp(&rhs)
    }
    fn lt(&self, other: &Self) -> bool {
        let (lhs, rhs) = (self.0, other.0);
        lhs.lt(&rhs)
    }
    fn le(&self, other: &Self) -> bool {
        let (lhs, rhs) = (self.0, other.0);
        lhs.le(&rhs)
    }
    fn gt(&self, other: &Self) -> bool {
        let (lhs, rhs) = (self.0, other.0);
        lhs.gt(&rhs)
    }
    fn ge(&self, other: &Self) -> bool {
        let (lhs, rhs) = (self.0, other.0);
        lhs.ge(&rhs)
    }
}
impl<T : LmdbRawIfUnaligned + cmp::Ord> cmp::Ord for Unaligned<T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let (lhs, rhs) = (self.0, other.0);
        lhs.cmp(&rhs)
    }
}

impl<T : LmdbRawIfUnaligned + Hash> Hash for Unaligned<T> {
    fn hash<H : Hasher>(&self, state: &mut H) {
        let v = self.0;
        v.hash(state)
    }
}

macro_rules! binop {
    ($tr:ident, $meth:ident) => {
        impl<T : LmdbRawIfUnaligned + ops::$tr<T>>
        ops::$tr<Unaligned<T>> for Unaligned<T>
        where T::Output : LmdbRawIfUnaligned {
            type Output = Unaligned<T::Output>;
            fn $meth(self, rhs: Self) -> Self::Output {
                let (lhs, rhs) = (self.0, rhs.0);
                Unaligned(lhs.$meth(rhs))
            }
        }
    }
}

macro_rules! binopeq {
    ($tr:ident, $meth:ident) => {
        impl<T : LmdbRawIfUnaligned + ops::$tr<T>>
        ops::$tr<Unaligned<T>> for Unaligned<T> {
            fn $meth(&mut self, rhs: Self) {
                let (mut lhs, rhs) = (self.0, rhs.0);
                lhs.$meth(rhs);
                self.0 = lhs;
            }
        }
    }
}

binop!(Add, add);
binop!(BitAnd, bitand);
binop!(BitOr, bitor);
binop!(BitXor, bitxor);
binop!(Div, div);
binop!(Mul, mul);
binop!(Rem, rem);
binop!(Shl, shl);
binop!(Shr, shr);
binop!(Sub, sub);

binopeq!(AddAssign, add_assign);
binopeq!(BitAndAssign, bitand_assign);
binopeq!(BitOrAssign, bitor_assign);
binopeq!(BitXorAssign, bitxor_assign);
binopeq!(DivAssign, div_assign);
binopeq!(MulAssign, mul_assign);
binopeq!(RemAssign, rem_assign);
binopeq!(ShlAssign, shl_assign);
binopeq!(ShrAssign, shr_assign);
binopeq!(SubAssign, sub_assign);
