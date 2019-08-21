use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

pub trait Field:
    Sized
    + Copy
    + Clone
    + Send
    + Sync
    + 'static
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
    + PartialEq
    + Eq
{
    /// How many bits of information can be stored reliably?
    const CAPACITY: u32;

    // p - 1 is divisible by 2^s
    const S: u32;

    /// Generator of the p - 1 order multiplicative subgroup
    const GENERATOR: Self;

    /// Generator of the 2^S multiplicative subgroup
    const ALPHA: Self;

    fn from_u64(v: u64) -> Self;
    fn invert(&self) -> Option<Self>;

    fn zero() -> Self {
        Self::from_u64(0)
    }
    fn one() -> Self {
        Self::from_u64(1)
    }
    fn square(&self) -> Self {
        (*self) * (*self)
    }
    fn pow(&self, by: u64) -> Self {
        let mut acc = Self::one();
        for i in (0..32).rev().map(|b| ((by >> b) & 1) == 1) {
            acc = acc.square();
            if i {
                acc = acc * (*self);
            }
        }
        acc
    }
}

mod fp;

pub use fp::*;
