use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

pub trait Field:
    Sized
    + Default
    + Copy
    + Clone
    + Send
    + Sync
    + 'static
    + Debug
    + From<bool>
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + MulAssign
    + AddAssign
    + SubAssign
    + for<'a> MulAssign<&'a Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + PartialEq
    + Eq
    + ConditionallySelectable
    + ConstantTimeEq
{
    /// How many bits needed to express the modulus?
    const NUM_BITS: u32;

    /// How many bits of information can be stored reliably?
    const CAPACITY: u32;

    // p - 1 is divisible by 2^s
    const S: u32;

    /// Generator of the 2^s multiplicative subgroup
    const ROOT_OF_UNITY: Self;

    /// Ideally the smallest prime such that gcd(p - 1, alpha) = 1
    const RESCUE_ALPHA: u64;

    /// RESCUE_INVALPHA * RESCUE_ALPHA = 1 mod (p - 1)
    const RESCUE_INVALPHA: [u64; 4];

    /// Element of multiplicative order 3.
    const ZETA: Self;

    fn is_zero(&self) -> Choice;

    fn from_u64(v: u64) -> Self;
    fn from_u128(v: u128) -> Self;
    fn sqrt(&self) -> CtOption<Self>;
    fn invert(&self) -> CtOption<Self>;

    fn zero() -> Self;
    fn one() -> Self;
    fn square(&self) -> Self;

    fn to_bytes(&self) -> [u8; 32];
    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;

    /// Exponentiates `self` by `by`, where `by` is a
    /// little-endian order integer exponent.
    fn pow(&self, by: &[u64; 4]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();
                let mut tmp = res;
                tmp *= self;
                res.conditional_assign(&tmp, (((*e >> i) & 0x1) as u8).into());
            }
        }
        res
    }

    /// Exponentiates `self` by `by`, where `by` is a
    /// little-endian order integer exponent.
    ///
    /// **This operation is variable time with respect
    /// to the exponent.** If the exponent is fixed,
    /// this operation is effectively constant time.
    fn pow_vartime(&self, by: &[u64; 4]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();

                if ((*e >> i) & 1) == 1 {
                    res.mul_assign(self);
                }
            }
        }
        res
    }

    /// Gets the lower 128 bits of this field element when
    /// expressed canonically.
    fn get_lower_128(&self) -> u128;

    // Performs a batch inversion using Montgomery's trick,
    // returns the product of every inverse. Zero inputs are
    // ignored.
    fn batch_invert(v: &mut [Self]) -> Self {
        let mut tmp = Vec::with_capacity(v.len());

        let mut acc = Self::one();
        for p in v.iter() {
            tmp.push(acc);
            acc = Self::conditional_select(&(acc * p), &acc, p.is_zero());
        }

        acc = acc.invert().unwrap();
        let allinv = acc;

        for (p, tmp) in v.iter_mut().rev().zip(tmp.into_iter().rev()) {
            let skip = p.is_zero();

            let tmp = tmp * acc;
            acc = Self::conditional_select(&(acc * *p), &acc, skip);
            *p = Self::conditional_select(&tmp, p, skip);
        }

        allinv
    }
}

mod fp;
mod fq;

pub use fp::*;
pub use fq::*;
