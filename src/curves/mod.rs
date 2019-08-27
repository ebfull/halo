use crate::Field;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

pub trait Curve:
    Sized
    + Default
    + Copy
    + Clone
    + Send
    + Sync
    + 'static
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<<Self as Curve>::Scalar, Output = Self>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Mul<&'a <Self as Curve>::Scalar, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + MulAssign<<Self as Curve>::Scalar>
    + AddAssign
    + SubAssign
    + for<'a> MulAssign<&'a <Self as Curve>::Scalar>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + PartialEq
    + Eq
    + ConditionallySelectable
    + ConstantTimeEq
{
    type Scalar: Field;
    type Base: Field;

    fn zero() -> Self;
    fn one() -> Self;

    fn is_zero(&self) -> Choice;

    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;
    fn to_bytes(&self) -> [u8; 32];
    fn get_xy(&self) -> CtOption<(Self::Base, Self::Base)>;

    fn double(&self) -> Self;

    fn b() -> Self::Base;
}

mod ec0;
mod ec1;

pub use ec0::*;
pub use ec1::*;
