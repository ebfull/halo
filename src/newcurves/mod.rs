use crate::Field;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

pub trait Curve:
    Sized
    + Default
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
    + for<'a> Mul<<Self as Curve>::Scalar, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + MulAssign<<Self as Curve>::Scalar>
    + AddAssign
    + SubAssign
    + for<'a> MulAssign<&'a <Self as Curve>::Scalar>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + AddAssign<<Self as Curve>::Affine>
    + SubAssign<<Self as Curve>::Affine>
    + for<'a> AddAssign<<Self as Curve>::Affine>
    + for<'a> SubAssign<<Self as Curve>::Affine>
    + PartialEq
    + Eq
    + ConditionallySelectable
    + ConstantTimeEq
{
    type Affine: CurveAffine<
        Projective = Self,
        Scalar = <Self as Curve>::Scalar,
        Base = <Self as Curve>::Base,
    >;
    type Scalar: Field;
    type Base: Field;

    /// Obtains the additive identity.
    fn zero() -> Self;

    /// Obtains the base point of the curve.
    fn one() -> Self;

    /// Doubles this element.
    fn double(&self) -> Self;

    /// Returns whether or not this element is the identity.
    fn is_zero(&self) -> Choice;

    /// Converts this element into its affine form.
    fn to_affine(&self) -> Self::Affine;

    /// Converts many elements into their affine form. Panics if the
    /// sizes of the slices are different.
    fn batch_to_affine(v: &[Self], target: &mut [Self::Affine]);

    fn b() -> Self::Base;
}

pub trait CurveAffine:
    Sized
    + Default
    + Clone
    + Send
    + Sync
    + 'static
    + Debug
    + Add<Output = <Self as CurveAffine>::Projective>
    + Sub<Output = <Self as CurveAffine>::Projective>
    + Mul<<Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + Neg
    + for<'a> Add<&'a Self, Output = <Self as CurveAffine>::Projective>
    + for<'a> Mul<&'a <Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + for<'a> Mul<<Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + for<'a> Sub<&'a Self, Output = <Self as CurveAffine>::Projective>
    + PartialEq
    + Eq
    + ConditionallySelectable
    + ConstantTimeEq
{
    type Projective: Curve<
        Affine = Self,
        Scalar = <Self as CurveAffine>::Scalar,
        Base = <Self as CurveAffine>::Base,
    >;
    type Scalar: Field;
    type Base: Field;

    /// Converts into the projective form.
    fn to_projective(&self) -> Self::Projective;
    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;
    fn to_bytes(&self) -> [u8; 32];
    fn from_bytes_wide(bytes: &[u8; 64]) -> CtOption<Self>;
    fn to_bytes_wide(&self) -> [u8; 64];
}
