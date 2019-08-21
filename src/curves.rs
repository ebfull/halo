use crate::fields::Field;
use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

pub trait Curve:
    Sized
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
    + PartialEq
    + Eq
{
    type Scalar: Field;

    fn one(&self) -> Self;
    fn double(&self) -> Self;
}

mod ec1;

pub use ec1::*;
