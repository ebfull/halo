use crate::curves::Curve;
use crate::fields::{Field, Fp};

use std::ops::{Add, Mul, Neg, Sub};

/// As a shortcut, pretend to have an elliptic curve
/// of this order.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Ec1(Fp);

impl Curve for Ec1 {
    type Scalar = Fp;

    fn one(&self) -> Self {
        Ec1(Fp::one())
    }
    fn double(&self) -> Self {
        Ec1(self.0 + self.0)
    }
}

impl Add for Ec1 {
    type Output = Ec1;

    fn add(self, other: Ec1) -> Self::Output {
        Ec1(self.0 + other.0)
    }
}

impl Neg for Ec1 {
    type Output = Ec1;

    fn neg(self) -> Self::Output {
        Ec1(-self.0)
    }
}

impl Sub for Ec1 {
    type Output = Ec1;

    fn sub(self, other: Ec1) -> Self::Output {
        Ec1(self.0 - other.0)
    }
}

impl Mul<Fp> for Ec1 {
    type Output = Ec1;

    fn mul(self, other: Fp) -> Self::Output {
        Ec1(self.0 * other)
    }
}
