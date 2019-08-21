use crate::fields::Field;
use std::ops::{Add, Mul, Neg, Sub};

const MODULUS: u32 = 2113929217;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Fp(u32);

impl Field for Fp {
    const CAPACITY: u32 = 30;
    const S: u32 = 25;
    const GENERATOR: Self = Fp(5);
    const ALPHA: Self = Fp(1971140334);

    fn from_u64(v: u64) -> Self {
        Fp((v % (MODULUS as u64)) as u32)
    }

    fn invert(&self) -> Option<Self> {
        if self.0 == 0 {
            None
        } else {
            Some(self.pow((MODULUS - 2) as u64))
        }
    }
}

impl Add for Fp {
    type Output = Fp;

    fn add(self, other: Fp) -> Self::Output {
        Fp((self.0 + other.0) % MODULUS)
    }
}

impl Neg for Fp {
    type Output = Fp;

    fn neg(self) -> Self::Output {
        Fp((MODULUS - self.0) % MODULUS)
    }
}

impl Sub for Fp {
    type Output = Fp;

    fn sub(self, other: Fp) -> Self::Output {
        self + (-other)
    }
}

impl Mul for Fp {
    type Output = Fp;

    fn mul(self, other: Fp) -> Self::Output {
        Fp((((self.0 as u64) * (other.0 as u64)) % (MODULUS as u64)) as u32)
    }
}
