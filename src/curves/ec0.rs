use crate::{Curve, Field, Fp, Fq};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Default, Eq, Debug, Copy, Clone)]
pub struct Ec0 {
    x: Fq,
    y: Fq,
    z: Fq,
}

impl ConstantTimeEq for Ec0 {
    fn ct_eq(&self, other: &Self) -> Choice {
        let x1 = self.x * other.z;
        let x2 = other.x * self.z;

        let y1 = self.y * other.z;
        let y2 = other.y * self.z;

        let z1 = self.is_zero();
        let z2 = self.is_zero();

        (z1 & z2) | ((!z1) & (!z2) & (x1.ct_eq(&x2)) & (y1.ct_eq(&y2)))
    }
}

impl PartialEq for Ec0 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl ConditionallySelectable for Ec0 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Ec0 {
            x: Fq::conditional_select(&a.x, &b.x, choice),
            y: Fq::conditional_select(&a.y, &b.y, choice),
            z: Fq::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl Curve for Ec0 {
    type Scalar = Fp;
    type Base = Fq;

    fn b() -> Self::Base {
        B
    }

    fn zero() -> Self {
        Ec0 {
            x: Fq::zero(),
            y: Fq::one(),
            z: Fq::zero(),
        }
    }
    fn one() -> Self {
        Ec0 {
            x: Fq::one(),
            y: Fq::from_raw([
                0x8470e2773a41d265,
                0xf027d2b37cab6325,
                0x622572e64860fa80,
                0xcd539c198b2acdf,
            ]),
            z: Fq::one(),
        }
    }

    fn is_zero(&self) -> Choice {
        self.z.ct_eq(&Fq::zero())
    }

    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        let mut tmp = *bytes;
        let ysign = Choice::from(tmp[31] >> 7);
        tmp[31] &= 0b0111_1111;

        Fq::from_bytes(&tmp).and_then(|x| {
            use crate::CtOptionExt;

            CtOption::new(Self::zero(), x.is_zero() & (!ysign)).or_else(|| {
                let x3 = x.square() * x;
                (x3 + B).sqrt().and_then(|y| {
                    let sign = Choice::from(y.to_bytes()[0] & 1);

                    let y = Fq::conditional_select(&y, &-y, ysign ^ sign);

                    CtOption::new(
                        Ec0 {
                            x: x,
                            y: y,
                            z: Fq::one(),
                        },
                        Choice::from(1u8),
                    )
                })
            })
        })
    }
    fn to_bytes(&self) -> [u8; 32] {
        // TODO: mark this vartime?
        if bool::from(self.is_zero()) {
            [0; 32]
        } else {
            let (x, y) = self.get_xy().unwrap();
            let sign = (y.to_bytes()[0] & 1) << 7;
            let mut xbytes = x.to_bytes();
            xbytes[31] |= sign;
            xbytes
        }
    }

    /// Returns (x, y) for a point that is not at infinity
    fn get_xy(&self) -> CtOption<(Self::Base, Self::Base)> {
        self.z.invert().and_then(|zinv| {
            let x = self.x * zinv;
            let y = self.y * zinv;

            CtOption::new((x, y), Choice::from(1u8))
        })
    }

    fn double(&self) -> Self {
        // Algorithm 9, https://eprint.iacr.org/2015/1060.pdf

        let t0 = self.y.square();
        let z3 = t0 + t0;
        let z3 = z3 + z3;
        let z3 = z3 + z3;
        let t1 = self.y * self.z;
        let t2 = self.z.square();
        let t2 = mul_by_3b(t2);
        let x3 = t2 * z3;
        let y3 = t0 + t2;
        let z3 = t1 * z3;
        let t1 = t2 + t2;
        let t2 = t1 + t2;
        let t0 = t0 - t2;
        let y3 = t0 * y3;
        let y3 = x3 + y3;
        let t1 = self.x * self.y;
        let x3 = t0 * t1;
        let x3 = x3 + x3;

        Ec0 {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    fn is_on_curve(&self) -> bool {
        if bool::from(self.is_zero()) {
            return true;
        }

        let (x, y) = self.get_xy().unwrap();
        (x.square() * x + B) == y.square()
    }
}

const B: Fq = Fq::from_raw([5, 0, 0, 0]);

#[inline]
fn mul_by_3b(a: Fq) -> Fq {
    // TODO: more efficient here plz
    a * Fq::from_raw([15, 0, 0, 0])
}

impl<'a> Neg for &'a Ec0 {
    type Output = Ec0;

    #[inline]
    fn neg(self) -> Ec0 {
        // TODO: not constant time
        if bool::from(self.is_zero()) {
            return *self;
        }

        Ec0 {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }
}

impl Neg for Ec0 {
    type Output = Ec0;

    #[inline]
    fn neg(self) -> Ec0 {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Ec0> for &'a Ec0 {
    type Output = Ec0;

    #[inline]
    fn sub(self, rhs: &'b Ec0) -> Ec0 {
        self + (-rhs)
    }
}

impl<'a, 'b> Add<&'b Ec0> for &'a Ec0 {
    type Output = Ec0;

    #[inline]
    fn add(self, rhs: &'b Ec0) -> Ec0 {
        // Algorithm 1, https://eprint.iacr.org/2015/1060.pdf
        // TODO: use another algorithm

        let t0 = self.x * rhs.x;
        let t1 = self.y * rhs.y;
        let t2 = self.z * rhs.z;
        let t3 = self.x + self.y;
        let t4 = rhs.x + rhs.y;
        let t3 = t3 * t4;
        let t4 = t0 + t1;
        let t3 = t3 - t4;
        let t4 = self.x + self.z;
        let t5 = rhs.x + rhs.z;
        let t4 = t4 * t5;
        let t5 = t0 + t2;
        let t4 = t4 - t5;
        let t5 = self.y + self.z;
        let x3 = rhs.y + rhs.z;
        let t5 = t5 * x3;
        let x3 = t1 + t2;
        let t5 = t5 - x3;
        let x3 = mul_by_3b(t2);
        let z3 = x3;
        let x3 = t1 - z3;
        let z3 = t1 + z3;
        let y3 = x3 * z3;
        let t1 = t0 + t0;
        let t1 = t1 + t0;
        let t4 = mul_by_3b(t4);
        let t0 = t1 * t4;
        let y3 = y3 + t0;
        let t0 = t5 * t4;
        let x3 = t3 * x3;
        let x3 = x3 - t0;
        let t0 = t3 * t1;
        let z3 = t5 * z3;
        let z3 = z3 + t0;

        Ec0 {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

impl<'a, 'b> Mul<&'b Fp> for &'a Ec0 {
    type Output = Ec0;

    #[inline]
    fn mul(self, rhs: &'b Fp) -> Ec0 {
        let mut acc = Ec0::zero();

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading bit because it's always unset for Fp
        // elements.
        for bit in rhs
            .to_bytes()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(1)
        {
            acc = acc.double();
            acc = Ec0::conditional_select(&acc, &(acc + self), bit);
        }

        acc
    }
}

impl_binops_additive!(Ec0, Ec0);
impl_binops_multiplicative!(Ec0, Fp);

#[test]
fn test_curve() {
    let a = Ec0::one();
    let b = Ec0 {
        x: Fq::from_raw([
            0x903fff0e1fffffff,
            0xb132e2296f00f3c2,
            0x14b9a896a89b03be,
            0x39baebee6198b8a2,
        ]),
        y: Fq::from_raw([
            0xd293110dbf95fae,
            0xf939a07526662e3e,
            0x347f08c7b29dbafe,
            0x3dfa76aaca2568e7,
        ]),
        z: Fq::one(),
    };

    assert_eq!(a + a - a + a, b);
    assert_eq!(a + a, b);
    assert_eq!(a.double(), b);

    let mut test1 = a.to_bytes();
    let test2 = (a + a - a).to_bytes();
    assert_eq!(test1, test2);
    let f = Ec0::from_bytes(&test1).unwrap();
    assert_eq!(a, f);
    test1[31] = (test1[31] & 0b0111_1111) | ((1 - (test1[31] >> 7)) << 7);
    let f = Ec0::from_bytes(&test1).unwrap();
    assert_eq!(-a, f);

    assert_eq!(Ec0::from_bytes(&[0; 32]).unwrap(), Ec0::zero());
    let mut test = [0; 32];
    test[31] = 0b1000_0000;
    assert!(bool::from(Ec0::from_bytes(&test).is_none()));

    let g = Ec0::one();
    let a = Fp::from_u64(1000).invert().unwrap();
    let b = Fp::from_u64(12).invert().unwrap();
    let c = a * b;

    assert_eq!(g * c, (g * a) * b);
    assert!(g * a != g * b);

    assert_eq!(g + Ec0::zero(), g - Ec0::zero());
}
