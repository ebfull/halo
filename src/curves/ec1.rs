use crate::{Curve, Field, Fp, Fq};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Default, Eq, Debug, Copy, Clone)]
pub struct Ec1 {
    x: Fp,
    y: Fp,
    z: Fp,
}

impl ConstantTimeEq for Ec1 {
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

impl PartialEq for Ec1 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl ConditionallySelectable for Ec1 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Ec1 {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
            z: Fp::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl Curve for Ec1 {
    type Scalar = Fq;
    type Base = Fp;

    const BETA_SCALAR: Self::Scalar = Fq::BETA;
    const BETA_BASE: Self::Base = Fp::BETA;

    fn b() -> Self::Base {
        B
    }

    fn zero() -> Self {
        Ec1 {
            x: Fp::zero(),
            y: Fp::one(),
            z: Fp::zero(),
        }
    }
    fn one() -> Self {
        Ec1 {
            x: Fp::one(),
            y: Fp::from_raw([
                0x793f9e8949e6de0d,
                0xf33aba0091f5fdeb,
                0xbecc40aa0beec5c0,
                0x5e808425ee1f35f,
            ]),
            z: Fp::one(),
        }
    }

    fn is_zero(&self) -> Choice {
        self.z.ct_eq(&Fp::zero())
    }

    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        let mut tmp = *bytes;
        let ysign = Choice::from(tmp[31] >> 7);
        tmp[31] &= 0b0111_1111;

        Fp::from_bytes(&tmp).and_then(|x| {
            use crate::CtOptionExt1;

            CtOption::new(Self::zero(), x.is_zero() & (!ysign)).or_else(|| {
                let x3 = x.square() * x;
                (x3 + B).sqrt().and_then(|y| {
                    let sign = Choice::from(y.to_bytes()[0] & 1);

                    let y = Fp::conditional_select(&y, &-y, ysign ^ sign);

                    CtOption::new(
                        Ec1 {
                            x: x,
                            y: y,
                            z: Fp::one(),
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

    fn get_xyz(&self) -> (Self::Base, Self::Base, Self::Base) {
        (self.x, self.y, self.z)
    }

    fn from_xy(x: Self::Base, y: Self::Base) -> CtOption<Self> {
        // TODO: not constant time yet
        let tmp = Self {
            x,
            y,
            z: Self::Base::one(),
        };

        if tmp.is_on_curve() {
            CtOption::new(tmp, Choice::from(1u8))
        } else if (x.is_zero() & y.is_zero()).into() {
            CtOption::new(Self::zero(), Choice::from(1u8))
        } else {
            CtOption::new(Self::zero(), Choice::from(0u8))
        }
    }

    fn from_xy_unchecked(x: Self::Base, y: Self::Base) -> Self {
        Self {
            x,
            y,
            z: Self::Base::one(),
        }
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

        Ec1 {
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

const B: Fp = Fp::from_raw([7, 0, 0, 0]);

#[inline]
fn mul_by_3b(a: Fp) -> Fp {
    // TODO: more efficient here plz
    a * Fp::from_raw([21, 0, 0, 0])
}

impl<'a> Neg for &'a Ec1 {
    type Output = Ec1;

    #[inline]
    fn neg(self) -> Ec1 {
        // TODO: not constant time
        if bool::from(self.is_zero()) {
            return *self;
        }

        Ec1 {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }
}

impl Neg for Ec1 {
    type Output = Ec1;

    #[inline]
    fn neg(self) -> Ec1 {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Ec1> for &'a Ec1 {
    type Output = Ec1;

    #[inline]
    fn sub(self, rhs: &'b Ec1) -> Ec1 {
        self + (-rhs)
    }
}

impl<'a, 'b> Add<&'b Ec1> for &'a Ec1 {
    type Output = Ec1;

    #[inline]
    fn add(self, rhs: &'b Ec1) -> Ec1 {
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

        Ec1 {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

impl<'a, 'b> Mul<&'b Fq> for &'a Ec1 {
    type Output = Ec1;

    #[inline]
    fn mul(self, rhs: &'b Fq) -> Ec1 {
        let mut acc = Ec1::zero();

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading bit because it's always unset for Fq
        // elements.
        for bit in rhs
            .to_bytes()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(1)
        {
            acc = acc.double();
            acc = Ec1::conditional_select(&acc, &(acc + self), bit);
        }

        acc
    }
}

impl_binops_additive!(Ec1, Ec1);
impl_binops_multiplicative!(Ec1, Fq);

#[test]
fn test_curve() {
    let a = Ec1::one();
    let b = Ec1 {
        x: Fp::from_raw([
            0xdeaffee9d7ffffff,
            0xdd410032d3f0d23d,
            0xfe3be846db7f111a,
            0x4263c28556a2d453,
        ]),
        y: Fp::from_raw([
            0xc8824f3753c55225,
            0x8129510c7e195523,
            0x81227bb9c2fc91e3,
            0x1f8feb2c2589c964,
        ]),
        z: Fp::one(),
    };

    assert_eq!(a + a - a + a, b);
    assert_eq!(a + a, b);
    assert_eq!(a.double(), b);

    let mut test1 = a.to_bytes();
    let test2 = (a + a - a).to_bytes();
    assert_eq!(test1, test2);
    let f = Ec1::from_bytes(&test1).unwrap();
    assert_eq!(a, f);
    test1[31] = (test1[31] & 0b0111_1111) | ((1 - (test1[31] >> 7)) << 7);
    let f = Ec1::from_bytes(&test1).unwrap();
    assert_eq!(-a, f);

    assert_eq!(Ec1::from_bytes(&[0; 32]).unwrap(), Ec1::zero());
    let mut test = [0; 32];
    test[31] = 0b1000_0000;
    assert!(bool::from(Ec1::from_bytes(&test).is_none()));

    let g = Ec1::one();
    let a = Fq::from_u64(1000).invert().unwrap();
    let b = Fq::from_u64(12).invert().unwrap();
    let c = a * b;

    assert_eq!(g * c, (g * a) * b);
    assert!(g * a != g * b);

    assert_eq!(g + Ec1::zero(), g - Ec1::zero());
}

#[test]
fn test_endo() {
    let g = Ec1::one();
    let (x, y) = g.get_xy().unwrap();
    let x = x * Ec1::BETA_BASE;
    assert_eq!(g * Ec1::BETA_SCALAR, Ec1::from_xy_unchecked(x, y));
}
