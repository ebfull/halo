use crate::{Field, Fp, Fq};
use std::cmp;
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
    // + Add<Output = Self>
    // + Sub<Output = Self>
    // + Mul<<Self as Curve>::Scalar, Output = Self>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a <Self as Curve>::Affine, Output = Self>
    // + for<'a> Mul<&'a <Self as Curve>::Scalar, Output = Self>
    // + for<'a> Mul<<Self as Curve>::Scalar, Output = Self>
    // + for<'a> Sub<&'a Self, Output = Self>
    // + MulAssign<<Self as Curve>::Scalar>
    // + AddAssign
    // + SubAssign
    // + for<'a> MulAssign<&'a <Self as Curve>::Scalar>
    // + for<'a> AddAssign<&'a Self>
    // + for<'a> SubAssign<&'a Self>
    // + AddAssign<<Self as Curve>::Affine>
    // + SubAssign<<Self as Curve>::Affine>
    // + for<'a> AddAssign<<Self as Curve>::Affine>
    // + for<'a> SubAssign<<Self as Curve>::Affine>
    + PartialEq
    + cmp::Eq
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

    // /// Converts many elements into their affine form. Panics if the
    // /// sizes of the slices are different.
    // fn batch_to_affine(v: &[Self], target: &mut [Self::Affine]);

    fn b() -> Self::Base;
}

pub trait CurveAffine:
    Sized
    + Default
    + Copy
    + Clone
    + Send
    + Sync
    + 'static
    + Debug
    // + Add<Output = <Self as CurveAffine>::Projective>
    // + Sub<Output = <Self as CurveAffine>::Projective>
    // + Mul<<Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = <Self as CurveAffine>::Projective>
    // + for<'a> Mul<&'a <Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    // + for<'a> Mul<<Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    // + for<'a> Sub<&'a Self, Output = <Self as CurveAffine>::Projective>
    + PartialEq
    + cmp::Eq
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

    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> Choice;

    fn to_projective(&self) -> Self::Projective;

    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;
    fn to_bytes(&self) -> [u8; 32];
    fn from_bytes_wide(bytes: &[u8; 64]) -> CtOption<Self>;
    fn to_bytes_wide(&self) -> [u8; 64];
}

macro_rules! new_curve_impl {
    ($name:ident, $name_affine:ident, $base:ident, $scalar:ident) => {
        #[derive(Copy, Clone, Debug)]
        pub struct $name {
            x: $base,
            y: $base,
            z: $base,
        }

        impl $name {
            const fn curve_constant_b() -> $base {
                // TODO: this may be different with another cycle
                $base::from_raw([5, 0, 0, 0])
            }

            fn mul_by_3b(cur: $base) -> $base {
                // NB: This is specific to b = 5
                let tmp = cur + cur;
                let tmp = tmp + tmp;
                let tmp = tmp + tmp;
                let tmp = tmp + tmp;
                let tmp = tmp - cur;

                tmp
            }
        }

        #[derive(Copy, Clone, Debug)]
        pub struct $name_affine {
            x: $base,
            y: $base,
            infinity: Choice,
        }

        impl Curve for $name {
            type Affine = $name_affine;
            type Scalar = $scalar;
            type Base = $base;

            fn zero() -> Self {
                Self {
                    x: $base::zero(),
                    y: $base::one(),
                    z: $base::zero(),
                }
            }

            fn one() -> Self {
                const NEGATIVE_ONE: $base = $base::neg(&$base::from_raw([1, 0, 0, 0]));
                const TWO: $base = $base::from_raw([2, 0, 0, 0]);

                Self {
                    x: NEGATIVE_ONE,
                    y: TWO,
                    z: $base::one(),
                }
            }

            fn is_zero(&self) -> Choice {
                self.z.is_zero()
            }

            fn to_affine(&self) -> Self::Affine {
                // TODO: not constant time
                if bool::from(self.is_zero()) {
                    $name_affine::zero()
                } else {
                    let zinv = self.z.invert().unwrap();

                    $name_affine {
                        x: self.x * zinv,
                        y: self.y * zinv,
                        infinity: Choice::from(0u8),
                    }
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

                let t2 = $name::mul_by_3b(t2);
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

                Self {
                    x: x3,
                    y: y3,
                    z: z3,
                }
            }

            fn b() -> Self::Base {
                $name::curve_constant_b()
            }
        }

        impl Default for $name {
            fn default() -> $name {
                $name::zero()
            }
        }

        impl ConstantTimeEq for $name {
            fn ct_eq(&self, other: &Self) -> Choice {
                let x1 = self.x * other.z;
                let x2 = other.x * self.z;
                let y1 = self.y * other.z;
                let y2 = other.y * self.z;

                let z1 = self.z.is_zero();
                let z2 = other.z.is_zero();

                (z1 & z2) | ((!z1) & (!z2) & (x1.ct_eq(&x2)) & (y1.ct_eq(&y2)))
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.ct_eq(other).into()
            }
        }

        impl cmp::Eq for $name {}

        impl ConditionallySelectable for $name {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $name {
                    x: $base::conditional_select(&a.x, &b.x, choice),
                    y: $base::conditional_select(&a.y, &b.y, choice),
                    z: $base::conditional_select(&a.z, &b.z, choice),
                }
            }
        }

        impl Neg for $name {
            type Output = $name;

            fn neg(self) -> $name {
                $name {
                    x: self.x,
                    y: -self.y,
                    z: self.z,
                }
            }
        }

        impl<'a> Add<&'a Self> for $name {
            type Output = $name;

            fn add(self, other: &'a $name) -> $name {
                // Algorithm 7, https://eprint.iacr.org/2015/1060.pdf

                let t0 = self.x * other.x;
                let t1 = self.y * other.y;
                let t2 = self.z * other.z;

                let t3 = self.x + self.y;
                let t4 = other.x + other.y;
                let t3 = t3 * t4;

                let t4 = t0 + t1;
                let t3 = t3 - t4;
                let t4 = self.y + self.z;

                let x3 = other.y * other.z;
                let t4 = t4 * x3;
                let x3 = t1 + t2;

                let t4 = t4 - x3;
                let x3 = self.x + self.z;
                let y3 = other.x + other.z;

                let x3 = x3 * y3;
                let y3 = t0 + t2;
                let y3 = x3 - y3;

                let x3 = t0 + t0;
                let t0 = x3 + t0;
                let t2 = $name::mul_by_3b(t2);

                let z3 = t1 + t2;
                let t1 = t1 - t2;
                let y3 = $name::mul_by_3b(y3);

                let x3 = t4 * y3;
                let t2 = t3 * t1;
                let x3 = t2 - x3;

                let y3 = y3 * t0;
                let t1 = t1 * z3;
                let y3 = t1 + y3;

                let t0 = t0 * t3;
                let z3 = z3 * t4;
                let z3 = z3 + t0;

                $name {
                    x: x3,
                    y: y3,
                    z: z3,
                }
            }
        }

        impl<'a> Add<&'a $name_affine> for $name {
            type Output = $name;

            fn add(self, other: &'a $name_affine) -> $name {
                // Algorithm 8, https://eprint.iacr.org/2015/1060.pdf

                // TODO: not constant time
                if bool::from(other.infinity) {
                    self
                } else {
                    let t0 = self.x * other.x;
                    let t1 = self.y * other.y;
                    let t3 = other.x + other.y;

                    let t4 = self.x + self.y;
                    let t3 = t3 * t4;
                    let t4 = t0 + t1;

                    let t3 = t3 - t4;
                    let t4 = other.y * self.z;
                    let t4 = t4 + self.y;

                    let y3 = other.x * self.z;
                    let y3 = y3 + self.x;
                    let x3 = t0 + t0;

                    let t0 = x3 + t0;
                    let t2 = $name::mul_by_3b(self.z);
                    let z3 = t1 + t2;

                    let t1 = t1 - t2;
                    let y3 = $name::mul_by_3b(y3);
                    let x3 = t4 * y3;

                    let t2 = t3 * t1;
                    let x3 = t2 - x3;
                    let t3 = y3 * t0;

                    let t1 = t1 * z3;
                    let y3 = t1 + y3;
                    let t0 = t0 * t3;

                    let z3 = z3 * t4;
                    let z3 = z3 + t0;

                    $name {
                        x: x3,
                        y: y3,
                        z: z3,
                    }
                }
            }
        }

        impl Neg for $name_affine {
            type Output = $name_affine;

            fn neg(self) -> $name_affine {
                $name_affine {
                    x: self.x,
                    y: -self.y,
                    infinity: self.infinity,
                }
            }
        }

        impl<'a> Add<&'a $name_affine> for $name_affine {
            type Output = $name;

            fn add(self, other: &'a $name_affine) -> $name {
                // Variant of
                // Algorithm 8, https://eprint.iacr.org/2015/1060.pdf

                // TODO: not constant time
                if bool::from(self.infinity) {
                    other.to_projective()
                } else if bool::from(other.infinity) {
                    self.to_projective()
                } else {
                    let t0 = self.x * other.x;
                    let t1 = self.y * other.y;
                    let t3 = other.x + other.y;

                    let t4 = self.x + self.y;
                    let t3 = t3 * t4;
                    let t4 = t0 + t1;

                    let t3 = t3 - t4;
                    //let t4 = other.y * self.z;
                    let t4 = other.y + self.y;

                    //let y3 = other.x * self.z;
                    let y3 = other.x + self.x;
                    let x3 = t0 + t0;

                    let t0 = x3 + t0;
                    //let t2 = $name::mul_by_3b(self.z);
                    let t2 = $base::from_raw([15, 0, 0, 0]);
                    let z3 = t1 + t2;

                    let t1 = t1 - t2;
                    let y3 = $name::mul_by_3b(y3);
                    let x3 = t4 * y3;

                    let t2 = t3 * t1;
                    let x3 = t2 - x3;
                    let t3 = y3 * t0;

                    let t1 = t1 * z3;
                    let y3 = t1 + y3;
                    let t0 = t0 * t3;

                    let z3 = z3 * t4;
                    let z3 = z3 + t0;

                    $name {
                        x: x3,
                        y: y3,
                        z: z3,
                    }
                }
            }
        }

        impl CurveAffine for $name_affine {
            type Projective = $name;
            type Scalar = $scalar;
            type Base = $base;

            fn zero() -> Self {
                Self {
                    x: $base::zero(),
                    y: $base::one(),
                    infinity: Choice::from(1u8),
                }
            }

            fn one() -> Self {
                const NEGATIVE_ONE: $base = $base::neg(&$base::from_raw([1, 0, 0, 0]));
                const TWO: $base = $base::from_raw([2, 0, 0, 0]);

                Self {
                    x: NEGATIVE_ONE,
                    y: TWO,
                    infinity: Choice::from(0u8),
                }
            }

            fn is_zero(&self) -> Choice {
                self.infinity
            }

            fn to_projective(&self) -> Self::Projective {
                // TODO: not constant time
                if bool::from(self.infinity) {
                    $name::zero()
                } else {
                    $name {
                        x: self.x,
                        y: self.y,
                        z: $base::one(),
                    }
                }
            }

            fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
                let mut tmp = *bytes;
                let ysign = Choice::from(tmp[31] >> 7);
                tmp[31] &= 0b0111_1111;

                $base::from_bytes(&tmp).and_then(|x| {
                    use crate::util::CtOptionExt1;

                    CtOption::new(Self::zero(), x.is_zero() & (!ysign)).or_else(|| {
                        let x3 = x.square() * x;
                        (x3 + $name::curve_constant_b()).sqrt().and_then(|y| {
                            let sign = Choice::from(y.to_bytes()[0] & 1);

                            let y = $base::conditional_select(&y, &-y, ysign ^ sign);

                            CtOption::new(
                                $name_affine {
                                    x: x,
                                    y: y,
                                    infinity: Choice::from(0u8),
                                },
                                Choice::from(1u8),
                            )
                        })
                    })
                })
            }

            fn to_bytes(&self) -> [u8; 32] {
                // TODO: not constant time
                if bool::from(self.is_zero()) {
                    [0; 32]
                } else {
                    let (x, y) = (self.x, self.y);
                    let sign = (y.to_bytes()[0] & 1) << 7;
                    let mut xbytes = x.to_bytes();
                    xbytes[31] |= sign;
                    xbytes
                }
            }

            fn from_bytes_wide(bytes: &[u8; 64]) -> CtOption<Self> {
                let mut xbytes = [0u8; 32];
                let mut ybytes = [0u8; 32];
                xbytes.copy_from_slice(&bytes[0..32]);
                ybytes.copy_from_slice(&bytes[32..64]);

                $base::from_bytes(&xbytes).and_then(|x| {
                    $base::from_bytes(&ybytes).and_then(|y| {
                        use crate::util::CtOptionExt1;

                        CtOption::new(Self::zero(), x.is_zero() & y.is_zero()).or_else(|| {
                            let on_curve =
                                (x * x.square() + $name::curve_constant_b()).ct_eq(&y.square());

                            CtOption::new(
                                $name_affine {
                                    x: x,
                                    y: y,
                                    infinity: Choice::from(0u8),
                                },
                                Choice::from(on_curve),
                            )
                        })
                    })
                })
            }

            fn to_bytes_wide(&self) -> [u8; 64] {
                // TODO: not constant time
                if bool::from(self.is_zero()) {
                    [0; 64]
                } else {
                    let mut out = [0u8; 64];
                    (&mut out[0..32]).copy_from_slice(&self.x.to_bytes());
                    (&mut out[32..64]).copy_from_slice(&self.y.to_bytes());

                    out
                }
            }
        }

        impl Default for $name_affine {
            fn default() -> $name_affine {
                $name_affine::zero()
            }
        }

        impl ConstantTimeEq for $name_affine {
            fn ct_eq(&self, other: &Self) -> Choice {
                // TODO: infinity should be a Choice
                let z1 = self.infinity;
                let z2 = other.infinity;

                (z1 & z2) | ((!z1) & (!z2) & (self.x.ct_eq(&other.x)) & (self.y.ct_eq(&other.y)))
            }
        }

        impl PartialEq for $name_affine {
            fn eq(&self, other: &Self) -> bool {
                self.ct_eq(other).into()
            }
        }

        impl cmp::Eq for $name_affine {}

        impl ConditionallySelectable for $name_affine {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $name_affine {
                    x: $base::conditional_select(&a.x, &b.x, choice),
                    y: $base::conditional_select(&a.y, &b.y, choice),
                    infinity: Choice::conditional_select(&a.infinity, &b.infinity, choice),
                }
            }
        }
    };
}

new_curve_impl!(Ep, EpAffine, Fp, Fq);
new_curve_impl!(Eq, EqAffine, Fq, Fp);
