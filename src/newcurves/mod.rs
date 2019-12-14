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
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<<Self as Curve>::Scalar, Output = Self>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Add<&'a <Self as Curve>::Affine, Output = Self>
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
    + for<'a> AddAssign<&'a <Self as Curve>::Affine>
    + for<'a> SubAssign<&'a <Self as Curve>::Affine>
    + PartialEq
    + cmp::Eq
    + ConditionallySelectable
    + ConstantTimeEq
    + for<'a> From<&'a <Self as Curve>::Affine>
    + From<<Self as Curve>::Affine>
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

    /// Apply the curve endomorphism by multiplying the x-coordinate
    /// by an element of multiplicative order 3.
    fn endo(&self) -> Self;

    /// Converts this element into its affine form.
    fn to_affine(&self) -> Self::Affine;

    /// Returns whether or not this element is on the curve; should
    /// always be true unless an "unchecked" API was used.
    fn is_on_curve(&self) -> Choice;

    // /// Converts many elements into their affine form. Panics if the
    // /// sizes of the slices are different.
    fn batch_to_affine(v: &[Self], target: &mut [Self::Affine]);

    /// Returns the curve constant b
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
    + Add<Output = <Self as CurveAffine>::Projective>
    + Sub<Output = <Self as CurveAffine>::Projective>
    + Mul<<Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = <Self as CurveAffine>::Projective>
    + for<'a> Sub<&'a Self, Output = <Self as CurveAffine>::Projective>
    + for<'a> Mul<&'a <Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + for<'a> Mul<<Self as CurveAffine>::Scalar, Output = <Self as CurveAffine>::Projective>
    + PartialEq
    + cmp::Eq
    + ConditionallySelectable
    + ConstantTimeEq
    + for<'a> From<&'a <Self as CurveAffine>::Projective>
    + From<<Self as CurveAffine>::Projective>
{
    type Projective: Curve<
        Affine = Self,
        Scalar = <Self as CurveAffine>::Scalar,
        Base = <Self as CurveAffine>::Base,
    >;
    type Scalar: Field;
    type Base: Field;

    /// Obtains the additive identity.
    fn zero() -> Self;

    /// Obtains the base point of the curve.
    fn one() -> Self;

    /// Returns whether or not this element is the identity.
    fn is_zero(&self) -> Choice;

    /// Converts this element into its projective form.
    fn to_projective(&self) -> Self::Projective;

    /// Returns whether or not this element is on the curve; should
    /// always be true unless an "unchecked" API was used.
    fn is_on_curve(&self) -> Choice;

    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;
    fn to_bytes(&self) -> [u8; 32];
    fn from_bytes_wide(bytes: &[u8; 64]) -> CtOption<Self>;
    fn to_bytes_wide(&self) -> [u8; 64];

    /// Returns the curve constant b
    fn b() -> Self::Base;
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
                // TODO/NOTE: this is specific to b = 5
                $base::from_raw([5, 0, 0, 0])
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
                    y: $base::zero(),
                    z: $base::zero(),
                }
            }

            fn one() -> Self {
                // TODO/NOTE: This is specific to b = 5

                const NEGATIVE_ONE: $base = $base::neg(&$base::one());
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
                let zinv = self.z.invert().unwrap_or($base::zero());
                let zinv2 = zinv.square();
                let x = self.x * zinv2;
                let zinv3 = zinv2 * zinv;
                let y = self.y * zinv3;

                let tmp = $name_affine {
                    x,
                    y,
                    infinity: Choice::from(0u8),
                };

                $name_affine::conditional_select(&tmp, &$name_affine::zero(), zinv.is_zero())
            }

            fn double(&self) -> Self {
                // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
                //
                // There are no points of order 2.

                let a = self.x.square();
                let b = self.y.square();
                let c = b.square();
                let d = self.x + b;
                let d = d.square();
                let d = d - a - c;
                let d = d + d;
                let e = a + a + a;
                let f = e.square();
                let z3 = self.z * self.y;
                let z3 = z3 + z3;
                let x3 = f - (d + d);
                let c = c + c;
                let c = c + c;
                let c = c + c;
                let y3 = e * (d - x3) - c;

                let tmp = $name {
                    x: x3,
                    y: y3,
                    z: z3,
                };

                $name::conditional_select(&tmp, &$name::zero(), self.is_zero())
            }

            /// Apply the curve endomorphism by multiplying the x-coordinate
            /// by an element of multiplicative order 3.
            fn endo(&self) -> Self {
                $name {
                    x: self.x * $base::ZETA,
                    y: self.y,
                    z: self.z,
                }
            }

            fn b() -> Self::Base {
                $name::curve_constant_b()
            }

            fn is_on_curve(&self) -> Choice {
                // TODO/NOTE: This is specific to b = 5
                // Y^2 - X^3 = 5(Z^6)

                (self.y.square() - (self.x.square() * self.x))
                    .ct_eq(&((self.z.square() * self.z).square() * $name::curve_constant_b()))
                    | self.z.is_zero()
            }

            fn batch_to_affine(p: &[Self], q: &mut [Self::Affine]) {
                assert_eq!(p.len(), q.len());

                let mut acc = $base::one();
                for (p, q) in p.iter().zip(q.iter_mut()) {
                    // We use the `x` field of $name_affine to store the product
                    // of previous z-coordinates seen.
                    q.x = acc;

                    // We will end up skipping all identities in p
                    acc = $base::conditional_select(&(acc * p.z), &acc, p.is_zero());
                }

                // This is the inverse, as all z-coordinates are nonzero and the ones
                // that are not are skipped.
                acc = acc.invert().unwrap();

                for (p, q) in p.iter().rev().zip(q.iter_mut().rev()) {
                    let skip = p.is_zero();

                    // Compute tmp = 1/z
                    let tmp = q.x * acc;

                    // Cancel out z-coordinate in denominator of `acc`
                    acc = $base::conditional_select(&(acc * p.z), &acc, skip);

                    // Set the coordinates to the correct value
                    let tmp2 = tmp.square();
                    let tmp3 = tmp2 * tmp;

                    q.x = p.x * tmp2;
                    q.y = p.y * tmp3;
                    q.infinity = Choice::from(0u8);

                    *q = $name_affine::conditional_select(&q, &$name_affine::zero(), skip);
                }
            }
        }

        impl<'a> From<&'a $name_affine> for $name {
            fn from(p: &'a $name_affine) -> $name {
                p.to_projective()
            }
        }

        impl From<$name_affine> for $name {
            fn from(p: $name_affine) -> $name {
                p.to_projective()
            }
        }

        impl Default for $name {
            fn default() -> $name {
                $name::zero()
            }
        }

        impl ConstantTimeEq for $name {
            fn ct_eq(&self, other: &Self) -> Choice {
                // Is (xz^2, yz^3, z) equal to (x'z'^2, yz'^3, z') when converted to affine?

                let z = other.z.square();
                let x1 = self.x * z;
                let z = z * other.z;
                let y1 = self.y * z;
                let z = self.z.square();
                let x2 = other.x * z;
                let z = z * self.z;
                let y2 = other.y * z;

                let self_is_zero = self.is_zero();
                let other_is_zero = other.is_zero();

                (self_is_zero & other_is_zero) // Both point at infinity
                            | ((!self_is_zero) & (!other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
                // Neither point at infinity, coordinates are the same
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

        impl<'a> Neg for &'a $name {
            type Output = $name;

            fn neg(self) -> $name {
                $name {
                    x: self.x,
                    y: -self.y,
                    z: self.z,
                }
            }
        }

        impl Neg for $name {
            type Output = $name;

            fn neg(self) -> $name {
                -&self
            }
        }

        impl<'a, 'b> Add<&'a $name> for &'b $name {
            type Output = $name;

            fn add(self, rhs: &'a $name) -> $name {
                // This Jacobian point addition technique is based on the implementation in libsecp256k1,
                // which assumes that rhs has z=1. Let's address the case of zero z-coordinates generally.

                // If self is the identity, return rhs. Otherwise, return self. The other cases will be
                // predicated on neither self nor rhs being the identity.
                let f1 = self.is_zero();
                let res = $name::conditional_select(self, rhs, f1);
                let f2 = rhs.is_zero();

                // If neither are the identity but x1 = x2 and y1 != y2, then return the identity
                let z = rhs.z.square();
                let u1 = self.x * z;
                let z = z * rhs.z;
                let s1 = self.y * z;
                let z = self.z.square();
                let u2 = rhs.x * z;
                let z = z * self.z;
                let s2 = rhs.y * z;
                let f3 = u1.ct_eq(&u2) & (!s1.ct_eq(&s2));
                let res = $name::conditional_select(&res, &$name::zero(), (!f1) & (!f2) & f3);

                let t = u1 + u2;
                let m = s1 + s2;
                let rr = t.square();
                let m_alt = -u2;
                let tt = u1 * m_alt;
                let rr = rr + tt;

                // Correct for x1 != x2 but y1 = -y2, which can occur because p - 1 is divisible by 3.
                // libsecp256k1 does this by substituting in an alternative (defined) expression for lambda.
                let degenerate = m.is_zero() & rr.is_zero();
                let rr_alt = s1 + s1;
                let m_alt = m_alt + u1;
                let rr_alt = $base::conditional_select(&rr_alt, &rr, !degenerate);
                let m_alt = $base::conditional_select(&m_alt, &m, !degenerate);

                let n = m_alt.square();
                let q = n * t;

                let n = n.square();
                let n = $base::conditional_select(&n, &m, degenerate);
                let t = rr_alt.square();
                let z3 = m_alt * self.z * rhs.z; // We allow rhs.z != 1, so we must account for this.
                let z3 = z3 + z3;
                let q = -q;
                let t = t + q;
                let x3 = t;
                let t = t + t;
                let t = t + q;
                let t = t * rr_alt;
                let t = t + n;
                let y3 = -t;
                let x3 = x3 + x3;
                let x3 = x3 + x3;
                let y3 = y3 + y3;
                let y3 = y3 + y3;

                let tmp = $name {
                    x: x3,
                    y: y3,
                    z: z3,
                };

                $name::conditional_select(&res, &tmp, (!f1) & (!f2) & (!f3))
            }
        }

        impl<'a, 'b> Add<&'a $name_affine> for &'b $name {
            type Output = $name;

            fn add(self, rhs: &'a $name_affine) -> $name {
                // This Jacobian point addition technique is based on the implementation in libsecp256k1,
                // which assumes that rhs has z=1. Let's address the case of zero z-coordinates generally.

                // If self is the identity, return rhs. Otherwise, return self. The other cases will be
                // predicated on neither self nor rhs being the identity.
                let f1 = self.is_zero();
                let res = $name::conditional_select(self, &$name::from(rhs), f1);
                let f2 = rhs.is_zero();

                // If neither are the identity but x1 = x2 and y1 != y2, then return the identity
                let u1 = self.x;
                let s1 = self.y;
                let z = self.z.square();
                let u2 = rhs.x * z;
                let z = z * self.z;
                let s2 = rhs.y * z;
                let f3 = u1.ct_eq(&u2) & (!s1.ct_eq(&s2));
                let res = $name::conditional_select(&res, &$name::zero(), (!f1) & (!f2) & f3);

                let t = u1 + u2;
                let m = s1 + s2;
                let rr = t.square();
                let m_alt = -u2;
                let tt = u1 * m_alt;
                let rr = rr + tt;

                // Correct for x1 != x2 but y1 = -y2, which can occur because p - 1 is divisible by 3.
                // libsecp256k1 does this by substituting in an alternative (defined) expression for lambda.
                let degenerate = m.is_zero() & rr.is_zero();
                let rr_alt = s1 + s1;
                let m_alt = m_alt + u1;
                let rr_alt = $base::conditional_select(&rr_alt, &rr, !degenerate);
                let m_alt = $base::conditional_select(&m_alt, &m, !degenerate);

                let n = m_alt.square();
                let q = n * t;

                let n = n.square();
                let n = $base::conditional_select(&n, &m, degenerate);
                let t = rr_alt.square();
                let z3 = m_alt * self.z;
                let z3 = z3 + z3;
                let q = -q;
                let t = t + q;
                let x3 = t;
                let t = t + t;
                let t = t + q;
                let t = t * rr_alt;
                let t = t + n;
                let y3 = -t;
                let x3 = x3 + x3;
                let x3 = x3 + x3;
                let y3 = y3 + y3;
                let y3 = y3 + y3;

                let tmp = $name {
                    x: x3,
                    y: y3,
                    z: z3,
                };

                $name::conditional_select(&res, &tmp, (!f1) & (!f2) & (!f3))
            }
        }

        impl<'a, 'b> Sub<&'a $name> for &'b $name {
            type Output = $name;

            fn sub(self, other: &'a $name) -> $name {
                self + (-other)
            }
        }

        impl<'a, 'b> Sub<&'a $name_affine> for &'b $name {
            type Output = $name;

            fn sub(self, other: &'a $name_affine) -> $name {
                self + (-other)
            }
        }

        impl<'a, 'b> Mul<&'b $scalar> for &'a $name {
            type Output = $name;

            fn mul(self, other: &'b $scalar) -> Self::Output {
                // TODO: make this faster

                let mut acc = $name::zero();

                // This is a simple double-and-add implementation of point
                // multiplication, moving from most significant to least
                // significant bit of the scalar.
                //
                // TODO/NOTE: We skip the leading bit because it's always unset.
                for bit in other
                    .to_bytes()
                    .iter()
                    .rev()
                    .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
                    .skip(1)
                {
                    acc = acc.double();
                    acc = $name::conditional_select(&acc, &(acc + self), bit);
                }

                acc
            }
        }

        impl<'a> Neg for &'a $name_affine {
            type Output = $name_affine;

            fn neg(self) -> $name_affine {
                $name_affine {
                    x: self.x,
                    y: -self.y,
                    infinity: self.infinity,
                }
            }
        }

        impl Neg for $name_affine {
            type Output = $name_affine;

            fn neg(self) -> $name_affine {
                -&self
            }
        }

        impl<'a, 'b> Add<&'a $name> for &'b $name_affine {
            type Output = $name;

            fn add(self, rhs: &'a $name) -> $name {
                rhs + self
            }
        }

        impl<'a, 'b> Add<&'a $name_affine> for &'b $name_affine {
            type Output = $name;

            fn add(self, rhs: &'a $name_affine) -> $name {
                // This Jacobian point addition technique is based on the implementation in libsecp256k1,
                // which assumes that rhs has z=1. Let's address the case of zero z-coordinates generally.

                // If self is the identity, return rhs. Otherwise, return self. The other cases will be
                // predicated on neither self nor rhs being the identity.
                let f1 = self.is_zero();
                let res = $name::conditional_select(&self.to_projective(), &$name::from(rhs), f1);
                let f2 = rhs.is_zero();

                // If neither are the identity but x1 = x2 and y1 != y2, then return the identity
                let f3 = self.x.ct_eq(&rhs.x) & (!self.y.ct_eq(&rhs.y));
                let res = $name::conditional_select(&res, &$name::zero(), (!f1) & (!f2) & f3);

                let t = self.x + rhs.x;
                let m = self.y + rhs.y;
                let rr = t.square();
                let m_alt = -rhs.x;
                let tt = self.x * m_alt;
                let rr = rr + tt;

                // Correct for x1 != x2 but y1 = -y2, which can occur because p - 1 is divisible by 3.
                // libsecp256k1 does this by substituting in an alternative (defined) expression for lambda.
                let degenerate = m.is_zero() & rr.is_zero();
                let rr_alt = self.y + self.y;
                let m_alt = m_alt + self.x;
                let rr_alt = $base::conditional_select(&rr_alt, &rr, !degenerate);
                let m_alt = $base::conditional_select(&m_alt, &m, !degenerate);

                let n = m_alt.square();
                let q = n * t;

                let n = n.square();
                let n = $base::conditional_select(&n, &m, degenerate);
                let t = rr_alt.square();
                let z3 = m_alt;
                let z3 = z3 + z3;
                let q = -q;
                let t = t + q;
                let x3 = t;
                let t = t + t;
                let t = t + q;
                let t = t * rr_alt;
                let t = t + n;
                let y3 = -t;
                let x3 = x3 + x3;
                let x3 = x3 + x3;
                let y3 = y3 + y3;
                let y3 = y3 + y3;

                let tmp = $name {
                    x: x3,
                    y: y3,
                    z: z3,
                };

                $name::conditional_select(&res, &tmp, (!f1) & (!f2) & (!f3))
            }
        }

        impl<'a, 'b> Sub<&'a $name_affine> for &'b $name_affine {
            type Output = $name;

            fn sub(self, other: &'a $name_affine) -> $name {
                self + (-other)
            }
        }

        impl<'a, 'b> Sub<&'a $name> for &'b $name_affine {
            type Output = $name;

            fn sub(self, other: &'a $name) -> $name {
                self + (-other)
            }
        }

        impl<'a, 'b> Mul<&'b $scalar> for &'a $name_affine {
            type Output = $name;

            fn mul(self, other: &'b $scalar) -> Self::Output {
                // TODO: make this faster

                let mut acc = $name::zero();

                // This is a simple double-and-add implementation of point
                // multiplication, moving from most significant to least
                // significant bit of the scalar.
                //
                // TODO/NOTE: We skip the leading bit because it's always unset.
                for bit in other
                    .to_bytes()
                    .iter()
                    .rev()
                    .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
                    .skip(1)
                {
                    acc = acc.double();
                    acc = $name::conditional_select(&acc, &(acc + self), bit);
                }

                acc
            }
        }

        impl CurveAffine for $name_affine {
            type Projective = $name;
            type Scalar = $scalar;
            type Base = $base;

            fn zero() -> Self {
                Self {
                    x: $base::zero(),
                    y: $base::zero(),
                    infinity: Choice::from(1u8),
                }
            }

            fn one() -> Self {
                // TODO/NOTE: This is specific to b = 5

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

            fn is_on_curve(&self) -> Choice {
                // TODO/NOTE: This is specific to b = 5

                // y^2 - x^3 ?= 5
                (self.y.square() - (self.x.square() * self.x)).ct_eq(&$name::curve_constant_b())
                    | self.infinity
            }

            fn to_projective(&self) -> Self::Projective {
                $name {
                    x: self.x,
                    y: self.y,
                    z: $base::conditional_select(&$base::one(), &$base::zero(), self.infinity),
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

            fn b() -> Self::Base {
                $name::curve_constant_b()
            }
        }

        impl Default for $name_affine {
            fn default() -> $name_affine {
                $name_affine::zero()
            }
        }

        impl<'a> From<&'a $name> for $name_affine {
            fn from(p: &'a $name) -> $name_affine {
                p.to_affine()
            }
        }

        impl From<$name> for $name_affine {
            fn from(p: $name) -> $name_affine {
                p.to_affine()
            }
        }

        impl ConstantTimeEq for $name_affine {
            fn ct_eq(&self, other: &Self) -> Choice {
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

        impl_binops_additive!($name, $name);
        impl_binops_additive!($name, $name_affine);
        impl_binops_additive_specify_output!($name_affine, $name_affine, $name);
        impl_binops_additive_specify_output!($name_affine, $name, $name);
        impl_binops_multiplicative!($name, $scalar);
        impl_binops_multiplicative_mixed!($name_affine, $scalar, $name);
    };
}

new_curve_impl!(Ep, EpAffine, Fp, Fq);
new_curve_impl!(Eq, EqAffine, Fq, Fp);

#[test]
fn test_on_curve() {
    let a = Ep::one();
    assert!(bool::from(a.is_on_curve()));
    let b = a * <Fq as Field>::ZETA;
    assert!(bool::from(b.is_on_curve()));
}

#[test]
fn test_endo_consistency() {
    let a = Ep::one();
    assert_eq!(a.endo(), a * <Fq as Field>::ZETA);
    let a = Eq::one();
    assert_eq!(a.endo(), a * <Fp as Field>::ZETA);
}

#[test]
fn test_consistent_values() {
    let a = Ep::one() * <Fq as Field>::ZETA;
    let b = EpAffine::one() * <Fq as Field>::ZETA;
    assert_eq!(a, b);

    let a = Ep::one() + EpAffine::one();
    let b = EpAffine::one() + EpAffine::one();
    let c = Ep::one() + Ep::one();
    let d = Ep::one().double();

    assert_eq!(a, b);
    assert_eq!(b, c);
    assert_eq!(c, d);

    let a = Ep::one() - EpAffine::one();
    let b = EpAffine::one() - EpAffine::one();
    assert_eq!(a, b);
    assert!(bool::from(a.is_zero()));
}
