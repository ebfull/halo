use super::AllocatedNum;
use super::{AllocatedBit, Boolean, Num};
use crate::{
    circuits::{Coeff, ConstraintSystem, LinearCombination, SynthesisError},
    fields::Field,
    Curve,
};
use subtle::CtOption;

/// A curve point. It is either the identity, or a valid curve point.
///
/// Internally it is represented either with coordinates that satisfy the
/// curve equation, or (0, 0). We also maintain a [`Boolean`] tracking whether
/// it is the identity.
#[derive(Debug, Clone)]
pub struct CurvePoint<C: Curve> {
    x: Num<C::Base>,
    y: Num<C::Base>,

    /// Whether or not this curve point actually represents the identity.
    is_identity: Boolean,
}

impl<C: Curve> CurvePoint<C> {
    /// Create a constant that is the identity.
    pub fn identity() -> Self {
        // Represent the identity internally as (0, 0).
        CurvePoint {
            x: Num::constant(C::Base::zero()),
            y: Num::constant(C::Base::zero()),
            is_identity: Boolean::constant(true),
        }
    }

    /// Create a constant that is assumed to not be the identity.
    pub fn constant(x: C::Base, y: C::Base) -> Self {
        CurvePoint {
            x: Num::constant(x),
            y: Num::constant(y),
            is_identity: Boolean::constant(false),
        }
    }

    /// Witness an arbitrary curve point
    pub fn witness<CS, P>(cs: &mut CS, point: P) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<C::Base>,
        P: FnOnce() -> Result<C, SynthesisError>,
    {
        // If get_xy returns None, then the point is the identity, so represent
        // it internally as (0, 0).
        let point = point().map(|p| {
            let coords = p.get_xy();
            if coords.is_some().into() {
                let (x, y) = coords.unwrap();
                (x, y, false)
            } else {
                (C::Base::zero(), C::Base::zero(), true)
            }
        });
        let x_val = point.map(|(x, _, _)| x);
        let y_val = point.map(|(_, y, _)| y);
        let is_identity_val = point.map(|(_, _, b)| b);

        // Curve equation is y^2 = x^3 + B
        // As constraints:
        //
        // a * b = c
        // a = y
        // b = y
        // c := y^2
        //
        // d * e = f
        // d = x
        // e = x
        // f := x^2
        //
        // g * h = i
        // g = f
        // h = x
        // i := x^3
        //
        // j * k = l
        // j = i + B - c
        // k = (1 - is_identity)
        // l = 0

        let ysq = y_val.map(|y| y * &y);
        let xsq = x_val.map(|x| x * &x);
        let xcub = xsq.and_then(|xsq| x_val.map(|x| xsq * &x));

        let x = AllocatedNum::alloc(cs, || x_val)?;
        let y = AllocatedNum::alloc(cs, || y_val)?;
        let is_identity = AllocatedBit::alloc(cs, || is_identity_val)?;

        // let (x, y) = C::one().get_xy().unwrap();
        // return Ok(Self::constant(x, y));

        let (a_var, b_var, c_var) = cs.multiply(|| Ok((y_val?, y_val?, ysq?)))?;
        cs.enforce_zero(y.lc() - a_var);
        cs.enforce_zero(y.lc() - b_var);

        let (d_var, e_var, f_var) = cs.multiply(|| Ok((x_val?, x_val?, xsq?)))?;
        cs.enforce_zero(x.lc() - d_var);
        cs.enforce_zero(x.lc() - e_var);

        let (g_var, h_var, i_var) = cs.multiply(|| Ok((xsq?, x_val?, xcub?)))?;
        cs.enforce_zero(LinearCombination::from(f_var) - g_var);
        cs.enforce_zero(x.lc() - h_var);

        let (j_var, k_var, l_var) = cs.multiply(|| {
            let is_not_identity = if !is_identity_val? {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((xcub? + &C::b() - &ysq?, is_not_identity, C::Base::zero()))
        })?;
        cs.enforce_zero(
            LinearCombination::from(i_var) + (Coeff::Full(C::b()), CS::ONE) - c_var - j_var,
        );
        cs.enforce_zero(
            LinearCombination::zero() + (Coeff::One, CS::ONE) - is_identity.get_variable() - k_var,
        );
        cs.enforce_zero(LinearCombination::from(l_var));

        Ok(CurvePoint {
            x: Num::from(x),
            y: Num::from(y),
            is_identity: is_identity.into(),
        })
    }

    /// Returns Some(None) if this is the identity, and Some(point) otherwise.
    fn get_point(&self) -> Option<CtOption<C>> {
        match (self.x.value(), self.y.value(), self.is_identity.get_value()) {
            (Some(x), Some(y), Some(is_identity)) => Some(if is_identity {
                CtOption::new(C::zero(), 0.into())
            } else {
                C::from_xy(x, y)
            }),
            _ => None,
        }
    }

    /// Returns variables constrained to (0, 0) if this is the identity, and
    /// (x, y) otherwise.
    pub fn get_xy<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
    ) -> Result<(Num<C::Base>, Num<C::Base>), SynthesisError> {
        // We represent the identity internally as (0, 0), so we can just return
        // (x, y).
        Ok((self.x, self.y))
    }

    /// Adds a point to another point.
    ///
    /// Handles all edge cases.
    pub fn add<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let x1 = self.x;
        let y1 = self.y;
        let x1_val = x1.value();
        let y1_val = y1.value();

        let x2 = other.x;
        let y2 = other.y;
        let x2_val = x2.value();
        let y2_val = y2.value();

        let p1_val = x1_val.and_then(|x| y1_val.map(|y| C::from_xy(x, y).unwrap()));
        let p2_val = x2_val.and_then(|x| y2_val.map(|y| C::from_xy(x, y).unwrap()));
        let p3_val = p1_val.and_then(|p1| p2_val.map(|p2| (p1 + p2)));

        // If get_xy returns None, then the sum is the identity, so represent
        // it internally as C::one() which does satisfy the curve equation.
        let (x3_val, y3_val, p3_is_identity_val) = match p3_val {
            Some(p) => {
                let coords = p.get_xy();
                if coords.is_some().into() {
                    let (x, y) = coords.unwrap();
                    (Some(x), Some(y), Some(false))
                } else {
                    let (x, y) = C::one().get_xy().unwrap();
                    (Some(x), Some(y), Some(true))
                }
            }
            None => (None, None, None),
        };

        let x3 = AllocatedNum::alloc(cs, || x3_val.ok_or(SynthesisError::AssignmentMissing))?;
        let y3 = AllocatedNum::alloc(cs, || y3_val.ok_or(SynthesisError::AssignmentMissing))?;
        let p3_is_identity = AllocatedBit::alloc(cs, || {
            p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Output conditions:
        //
        // - If self.is_identity is true, return other
        // - If self.is_identity is false:
        //   - If other.is_identity is true, return self
        //   - If other.is_identity is false, return self + other

        let p1_is_identity_val = self.is_identity.get_value();
        let p2_is_identity_val = other.is_identity.get_value();

        let (x_out_val, y_out_val, out_is_identity_val) =
            match (p1_is_identity_val, p2_is_identity_val) {
                (Some(true), Some(_)) => (x2_val, y2_val, p2_is_identity_val),
                (Some(false), Some(true)) => (x1_val, y1_val, p1_is_identity_val),
                (Some(false), Some(false)) => (x3_val, y3_val, p3_is_identity_val),
                _ => (None, None, None),
            };

        let x_out = AllocatedNum::alloc(cs, || x_out_val.ok_or(SynthesisError::AssignmentMissing))?;
        let y_out = AllocatedNum::alloc(cs, || y_out_val.ok_or(SynthesisError::AssignmentMissing))?;
        let out_is_identity = AllocatedBit::alloc(cs, || {
            out_is_identity_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let x1_lc = x1.lc(cs);
        let y1_lc = y1.lc(cs);
        let x2_lc = x2.lc(cs);
        let y2_lc = y2.lc(cs);

        // Complete affine addition for y^3 = x^2 + b:
        //
        // p1 != p2:
        //   lambda = (y2 - y1) / (x2 - x1)
        //   x3 = lambda^2 - x1 - x2
        //   y3 = -lambda x3 + lambda x1 - y1
        //
        // p1 == p2:
        //   lambda = (3 (x1)^2) / (2 y1)
        //   x3 = lambda^2 - 2 x1 = lambda^2 - x1 - x2
        //   y3 = -lambda x3 + lambda x1 - y1
        //
        // So we can handle both cases by including a selection constraint:
        //   (x2 - x1) * is_same = 0
        //     --> if different, is_same must be 0
        //
        //   (x2 - x1) * (x2 - x1)^-1 = (1 - is_same)
        //     --> if the same, is_same must be 1
        //
        //   (lambda - lambda_diff) = is_same * (lambda_same - lambda_diff)
        //
        // In R1CS:
        //
        // x1 * x1 = (x1)^2
        // (x2 - x1) * lambda_diff = (y2 - y1)
        // (2 y1) * lambda_same = 3 (x1)^2
        // (x2 - x1) * is_same = 0
        // (x2 - x1) * (x2 - x1)^-1 = (1 - is_same)
        // (lambda - lambda_diff) = is_same * (lambda_same - lambda_diff)
        // lambda * lambda = x1 + x2 + x3
        // (x1 - x3) * lambda = y1 + y3
        //
        // This is complete in the sense that it handles p1 = p2. However,
        // because we represent the identity internally by C::one(), we need to
        // additionally handle the following edge cases:
        //
        // p1 = identity --> p_out = p2
        // p1 != identity && p2 = identity --> p_out = p1
        // p1 != identity && p2 != identity && p3 = identity (p2 = -p1) --> p_out = C::one() := (1X, 1Y)
        // p1 != identity && p2 != identity && p3 != identity --> p_out = p3
        //
        // x_out = x2 *      p1_is_identity
        //       + x1 * (1 - p1_is_identity) *      p2_is_identity
        //       + 1X * (1 - p1_is_identity) * (1 - p2_is_identity) *      p3_is_identity
        //       + x3 * (1 - p1_is_identity) * (1 - p2_is_identity) * (1 - p3_is_identity)
        //
        // y_out = y2 *      p1_is_identity
        //       + y1 * (1 - p1_is_identity) *      p2_is_identity
        //       + 1Y * (1 - p1_is_identity) * (1 - p2_is_identity) *      p3_is_identity
        //       + y3 * (1 - p1_is_identity) * (1 - p2_is_identity) * (1 - p3_is_identity)
        //
        // out_is_identity = p2_is_identity *      p1_is_identity
        //                 + p1_is_identity * (1 - p1_is_identity) *      p2_is_identity
        //                 + true           * (1 - p1_is_identity) * (1 - p2_is_identity) *      p3_is_identity
        //                 + p3_is_identity * (1 - p1_is_identity) * (1 - p2_is_identity) * (1 - p3_is_identity)
        //
        //                 = p2_is_identity * p1_is_identity
        //                 + (1 - p1_is_identity) * (1 - p2_is_identity) * p3_is_identity
        //
        // As constraints:
        //
        // mid_a =      p1_is_identity  *      p2_is_identity
        // mid_b = (1 - p1_is_identity) *      p2_is_identity
        // mid_c = (1 - p1_is_identity) * (1 - p2_is_identity)
        // mid_d = mid_c *      p3_is_identity
        // mid_e = mid_c * (1 - p3_is_identity)
        //
        // x_out = x2 * p1_is_identity
        //       + x1 * mid_b
        //       + 1X * mid_d
        //       + x3 * mid_e
        // y_out = y2 * p1_is_identity
        //       + y1 * mid_b
        //       + 1Y * mid_d
        //       + y3 * mid_e
        // out_is_identity - mid_a = mid_d

        // x1 * x1 = (x1)^2
        // a * b = c
        // a = x1
        // b = x1
        // c := x1^2

        let x1_sq = x1_val.map(|x| x * &x);

        let (a_var, b_var, c_var) = cs.multiply(|| {
            let x = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let xsq = x1_sq.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x, x, xsq))
        })?;
        cs.enforce_zero(x1_lc.clone() - a_var);
        cs.enforce_zero(x1_lc.clone() - b_var);

        // (x2 - x1) * lambda_diff = (y2 - y1)
        // d * e = f
        // d = x2 - x1
        // e := lambda_diff
        // f = y2 - y1

        let d_val = x1_val.and_then(|x1| x2_val.map(|x2| x2 - &x1));
        let f_val = y1_val.and_then(|y1| y2_val.map(|y2| y2 - &y1));
        let e_val = d_val.and_then(|x2mx1| {
            f_val.map(|y2my1| {
                let inv = x2mx1.invert();
                if inv.is_some().into() {
                    inv.unwrap() * &y2my1
                } else {
                    // lambda_diff is unconstrained
                    C::Base::one()
                }
            })
        });

        let (d_var, e_var, f_var) = cs.multiply(|| {
            let x2mx1 = d_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y2my1 = f_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_diff = e_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x2mx1, lambda_diff, y2my1))
        })?;
        cs.enforce_zero(x2_lc.clone() - &x1_lc - d_var);
        cs.enforce_zero(y2_lc.clone() - &y1_lc - f_var);

        // (2 y1) * lambda_same = 3 (x1)^2
        // g * h = i
        // g = 2 y1
        // h: lambda_same
        // i = 3 c = 3 x1^2

        let g_val = y1_val.map(|y1| y1 + &y1);
        let i_val = x1_sq.map(|x1sq| x1sq + &x1sq + &x1sq);
        let h_val = g_val.and_then(|y1two| {
            i_val.map(|x1sq3| {
                let inv = y1two.invert();
                if inv.is_some().into() {
                    inv.unwrap() * &x1sq3
                } else {
                    // lambda_same is unconstrained
                    C::Base::one()
                }
            })
        });

        let (g_var, h_var, i_var) = cs.multiply(|| {
            let y1two = g_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1sq3 = i_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_same = h_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y1two, lambda_same, x1sq3))
        })?;
        cs.enforce_zero(y1_lc.clone() + &y1_lc - g_var);
        cs.enforce_zero(
            LinearCombination::zero() + (Coeff::Full(C::Base::from_u64(3)), c_var) - i_var,
        );

        // lambda * lambda = x1 + x2 + x3
        // j * k = l
        // j := lambda
        // k = j
        // l = x1 + x2 + x3
        //
        // Constrain this here so we have a variable for lambda

        let lambda_val = d_val.and_then(|x2mx1| if x2mx1.is_zero().into() { h_val } else { e_val });

        let (j_var, k_var, l_var) = cs.multiply(|| {
            let lambda = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1 = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x2 = x2_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x3 = x3_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda, lambda, x1 + &x2 + &x3))
        })?;
        cs.enforce_zero(LinearCombination::from(j_var) - k_var);
        cs.enforce_zero(x1_lc.clone() + &x2_lc + &x3.lc() - l_var);

        // (x2 - x1) * is_same = 0
        // m * n = o
        // m = d = x2 - x1
        // n := is_same
        // o = 0

        let is_same_val = d_val.map(|x2mx1| {
            if x2mx1.is_zero().into() {
                C::Base::one()
            } else {
                C::Base::zero()
            }
        });

        let (m_var, n_var, o_var) = cs.multiply(|| {
            let x2mx1 = d_val.ok_or(SynthesisError::AssignmentMissing)?;
            let is_same = is_same_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x2mx1, is_same, C::Base::zero()))
        })?;
        cs.enforce_zero(LinearCombination::from(d_var) - m_var);
        cs.enforce_zero(LinearCombination::from(o_var));

        // (x2 - x1) * (x2 - x1)^-1 = (1 - is_same)
        // p * q = r
        // p = d = x2 - x1
        // q := d^-1
        // r = (1 - is_same)

        let dinv_val = d_val.map(|x2mx1| {
            let inv = x2mx1.invert();
            if inv.is_some().into() {
                inv.unwrap()
            } else {
                // dinv is unconstrained
                C::Base::one()
            }
        });

        let (p_var, q_var, r_var) = cs.multiply(|| {
            let x2mx1 = d_val.ok_or(SynthesisError::AssignmentMissing)?;
            let dinv = dinv_val.ok_or(SynthesisError::AssignmentMissing)?;
            let is_same = is_same_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x2mx1, dinv, C::Base::one() - &is_same))
        })?;
        cs.enforce_zero(LinearCombination::from(d_var) - p_var);
        cs.enforce_zero(LinearCombination::zero() + (Coeff::One, CS::ONE) - n_var - r_var);

        // (lambda - lambda_diff) = is_same * (lambda_same - lambda_diff)
        // s * t = u
        // s = n
        // t = h - e
        // u = j - e

        let (s_var, t_var, u_var) = cs.multiply(|| {
            let is_same = is_same_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_diff = e_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_same = h_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((is_same, lambda_same - &lambda_diff, lambda - &lambda_diff))
        })?;
        cs.enforce_zero(LinearCombination::from(n_var) - s_var);
        cs.enforce_zero(LinearCombination::from(h_var) - e_var - t_var);
        cs.enforce_zero(LinearCombination::from(j_var) - e_var - u_var);

        // (x1 - x3) * lambda = y1 + y3
        // v * w = x
        // v = x1 - x3
        // w = j
        // x = y1 + y3

        let (v_var, w_var, x_var) = cs.multiply(|| {
            let lambda = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1 = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x3 = x3_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y1 = y1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y3 = y3_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x1 - &x3, lambda, y1 + &y3))
        })?;
        cs.enforce_zero(x1_lc.clone() - &x3.lc() - v_var);
        cs.enforce_zero(LinearCombination::from(j_var) - w_var);
        cs.enforce_zero(y1_lc.clone() + &y3.lc() - x_var);

        // mid_a = p1_is_identity * p2_is_identity
        let mid_a_val = p1_is_identity_val.and_then(|p1| {
            p2_is_identity_val.map(|p2| match (p1, p2) {
                (true, true) => C::Base::one(),
                _ => C::Base::zero(),
            })
        });

        let (y_var, z_var, mid_a) = cs.multiply(|| {
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p2_is_identity = p2_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_a = mid_a_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p1_is_identity = if p1_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };
            let p2_is_identity = if p2_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((p1_is_identity, p2_is_identity, mid_a))
        })?;
        cs.enforce_zero(self.is_identity.lc(CS::ONE, Coeff::One) - y_var);
        cs.enforce_zero(other.is_identity.lc(CS::ONE, Coeff::One) - z_var);

        // mid_b = (1 - p1_is_identity) * p2_is_identity
        let mid_b_val = p1_is_identity_val.and_then(|p1| {
            p2_is_identity_val.map(|p2| match (p1, p2) {
                (false, true) => C::Base::one(),
                _ => C::Base::zero(),
            })
        });

        let (aa_var, bb_var, mid_b) = cs.multiply(|| {
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p2_is_identity = p2_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_b = mid_b_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p1_is_not_identity = if !p1_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };
            let p2_is_identity = if p2_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((p1_is_not_identity, p2_is_identity, mid_b))
        })?;
        cs.enforce_zero(self.is_identity.not().lc(CS::ONE, Coeff::One) - aa_var);
        cs.enforce_zero(other.is_identity.lc(CS::ONE, Coeff::One) - bb_var);

        // mid_c = (1 - p1_is_identity) * (1 - p2_is_identity)
        let mid_c_val = p1_is_identity_val.and_then(|p1| {
            p2_is_identity_val.map(|p2| match (p1, p2) {
                (false, false) => C::Base::one(),
                _ => C::Base::zero(),
            })
        });

        let (cc_var, dd_var, mid_c) = cs.multiply(|| {
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p2_is_identity = p2_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_c = mid_c_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p1_is_not_identity = if !p1_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };
            let p2_is_not_identity = if !p2_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((p1_is_not_identity, p2_is_not_identity, mid_c))
        })?;
        cs.enforce_zero(self.is_identity.not().lc(CS::ONE, Coeff::One) - cc_var);
        cs.enforce_zero(other.is_identity.not().lc(CS::ONE, Coeff::One) - dd_var);

        // mid_d = mid_c * p3_is_identity
        let mid_d_val = mid_c_val.and_then(|mid_c| {
            p3_is_identity_val.map(|p3| if p3 { mid_c } else { C::Base::zero() })
        });

        let (ee_var, ff_var, mid_d) = cs.multiply(|| {
            let mid_c = mid_c_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_d = mid_d_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p3_is_identity = p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p3_is_identity = if p3_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((mid_c, p3_is_identity, mid_d))
        })?;
        cs.enforce_zero(LinearCombination::from(mid_c) - ee_var);
        cs.enforce_zero(LinearCombination::from(p3_is_identity.get_variable()) - ff_var);

        // mid_e = mid_c * (1 - p3_is_identity)
        let mid_e_val = mid_c_val.and_then(|mid_c| {
            p3_is_identity_val.map(|p3| if !p3 { mid_c } else { C::Base::zero() })
        });

        let (gg_var, hh_var, mid_e) = cs.multiply(|| {
            let mid_c = mid_c_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_e = mid_e_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p3_is_identity = p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p3_is_not_identity = if !p3_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((mid_c, p3_is_not_identity, mid_e))
        })?;
        cs.enforce_zero(LinearCombination::from(mid_c) - gg_var);
        cs.enforce_zero(
            LinearCombination::zero() + (Coeff::One, CS::ONE)
                - p3_is_identity.get_variable()
                - hh_var,
        );

        // x_out = x2 * p1_is_identity
        //       + x1 * mid_b
        //       + 1X * mid_d
        //       + x3 * mid_e

        // x2 * p1_is_identity
        let (ii_var, jj_var, x2_p1_var) = cs.multiply(|| {
            let x2 = x2_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p1_is_identity = if p1_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((x2, p1_is_identity, x2 * &p1_is_identity))
        })?;
        cs.enforce_zero(x2_lc - ii_var);
        cs.enforce_zero(self.is_identity.lc(CS::ONE, Coeff::One) - jj_var);

        // x1 * mid_b
        let (kk_var, ll_var, x1_mid_b_var) = cs.multiply(|| {
            let x1 = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_b = mid_b_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x1, mid_b, x1 * &mid_b))
        })?;
        cs.enforce_zero(x1_lc - kk_var);
        cs.enforce_zero(LinearCombination::from(mid_b) - ll_var);

        // 1X * mid_d
        let (mm_var, nn_var, one_x_mid_d_var) = cs.multiply(|| {
            let mid_d = mid_d_val.ok_or(SynthesisError::AssignmentMissing)?;
            let one_x = C::one().get_xy().unwrap().0;

            Ok((one_x, mid_d, one_x * &mid_d))
        })?;
        let one_x_lc = Num::constant(C::one().get_xy().unwrap().0).lc(cs);
        cs.enforce_zero(one_x_lc - mm_var);
        cs.enforce_zero(LinearCombination::from(mid_d) - nn_var);

        // x3 * mid_e
        let (oo_var, pp_var, x3_mid_e_var) = cs.multiply(|| {
            let x3 = x3_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_e = mid_e_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x3, mid_e, x3 * &mid_e))
        })?;
        cs.enforce_zero(x3.lc() - oo_var);
        cs.enforce_zero(LinearCombination::from(mid_e) - pp_var);

        cs.enforce_zero(
            LinearCombination::zero() + x2_p1_var + x1_mid_b_var + one_x_mid_d_var + x3_mid_e_var
                - &x_out.lc(),
        );

        // y_out = y2 * p1_is_identity
        //       + y1 * mid_b
        //       + 1Y * mid_d
        //       + y3 * mid_e

        // y2 * p1_is_identity
        let (qq_var, rr_var, y2_p1_var) = cs.multiply(|| {
            let y2 = y2_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            let p1_is_identity = if p1_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((y2, p1_is_identity, y2 * &p1_is_identity))
        })?;
        cs.enforce_zero(y2_lc - qq_var);
        cs.enforce_zero(self.is_identity.lc(CS::ONE, Coeff::One) - rr_var);

        // y1 * mid_b
        let (ss_var, tt_var, y1_mid_b_var) = cs.multiply(|| {
            let y1 = y1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_b = mid_b_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y1, mid_b, y1 * &mid_b))
        })?;
        cs.enforce_zero(y1_lc - ss_var);
        cs.enforce_zero(LinearCombination::from(mid_b) - tt_var);

        // 1Y * mid_d
        let (uu_var, vv_var, one_y_mid_d_var) = cs.multiply(|| {
            let mid_d = mid_d_val.ok_or(SynthesisError::AssignmentMissing)?;
            let one_y = C::one().get_xy().unwrap().1;

            Ok((one_y, mid_d, one_y * &mid_d))
        })?;
        let one_y_lc = Num::constant(C::one().get_xy().unwrap().1).lc(cs);
        cs.enforce_zero(one_y_lc - uu_var);
        cs.enforce_zero(LinearCombination::from(mid_d) - vv_var);

        // y3 * mid_e
        let (ww_var, xx_var, y3_mid_e_var) = cs.multiply(|| {
            let y3 = y3_val.ok_or(SynthesisError::AssignmentMissing)?;
            let mid_e = mid_e_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y3, mid_e, y3 * &mid_e))
        })?;
        cs.enforce_zero(y3.lc() - ww_var);
        cs.enforce_zero(LinearCombination::from(mid_e) - xx_var);

        cs.enforce_zero(
            LinearCombination::zero() + y2_p1_var + y1_mid_b_var + one_y_mid_d_var + y3_mid_e_var
                - &y_out.lc(),
        );

        // out_is_identity - mid_a = mid_d
        cs.enforce_zero(LinearCombination::from(out_is_identity.get_variable()) - mid_a - mid_d);

        Ok(CurvePoint {
            x: x_out.into(),
            y: y_out.into(),
            is_identity: out_is_identity.into(),
        })
    }

    /// Adds `self` to `other`, returning the result unless
    /// condition is false, in which case it returns `self`.
    ///
    /// Handles all edge cases.
    pub fn add_conditionally<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        // Output conditions:
        //
        // - If condition is false, return self
        // - If condition is true, return self + other

        let sum = self.add(cs, other)?;

        let x1 = self.x;
        let y1 = self.y;

        let xsum = sum.x;
        let ysum = sum.y;

        let self_is_identity_val = self.is_identity.get_value();
        let sum_is_identity_val = sum.is_identity.get_value();

        let bit_val = condition.get_value();

        let (x_out_val, y_out_val, out_is_identity_val) = match bit_val {
            Some(true) => (xsum.value(), ysum.value(), sum_is_identity_val),
            Some(false) => (x1.value(), y1.value(), self_is_identity_val),
            _ => (None, None, None),
        };

        let x_out = AllocatedNum::alloc(cs, || x_out_val.ok_or(SynthesisError::AssignmentMissing))?;
        let y_out = AllocatedNum::alloc(cs, || y_out_val.ok_or(SynthesisError::AssignmentMissing))?;
        let out_is_identity = AllocatedBit::alloc(cs, || {
            out_is_identity_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let x1_lc = x1.lc(cs);
        let y1_lc = y1.lc(cs);
        let xsum_lc = xsum.lc(cs);
        let ysum_lc = ysum.lc(cs);

        // Now constrain the output:
        //
        // a * b = c
        // a = bit
        // b = x3 - x1
        // c = x_out - x1

        let (a_var, b_var, c_var) = cs.multiply(|| {
            let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1 = x1.value().ok_or(SynthesisError::AssignmentMissing)?;
            let x3 = xsum.value().ok_or(SynthesisError::AssignmentMissing)?;
            let x_out = x_out_val.ok_or(SynthesisError::AssignmentMissing)?;

            let bit = if bit { C::Base::one() } else { C::Base::zero() };

            Ok((bit, x3 - &x1, x_out - &x1))
        })?;
        cs.enforce_zero(condition.lc(CS::ONE, Coeff::One) - a_var);
        cs.enforce_zero(xsum_lc - &x1_lc - b_var);
        cs.enforce_zero(x_out.lc() - &x1_lc - c_var);

        // d * e = f
        // d = bit
        // e = y3 - y1
        // f = y_out - y1

        let (d_var, e_var, f_var) = cs.multiply(|| {
            let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y1 = y1.value().ok_or(SynthesisError::AssignmentMissing)?;
            let y3 = ysum.value().ok_or(SynthesisError::AssignmentMissing)?;
            let y_out = y_out_val.ok_or(SynthesisError::AssignmentMissing)?;

            let bit = if bit { C::Base::one() } else { C::Base::zero() };

            Ok((bit, y3 - &y1, y_out - &y1))
        })?;
        cs.enforce_zero(condition.lc(CS::ONE, Coeff::One) - d_var);
        cs.enforce_zero(ysum_lc - &y1_lc - e_var);
        cs.enforce_zero(y_out.lc() - &y1_lc - f_var);

        // g * h = i
        // g = bit
        // h = sum_is_identity - self_is_identity
        // i = out_is_identity - self_is_identity

        let (g_var, h_var, i_var) = cs.multiply(|| {
            let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
            let self_is_identity = self_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let sum_is_identity = sum_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;
            let out_is_identity = out_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            let bit = if bit { C::Base::one() } else { C::Base::zero() };
            let self_is_identity = if self_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };
            let sum_is_identity = if sum_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };
            let out_is_identity = if out_is_identity {
                C::Base::one()
            } else {
                C::Base::zero()
            };

            Ok((
                bit,
                sum_is_identity - &self_is_identity,
                out_is_identity - &self_is_identity,
            ))
        })?;

        cs.enforce_zero(condition.lc(CS::ONE, Coeff::One) - g_var);
        cs.enforce_zero(
            sum.is_identity.lc(CS::ONE, Coeff::One)
                - &self.is_identity.lc(CS::ONE, Coeff::One)
                - h_var,
        );
        cs.enforce_zero(
            LinearCombination::from(out_is_identity.get_variable())
                - &self.is_identity.lc(CS::ONE, Coeff::One)
                - i_var,
        );

        Ok(CurvePoint {
            x: x_out.into(),
            y: y_out.into(),
            is_identity: out_is_identity.into(),
        })
    }

    /// Adds `self` to `other`, returning the result unless
    /// condition is false, in which case it returns `self`.
    ///
    /// Assumes no edge cases will occur.
    pub fn add_conditionally_incomplete<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let x1 = self.x;
        let y1 = self.y;

        let x2 = other.x;
        let y2 = other.y;

        let p1 = self.get_point().map(|p| p.unwrap());
        let p2 = other.get_point().map(|p| p.unwrap());

        let p3_val = p1.and_then(|p1| p2.and_then(|p2| Some((p1 + p2).get_xy().unwrap())));

        let p_out = match (p3_val, condition.get_value()) {
            (Some(p3), Some(b)) => {
                if b {
                    Some(p3)
                } else {
                    self.x
                        .value()
                        .and_then(|x| self.y.value().and_then(|y| Some((x, y))))
                }
            }
            _ => None,
        };

        let x_out =
            AllocatedNum::alloc(cs, || Ok(p_out.ok_or(SynthesisError::AssignmentMissing)?.0))?;
        let y_out =
            AllocatedNum::alloc(cs, || Ok(p_out.ok_or(SynthesisError::AssignmentMissing)?.1))?;

        let x1_lc = x1.lc(cs);
        let y1_lc = y1.lc(cs);
        let x2_lc = x2.lc(cs);
        let y2_lc = y2.lc(cs);

        // Affine addition for y^3 = x^2 + b (p1 != p2):
        //
        // lambda = (y2 - y1) / (x2 - x1)
        // x3 = lambda^2 - x1 - x2
        // y3 = -lambda x3 + lambda x1 - y1
        //
        // As a constraint system:
        //
        // a * b = c
        // a = x2 - x1
        // b := lambda
        // c = y2 - y1
        //
        // d * e = f
        // d = b
        // e = b
        // f := lambda^2
        //
        // g * h = i
        // g = b
        // h := x3 = f - x1 - x2
        // i := lambda x3
        //
        // j * k = l
        // j = b
        // k = x1
        // l := lambda x1
        //
        // y3 := -i + l - y1
        //
        // m * n = o
        // m = bit
        // n = x3 - x1
        // o = x_out - x1
        //
        // p * q = r
        // p = bit
        // q = y3 - y1
        // r = y_out - y1

        let a_val = x1
            .value()
            .and_then(|x1| x2.value().and_then(|x2| Some(x2 - &x1)));
        let c_val = y1
            .value()
            .and_then(|y1| y2.value().and_then(|y2| Some(y2 - &y1)));
        let lambda_val = a_val
            .and_then(|a_val| c_val.and_then(|c_val| Some(a_val.invert().map(|inv| inv * &c_val))));

        let (a_var, lambda, c_var) = cs.multiply(|| {
            let a_val = a_val.ok_or(SynthesisError::AssignmentMissing)?;
            let c_val = c_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_val = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;

            if lambda_val.is_some().into() {
                Ok((a_val, lambda_val.unwrap(), c_val))
            } else {
                Err(SynthesisError::DivisionByZero)
            }
        })?;
        cs.enforce_zero(x2_lc.clone() - &x1_lc - a_var);
        cs.enforce_zero(y2_lc - &y1_lc - c_var);

        let (d_var, e_var, f_var) = cs.multiply(|| {
            let lambda_val = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;

            if lambda_val.is_some().into() {
                let lambda_val = lambda_val.unwrap();
                Ok((lambda_val, lambda_val, lambda_val * &lambda_val))
            } else {
                Err(SynthesisError::DivisionByZero)
            }
        })?;
        cs.enforce_zero(LinearCombination::from(lambda) - d_var);
        cs.enforce_zero(LinearCombination::from(lambda) - e_var);

        let (g_var, x3_var, i_var) = cs.multiply(|| {
            let lambda_val = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x3_val = p3_val.ok_or(SynthesisError::AssignmentMissing)?.0;

            if lambda_val.is_some().into() {
                let lambda_val = lambda_val.unwrap();
                Ok((lambda_val, x3_val, lambda_val * &x3_val))
            } else {
                Err(SynthesisError::DivisionByZero)
            }
        })?;
        cs.enforce_zero(LinearCombination::from(lambda) - g_var);
        cs.enforce_zero(LinearCombination::from(f_var) - &x1_lc - &x2_lc - x3_var);

        let (j_var, k_var, l_var) = cs.multiply(|| {
            let lambda_val = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1_val = x1.value().ok_or(SynthesisError::AssignmentMissing)?;

            if lambda_val.is_some().into() {
                let lambda_val = lambda_val.unwrap();
                Ok((lambda_val, x1_val, lambda_val * &x1_val))
            } else {
                Err(SynthesisError::DivisionByZero)
            }
        })?;
        cs.enforce_zero(LinearCombination::from(lambda) - j_var);
        cs.enforce_zero(x1_lc.clone() - k_var);

        let y3_lc = LinearCombination::from(l_var) - i_var - &y1_lc;

        let (m_var, n_var, o_var) = cs.multiply(|| {
            let bit = condition
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let x1_val = x1.value().ok_or(SynthesisError::AssignmentMissing)?;
            let x3_val = p3_val.ok_or(SynthesisError::AssignmentMissing)?.0;
            let x_out_val = p_out.ok_or(SynthesisError::AssignmentMissing)?.0;

            let bit = if bit { C::Base::one() } else { C::Base::zero() };

            Ok((bit, x3_val - &x1_val, x_out_val - &x1_val))
        })?;
        cs.enforce_zero(condition.lc(CS::ONE, Coeff::One) - m_var);
        cs.enforce_zero(LinearCombination::from(x3_var) - &x1_lc - n_var);
        cs.enforce_zero(x_out.lc() - &x1_lc - o_var);

        let (p_var, q_var, r_var) = cs.multiply(|| {
            let bit = condition
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let y1_val = y1.value().ok_or(SynthesisError::AssignmentMissing)?;
            let y3_val = p3_val.ok_or(SynthesisError::AssignmentMissing)?.1;
            let y_out_val = p_out.ok_or(SynthesisError::AssignmentMissing)?.1;

            let bit = if bit { C::Base::one() } else { C::Base::zero() };

            Ok((bit, y3_val - &y1_val, y_out_val - &y1_val))
        })?;
        cs.enforce_zero(condition.lc(CS::ONE, Coeff::One) - p_var);
        cs.enforce_zero(y3_lc - &y1_lc - q_var);
        cs.enforce_zero(y_out.lc() - &y1_lc - r_var);

        Ok(CurvePoint {
            x: Num::from(x_out),
            y: Num::from(y_out),
            is_identity: Boolean::constant(false), // TODO: Fix this method
        })
    }

    /// Mock addition
    pub fn mock_add<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut p1 = None;
        self.is_identity.get_value().map(|is_identity| {
            self.x.value().map(|x| {
                self.y.value().map(|y| {
                    if is_identity {
                        p1 = Some(C::zero());
                    } else {
                        p1 = Some(C::from_xy(x, y).unwrap());
                    }
                })
            })
        });

        let mut p2 = None;
        other.is_identity.get_value().map(|is_identity| {
            other.x.value().map(|x| {
                other.y.value().map(|y| {
                    if is_identity {
                        p2 = Some(C::zero());
                    } else {
                        p2 = Some(C::from_xy(x, y).unwrap());
                    }
                })
            })
        });

        let p3 = p1.and_then(|p1| p2.and_then(|p2| Some(p1 + p2)));

        Self::witness(cs, || p3.ok_or(SynthesisError::AssignmentMissing))
    }

    /// Mock scalar multiplication
    pub fn mock_multiply<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        let mut p = None;
        self.is_identity.get_value().map(|is_identity| {
            self.x.value().map(|x| {
                self.y.value().map(|y| {
                    if is_identity {
                        p = Some(C::zero());
                    } else {
                        p = Some(C::from_xy(x, y).unwrap());
                    }
                })
            })
        });

        let mut mulby = C::Scalar::zero();
        for bit in other.iter().rev() {
            mulby = mulby + &mulby;
            if let Some(bit) = bit.get_value() {
                if bit {
                    mulby = mulby + &C::Scalar::one();
                }
            }
        }

        let p = p.map(|p| p * &mulby);

        Self::witness(cs, || p.ok_or(SynthesisError::AssignmentMissing))
    }

    /// Mock scalar multiplication
    pub fn mock_multiply_inv<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        let mut p = None;
        self.is_identity.get_value().map(|is_identity| {
            self.x.value().map(|x| {
                self.y.value().map(|y| {
                    if is_identity {
                        p = Some(C::zero());
                    } else {
                        p = Some(C::from_xy(x, y).unwrap());
                    }
                })
            })
        });

        let mut mulby = C::Scalar::zero();
        for bit in other.iter().rev() {
            mulby = mulby + &mulby;
            if let Some(bit) = bit.get_value() {
                if bit {
                    mulby = mulby + &C::Scalar::one();
                }
            }
        }

        let p = p.map(|p| p * &mulby.invert().unwrap());

        Self::witness(cs, || p.ok_or(SynthesisError::AssignmentMissing))
    }

    /// Multiply by a little-endian scalar.
    pub fn multiply<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        let mut ret = CurvePoint::identity();

        for bit in other.iter().rev() {
            let dbl = ret.add(cs, &ret)?;
            let sum = dbl.add(cs, &self)?;

            let bit_val = bit.get_value();

            let x_out = AllocatedNum::alloc(cs, || {
                bit_val
                    .and_then(|b| if b { sum.x.value() } else { dbl.x.value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            let y_out = AllocatedNum::alloc(cs, || {
                bit_val
                    .and_then(|b| if b { sum.y.value() } else { dbl.y.value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            let is_identity_out = AllocatedBit::alloc(cs, || {
                bit_val
                    .and_then(|b| {
                        if b {
                            sum.is_identity.get_value()
                        } else {
                            dbl.is_identity.get_value()
                        }
                    })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;

            // (x_out - x_dbl) = bit * (x_sum - x_dbl)
            let (a_var, b_var, c_var) = cs.multiply(|| {
                let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
                let x_dbl = dbl.x.value().ok_or(SynthesisError::AssignmentMissing)?;
                let x_sum = sum.x.value().ok_or(SynthesisError::AssignmentMissing)?;
                let x_out = x_out.get_value().ok_or(SynthesisError::AssignmentMissing)?;

                let bit = if bit { C::Base::one() } else { C::Base::zero() };

                Ok((bit, x_sum - &x_dbl, x_out - &x_dbl))
            })?;
            let x_dbl_lc = dbl.x.lc(cs);
            let x_sum_lc = sum.x.lc(cs);
            cs.enforce_zero(LinearCombination::from(bit.get_variable()) - a_var);
            cs.enforce_zero(x_sum_lc - &x_dbl_lc - b_var);
            cs.enforce_zero(x_out.lc() - &x_dbl_lc - c_var);

            // (y_out - y_dbl) = bit * (y_sum - y_dbl)
            let (d_var, e_var, f_var) = cs.multiply(|| {
                let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
                let y_dbl = dbl.y.value().ok_or(SynthesisError::AssignmentMissing)?;
                let y_sum = sum.y.value().ok_or(SynthesisError::AssignmentMissing)?;
                let y_out = y_out.get_value().ok_or(SynthesisError::AssignmentMissing)?;

                let bit = if bit { C::Base::one() } else { C::Base::zero() };

                Ok((bit, y_sum - &y_dbl, y_out - &y_dbl))
            })?;
            let y_dbl_lc = dbl.y.lc(cs);
            let y_sum_lc = sum.y.lc(cs);
            cs.enforce_zero(LinearCombination::from(bit.get_variable()) - d_var);
            cs.enforce_zero(y_sum_lc - &y_dbl_lc - e_var);
            cs.enforce_zero(y_out.lc() - &y_dbl_lc - f_var);

            // (is_identity_out - is_identity_dbl) = bit * (is_identity_sum - is_identity_dbl)
            let (g_var, h_var, i_var) = cs.multiply(|| {
                let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
                let is_identity_dbl = dbl
                    .is_identity
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let is_identity_sum = sum
                    .is_identity
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let is_identity_out = is_identity_out
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;

                let bit = if bit { C::Base::one() } else { C::Base::zero() };
                let is_identity_dbl = if is_identity_dbl {
                    C::Base::one()
                } else {
                    C::Base::zero()
                };
                let is_identity_sum = if is_identity_sum {
                    C::Base::one()
                } else {
                    C::Base::zero()
                };
                let is_identity_out = if is_identity_out {
                    C::Base::one()
                } else {
                    C::Base::zero()
                };

                Ok((
                    bit,
                    is_identity_sum - &is_identity_dbl,
                    is_identity_out - &is_identity_dbl,
                ))
            })?;
            let is_identity_dbl_lc = dbl.is_identity.lc(CS::ONE, Coeff::One);
            cs.enforce_zero(LinearCombination::from(bit.get_variable()) - g_var);
            cs.enforce_zero(sum.is_identity.lc(CS::ONE, Coeff::One) - &is_identity_dbl_lc - h_var);
            cs.enforce_zero(
                LinearCombination::from(is_identity_out.get_variable())
                    - &is_identity_dbl_lc
                    - i_var,
            );

            ret = CurvePoint {
                x: x_out.into(),
                y: y_out.into(),
                is_identity: is_identity_out.into(),
            };
        }

        Ok(ret)
    }

    /// Multiply by the inverse of a little-endian scalar.
    pub fn multiply_inv<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        let p = self
            .x
            .value()
            .and_then(|x| self.y.value().map(|y| C::from_xy(x, y).unwrap()))
            .ok_or(SynthesisError::AssignmentMissing);

        let inverted_val = other
            .iter()
            .enumerate()
            .map(|(i, b)| {
                b.get_value().map(|b| {
                    if b {
                        let mut ret = C::Scalar::one();
                        for _ in 0..i {
                            ret = ret + &ret
                        }
                        ret
                    } else {
                        C::Scalar::zero()
                    }
                })
            })
            .fold(Some(C::Scalar::zero()), |acc, n| match (acc, n) {
                (Some(acc), Some(n)) => Some(acc + &n),
                _ => None,
            })
            .ok_or(SynthesisError::AssignmentMissing)
            .and_then(|s| {
                let inv_s = s.invert();
                if inv_s.is_some().into() {
                    p.map(|p| p * inv_s.unwrap())
                } else {
                    Err(SynthesisError::Unsatisfiable)
                }
            })
            .map(|p| {
                let coords = p.get_xy();
                if coords.is_some().into() {
                    let (x, y) = coords.unwrap();
                    (x, y, false)
                } else {
                    let (x, y) = C::one().get_xy().unwrap();
                    (x, y, true)
                }
            });

        let x_inv_val = inverted_val.map(|(x, _, _)| x);
        let y_inv_val = inverted_val.map(|(_, y, _)| y);
        let is_identity_inv_val = inverted_val.map(|(_, _, b)| b);

        let x_inv = AllocatedNum::alloc(cs, || x_inv_val)?;
        let y_inv = AllocatedNum::alloc(cs, || y_inv_val)?;
        let is_identity_inv = AllocatedBit::alloc(cs, || is_identity_inv_val)?;

        let inverted = CurvePoint {
            x: x_inv.into(),
            y: y_inv.into(),
            is_identity: is_identity_inv.into(),
        };

        let calculated = inverted.multiply(cs, &other)?;

        let orig_x_lc = self.x.lc(cs);
        let orig_y_lc = self.y.lc(cs);
        let calculated_x_lc = calculated.x.lc(cs);
        let calculated_y_lc = calculated.y.lc(cs);

        cs.enforce_zero(orig_x_lc - &calculated_x_lc);
        cs.enforce_zero(orig_y_lc - &calculated_y_lc);
        cs.enforce_zero(
            self.is_identity.lc(CS::ONE, Coeff::One)
                - &calculated.is_identity.lc(CS::ONE, Coeff::One),
        );

        Ok(inverted)
    }
}

#[cfg(test)]
mod test {
    use super::CurvePoint;
    use crate::{
        circuits::{is_satisfied, Circuit, Coeff, ConstraintSystem, SynthesisError},
        curves::{Curve, Ec1},
        fields::{Fp, Fq},
        gadgets::boolean::{AllocatedBit, Boolean},
        Basic,
    };

    #[test]
    fn test_witness() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let _ = CurvePoint::witness(cs, || Ok(Ec1::one()))?;
                let _ = CurvePoint::witness(cs, || Ok(Ec1::zero()))?;

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn test_get_xy() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let one_coords = one.get_xy().unwrap();

                let p1 = CurvePoint::witness(cs, || Ok(one))?;
                let (x1, y1) = p1.get_xy(cs)?;
                let x1_lc = x1.lc(cs);
                let y1_lc = y1.lc(cs);
                cs.enforce_zero(x1_lc - (Coeff::Full(one_coords.0), CS::ONE));
                cs.enforce_zero(y1_lc - (Coeff::Full(one_coords.1), CS::ONE));

                let p2 = CurvePoint::witness(cs, || Ok(Ec1::zero()))?;
                let (x2, y2) = p2.get_xy(cs)?;
                let x2_lc = x2.lc(cs);
                let y2_lc = y2.lc(cs);
                cs.enforce_zero(x2_lc - (Coeff::Zero, CS::ONE));
                cs.enforce_zero(y2_lc - (Coeff::Zero, CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn one_plus_two() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let three = one + two;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (three_x, three_y) = three.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p3 = p1.add(cs, &p2)?;
                let (p3_x, p3_y) = p3.get_xy(cs)?;
                let p3_x_lc = p3_x.lc(cs);
                let p3_y_lc = p3_y.lc(cs);
                cs.enforce_zero(p3_x_lc - (Coeff::Full(three_x), CS::ONE));
                cs.enforce_zero(p3_y_lc - (Coeff::Full(three_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn one_plus_identity() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let zero = Ec1::zero();
                let one = Ec1::one();

                let (one_x, one_y) = one.get_xy().unwrap();

                let p0 = CurvePoint::witness(cs, || Ok(zero))?;
                let p1 = CurvePoint::witness(cs, || Ok(one))?;

                let psum = p1.add(cs, &p0)?;
                let (psum_x, psum_y) = psum.get_xy(cs)?;
                let psum_x_lc = psum_x.lc(cs);
                let psum_y_lc = psum_y.lc(cs);
                cs.enforce_zero(psum_x_lc - (Coeff::Full(one_x), CS::ONE));
                cs.enforce_zero(psum_y_lc - (Coeff::Full(one_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn identity_plus_two() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let zero = Ec1::zero();
                let one = Ec1::one();
                let two = one.double();

                let (two_x, two_y) = two.get_xy().unwrap();

                let p0 = CurvePoint::witness(cs, || Ok(zero))?;
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let psum = p0.add(cs, &p2)?;
                let (psum_x, psum_y) = psum.get_xy(cs)?;
                let psum_x_lc = psum_x.lc(cs);
                let psum_y_lc = psum_y.lc(cs);
                cs.enforce_zero(psum_x_lc - (Coeff::Full(two_x), CS::ONE));
                cs.enforce_zero(psum_y_lc - (Coeff::Full(two_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn identity_plus_identity() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let zero = Ec1::zero();
                let p0 = CurvePoint::witness(cs, || Ok(zero))?;

                let psum = p0.add(cs, &p0)?;
                let (psum_x, psum_y) = psum.get_xy(cs)?;
                let psum_x_lc = psum_x.lc(cs);
                let psum_y_lc = psum_y.lc(cs);
                cs.enforce_zero(psum_x_lc - (Coeff::Full(Fp::zero()), CS::ONE));
                cs.enforce_zero(psum_y_lc - (Coeff::Full(Fp::zero()), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn test_add_conditionally() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let three = one + two;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (three_x, three_y) = three.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p3a = p1.add_conditionally(cs, &p2, &Boolean::constant(true))?;
                let (p3a_x, p3a_y) = p3a.get_xy(cs)?;
                let p3a_x_lc = p3a_x.lc(cs);
                let p3a_y_lc = p3a_y.lc(cs);
                cs.enforce_zero(p3a_x_lc - (Coeff::Full(three_x), CS::ONE));
                cs.enforce_zero(p3a_y_lc - (Coeff::Full(three_y), CS::ONE));

                let p3b = p1.add_conditionally(cs, &p2, &Boolean::constant(false))?;
                let (p3b_x, p3b_y) = p3b.get_xy(cs)?;
                let p3b_x_lc = p3b_x.lc(cs);
                let p3b_y_lc = p3b_y.lc(cs);
                cs.enforce_zero(p3b_x_lc - (Coeff::Full(one_x), CS::ONE));
                cs.enforce_zero(p3b_y_lc - (Coeff::Full(one_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn test_add_conditionally_incomplete() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let three = one + two;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (three_x, three_y) = three.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p3a = p1.add_conditionally_incomplete(cs, &p2, &Boolean::constant(true))?;
                let (p3a_x, p3a_y) = p3a.get_xy(cs)?;
                let p3a_x_lc = p3a_x.lc(cs);
                let p3a_y_lc = p3a_y.lc(cs);
                cs.enforce_zero(p3a_x_lc - (Coeff::Full(three_x), CS::ONE));
                cs.enforce_zero(p3a_y_lc - (Coeff::Full(three_y), CS::ONE));

                let p3b = p1.add_conditionally_incomplete(cs, &p2, &Boolean::constant(false))?;
                let (p3b_x, p3b_y) = p3b.get_xy(cs)?;
                let p3b_x_lc = p3b_x.lc(cs);
                let p3b_y_lc = p3b_y.lc(cs);
                cs.enforce_zero(p3b_x_lc - (Coeff::Full(one_x), CS::ONE));
                cs.enforce_zero(p3b_y_lc - (Coeff::Full(one_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn multiply() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let five = one.double().double() + one;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (five_x, five_y) = five.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);

                let scalar5 = [
                    AllocatedBit::alloc(cs, || Ok(true))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                    AllocatedBit::alloc(cs, || Ok(true))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                ];

                let p5 = p1.multiply(cs, &scalar5)?;
                let (p5_x, p5_y) = p5.get_xy(cs)?;
                let p5_x_lc = p5_x.lc(cs);
                let p5_y_lc = p5_y.lc(cs);
                cs.enforce_zero(p5_x_lc - (Coeff::Full(five_x), CS::ONE));
                cs.enforce_zero(p5_y_lc - (Coeff::Full(five_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn multiply_inv() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let invfive = one * Fq::from(5).invert().unwrap();

                let (one_x, one_y) = one.get_xy().unwrap();
                let (invfive_x, invfive_y) = invfive.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);

                let scalar5 = [
                    AllocatedBit::alloc(cs, || Ok(true))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                    AllocatedBit::alloc(cs, || Ok(true))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                    AllocatedBit::alloc(cs, || Ok(false))?,
                ];

                let pinv5 = p1.multiply_inv(cs, &scalar5)?;
                let (pinv5_x, pinv5_y) = pinv5.get_xy(cs)?;
                let pinv5_x_lc = pinv5_x.lc(cs);
                let pinv5_y_lc = pinv5_y.lc(cs);
                cs.enforce_zero(pinv5_x_lc - (Coeff::Full(invfive_x), CS::ONE));
                cs.enforce_zero(pinv5_y_lc - (Coeff::Full(invfive_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }
}
