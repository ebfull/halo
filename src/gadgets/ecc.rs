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
    pub fn witness<CS, P>(mut cs: CS, point: P) -> Result<Self, SynthesisError>
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

        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || x_val)?;
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || y_val)?;
        let is_identity = AllocatedBit::alloc(cs.namespace(|| "is_identity"), || is_identity_val)?;

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
            Ok((
                xcub? + &C::b() - &ysq?,
                (!is_identity_val?).into(),
                C::Base::zero(),
            ))
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
    pub fn get_xy(&self) -> (Num<C::Base>, Num<C::Base>) {
        // We represent the identity internally as (0, 0), so we can just return
        // (x, y).
        (self.x, self.y)
    }

    /// Returns -P if condition is true, else returns P.
    pub fn conditional_neg<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let y_ret_val = self
            .y
            .value()
            .and_then(|y| condition.get_value().map(|b| if b { -y } else { y }));
        let y_ret = AllocatedNum::alloc(cs.namespace(|| "y_ret"), || {
            y_ret_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // y_self × (1 - 2.bit) = y_ret
        let (y_self_var, negator, y_ret_var) = cs.multiply(|| {
            let y_self = self.y.value().ok_or(SynthesisError::AssignmentMissing)?;
            let y_ret = y_ret_val.ok_or(SynthesisError::AssignmentMissing)?;
            let bit = condition
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;

            let negator = if bit { -C::Base::one() } else { C::Base::one() };

            Ok((y_self, negator, y_ret))
        })?;
        let y_self_lc = self.y.lc(&mut cs);
        cs.enforce_zero(y_self_lc - y_self_var);
        cs.enforce_zero(
            LinearCombination::from(CS::ONE)
                - &condition.lc(CS::ONE, Coeff::Full(C::Base::from_u64(2)))
                - negator,
        );
        cs.enforce_zero(y_ret.lc() - y_ret_var);

        Ok(CurvePoint {
            x: self.x,
            y: y_ret.into(),
            is_identity: self.is_identity.clone(),
        })
    }

    /// Adds a point to another point.
    ///
    /// Requires either:
    /// - P != Q, P != -Q, and neither being the identity, in which case the
    ///   output is fully constrained.
    /// - P and Q are both the identity, in which case the caller MUST NOT rely
    ///   on the output being constrained to the identity.
    pub fn add_incomplete<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let x_p = self.x;
        let y_p = self.y;
        let x_p_val = x_p.value();
        let y_p_val = y_p.value();

        let x_q = other.x;
        let y_q = other.y;
        let x_q_val = x_q.value();
        let y_q_val = y_q.value();

        // lambda = (y_q - y_p)/(x_q - x_p)
        let lambda_val = match (x_q_val, y_q_val, x_p_val, y_p_val) {
            (Some(x_q), Some(y_q), Some(x_p), Some(y_p)) => {
                let inv_xqxp = (x_q - &x_p).invert();
                if inv_xqxp.is_some().into() {
                    Ok(inv_xqxp.unwrap() * &(y_q - &y_p))
                } else {
                    // We handle both points being the identity as a special
                    // case within the constraints
                    if let Some(true) = self.is_identity.get_value() {
                        Ok(C::Base::zero())
                    } else {
                        Err(SynthesisError::DivisionByZero)
                    }
                }
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        // x_r = lambda^2 - x_p - x_q
        // y_r = lambda (x_p - x_r) - y_p
        let x_r_val = match (x_p_val, x_q_val) {
            (Some(x_p), Some(x_q)) => lambda_val.map(|lambda| (lambda * &lambda) - &x_p - &x_q),
            _ => Err(SynthesisError::AssignmentMissing),
        };
        let y_r_val = match (x_p_val, y_p_val) {
            (Some(x_p), Some(y_p)) => {
                x_r_val.and_then(|x_r| lambda_val.map(|lambda| (lambda * &(x_p - &x_r)) - &y_p))
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        let x_r = AllocatedNum::alloc(cs.namespace(|| "x_r"), || x_r_val)?;
        let y_r = AllocatedNum::alloc(cs.namespace(|| "y_r"), || y_r_val)?;

        //
        // Constraints:
        //

        let x_p_lc = x_p.lc(&mut cs);
        let y_p_lc = y_p.lc(&mut cs);
        let x_q_lc = x_q.lc(&mut cs);
        let y_q_lc = y_q.lc(&mut cs);

        // (x_q - x_p) * lambda = (y_q - y_p)
        let (a_var, lambda, c_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_q = x_q_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_q = y_q_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_q - &x_p, lambda_val?, y_q - &y_p))
        })?;
        cs.enforce_zero(x_q_lc.clone() - &x_p_lc - a_var);
        cs.enforce_zero(y_q_lc - &y_p_lc - c_var);

        // lambda * lambda = (x_p + x_q + x_r)
        let (d_var, e_var, f_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_q = x_q_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda_val?, lambda_val?, x_p + &x_q + &x_r_val?))
        })?;
        cs.enforce_zero(LinearCombination::from(lambda) - d_var);
        cs.enforce_zero(LinearCombination::from(lambda) - e_var);
        let x_r_lc = LinearCombination::from(f_var) - &x_p_lc - &x_q_lc;

        // (x_p - x_r) * lambda = (y_p + y_r)
        let (g_var, h_var, i_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_p - &x_r_val?, lambda_val?, y_p + &y_r_val?))
        })?;
        cs.enforce_zero(x_p_lc.clone() - &x_r_lc - g_var);
        cs.enforce_zero(LinearCombination::from(lambda) - h_var);
        let y_r_lc = LinearCombination::from(i_var) - &y_p_lc;

        Ok(CurvePoint {
            x: x_r.into(),
            y: y_r.into(),
            is_identity: self.is_identity.clone(),
        })
    }

    /// Adds a point to another point.
    ///
    /// Handles all edge cases.
    pub fn add<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
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
        // it internally as (0, 0).
        let (x3_val, y3_val, p3_is_identity_val) = match p3_val {
            Some(p) => {
                let coords = p.get_xy();
                if coords.is_some().into() {
                    let (x, y) = coords.unwrap();
                    (Some(x), Some(y), Some(false))
                } else {
                    (Some(C::Base::zero()), Some(C::Base::zero()), Some(true))
                }
            }
            None => (None, None, None),
        };

        // Output conditions:
        //
        // - If self.is_identity is true, return other
        // - If self.is_identity is false:
        //   - If other.is_identity is true, return self
        //   - If other.is_identity is false, return self + other

        let p1_is_identity_val = self.is_identity.get_value();
        let p2_is_identity_val = other.is_identity.get_value();

        let x4_val =
            x3_val.and_then(|x3| p3_is_identity_val.map(|b| if b { C::Base::zero() } else { x3 }));

        let y4_val =
            y3_val.and_then(|y3| p3_is_identity_val.map(|b| if b { C::Base::zero() } else { y3 }));

        let x5_val = x2_val.and_then(|x2| {
            x4_val.and_then(|x4| p1_is_identity_val.map(|p1| if p1 { x2 } else { x4 }))
        });

        let y5_val = y2_val.and_then(|y2| {
            y4_val.and_then(|y4| p1_is_identity_val.map(|p1| if p1 { y2 } else { y4 }))
        });

        let x_out_val = x1_val.and_then(|x1| {
            x5_val.and_then(|x5| p2_is_identity_val.map(|p2| if p2 { x1 } else { x5 }))
        });
        let y_out_val = y1_val.and_then(|y1| {
            y5_val.and_then(|y5| p2_is_identity_val.map(|p2| if p2 { y1 } else { y5 }))
        });

        let x_out = AllocatedNum::alloc(cs.namespace(|| "x_out"), || {
            x_out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_out = AllocatedNum::alloc(cs.namespace(|| "y_out"), || {
            y_out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let p3_is_identity = AllocatedBit::alloc(cs.namespace(|| "p3_is_identity"), || {
            p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        //
        // Constraints
        //

        let x1_lc = x1.lc(&mut cs);
        let y1_lc = y1.lc(&mut cs);
        let x2_lc = x2.lc(&mut cs);
        let y2_lc = y2.lc(&mut cs);

        // Complete complete affine addition for y^3 = x^2 + b:
        //
        // p1 != p2, p1 != identity, p2 != identity:
        //   lambda = (y2 - y1) / (x2 - x1)
        //   x3 = lambda^2 - x1 - x2
        //   y3 = -lambda x3 + lambda x1 - y1
        //
        //   p1 != p2, p1 == -p2:
        //     lambda = (non-zero) / (0) --> unsatisfiable
        //      --> We need to ensure the denominator is non-zero when the x
        //          coordinates are the same:
        //          (x2 - x1 + x_is_same) * lambda = (y2 - y1)
        //
        // p1 != p2, p1 == identity, p2 != identity:
        //   lambda = (y2 - 0) / (x2 - 0) = y2/x2
        //     --> x2 cannot be zero in this case, because there is no point
        //         with x-coordinate 0 on the curve.
        //   x3 = lambda^2 - 0 - x2 = (y2/x2)^2 - x2
        //   y3 = -lambda x3 + lambda 0 - 0
        //      = x2(y2/x2) - (y2/x2)^3
        //
        // p1 != p2, p1 != identity, p2 == identity:
        //   lambda = (0 - y1) / (0 - x1) = (y1/x1)
        //     --> x1 cannot be zero in this case, because there is no point
        //         with x-coordinate 0 on the curve.
        //   x3 = lambda^2 - x1 - 0 = (y1/x1)^2 - x1
        //   y3 = -lambda x3 + lambda x1 - y1
        //      = -((y1/x1)^2 - x1) x3 + (y1/x1) x1 - y1
        //
        // p1 == p2 != identity:
        //   lambda = (3 (x1)^2) / (2 y1)
        //     --> y1 cannot be zero in this case; there is no point with
        //         y-coordinate 0 on the curve, because the curve is
        //         prime-order.
        //   x3 = lambda^2 - 2 x1 = lambda^2 - x1 - x2
        //   y3 = -lambda x3 + lambda x1 - y1
        //
        // p1 == p2 == identity:
        //   lambda = (3 * (0)^2) / (2 * 0) ==> lambda = 0
        //     --> Here we set both x1 and y1 to zero, so while this is not on
        //         the curve, it is satisfiable.
        //   x3 = 0^2 - 2 * 0 = 0
        //   y3 = -0 * 0 + 0 * 0 - 0 = 0
        //   --> We don't need to constrain lambda = 0, because we replace
        //       (x3, y3) with (0, 0) explicitly in later constraints.
        //
        // So we can handle both cases by including a selection constraint:
        //   (x2 - x1) * x_is_same = 0
        //     --> if different, x_is_same must be 0
        //
        //   (x2 - x1) * (x2 - x1)^-1 = (1 - x_is_same)
        //     --> if the same, x_is_same must be 1
        //
        //   (lambda - lambda_diff) = x_is_same * (lambda_same - lambda_diff)
        //
        // In R1CS:
        //
        // (x2 - x1) * x_is_same = 0
        // (x2 - x1) * (x2 - x1)^-1 = (1 - x_is_same)
        // x1 * x1 = (x1)^2
        // (x2 - x1 + x_is_same) * lambda_diff = (y2 - y1)
        // (2 y1) * lambda_same = 3 (x1)^2
        // (lambda - lambda_diff) = x_is_same * (lambda_same - lambda_diff)
        // lambda * lambda = x1 + x2 + x3
        // (x1 - x3) * lambda = y1 + y3
        //
        // This is complete in the sense that it handles p1 = p2. However, in
        // the case where p3 is the identity, we need to force the canonical
        // representation (0, 0) for x_out, y_out.
        //
        // Constrain p3_is_identity:
        //   (y2 + y1) * p3_is_identity = 0
        //     --> if (y2 + y1) != 0, p3_is_identity must be 0
        //
        //   (y2 + y1) * (y2 + y1)^-1 = (x_is_same - p3_is_identity)
        //     --> if (y2 + y1) == 0, p3_is_identity must be x_is_same
        //
        // x4 = x3 * (1 - p3_is_identity)
        // y4 = y3 * (1 - p3_is_identity)
        //
        // and handle the cases where p1 or p2 is the identity:
        //
        // (x5 - x4) = p1_is_identity * (x2 - x4)
        // (y5 - y4) = p1_is_identity * (y2 - y4)
        //
        // (x_out - x5) = p2_is_identity * (x1 - x5)
        // (y_out - y5) = p2_is_identity * (y1 - y5)

        // (x2 - x1) * x_is_same = 0
        // a = x2 - x1
        // b = 0

        let x2mx1_val = x1_val.and_then(|x1| x2_val.map(|x2| x2 - &x1));
        let x_is_same_val = x2mx1_val.map(|x2mx1| bool::from(x2mx1.is_zero()).into());
        let x2mx1psame_val =
            x2mx1_val.and_then(|x2mx1| x_is_same_val.map(|is_same| x2mx1 + &is_same));

        let (a_var, x_is_same_var, b_var) = cs.multiply(|| {
            let x2mx1 = x2mx1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_is_same = x_is_same_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x2mx1, x_is_same, C::Base::zero()))
        })?;
        cs.enforce_zero(x2_lc.clone() - &x1_lc - a_var);
        cs.enforce_zero(LinearCombination::from(b_var));

        // (x2 - x1) * (x2 - x1)^-1 = (1 - x_is_same)
        // c = a = x2 - x1
        // d := a^-1 unless a == 0, in which case witness d := 1
        // e = (1 - x_is_same)

        let x2mx1_inv_val = x2mx1_val.map(|x2mx1| {
            let inv = x2mx1.invert();
            if inv.is_some().into() {
                inv.unwrap()
            } else {
                // dinv is unconstrained
                C::Base::one()
            }
        });

        let (c_var, d_var, e_var) = cs.multiply(|| {
            let x2mx1 = x2mx1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x2mx1_inv = x2mx1_inv_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_is_same = x_is_same_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x2mx1, x2mx1_inv, C::Base::one() - &x_is_same))
        })?;
        cs.enforce_zero(LinearCombination::from(a_var) - c_var);
        cs.enforce_zero(LinearCombination::zero() + (Coeff::One, CS::ONE) - x_is_same_var - e_var);

        // x1 * x1 = (x1)^2
        // f = x1
        // g = x1
        // h := x1^2

        let x1_sq = x1_val.map(|x| x * &x);

        let (f_var, g_var, h_var) = cs.multiply(|| {
            let x = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let xsq = x1_sq.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x, x, xsq))
        })?;
        cs.enforce_zero(x1_lc.clone() - f_var);
        cs.enforce_zero(x1_lc.clone() - g_var);

        // (x2 - x1 + x_is_same) * lambda_diff = (y2 - y1)
        // i = x2 - x1 + x_is_same
        // j = y2 - y1

        let j_val = y1_val.and_then(|y1| y2_val.map(|y2| y2 - &y1));
        let lambda_diff_val = x2mx1psame_val.and_then(|x2mx1psame| {
            j_val.map(|y2my1| {
                let inv = x2mx1psame.invert();
                if inv.is_some().into() {
                    inv.unwrap() * &y2my1
                } else {
                    // lambda_diff is unconstrained
                    C::Base::one()
                }
            })
        });

        let (i_var, lambda_diff_var, j_var) = cs.multiply(|| {
            let x2mx1psame = x2mx1psame_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y2my1 = j_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_diff = lambda_diff_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x2mx1psame, lambda_diff, y2my1))
        })?;
        cs.enforce_zero(x2_lc.clone() - &x1_lc + x_is_same_var - i_var);
        cs.enforce_zero(y2_lc.clone() - &y1_lc - j_var);

        // (2 y1) * lambda_same = 3 (x1)^2
        // k = 2 y1
        // l = 3 h = 3 x1^2

        let k_val = y1_val.map(|y1| y1 + &y1);
        let l_val = x1_sq.map(|x1sq| x1sq + &x1sq + &x1sq);
        let lambda_same_val = k_val.and_then(|y1two| {
            l_val.map(|x1sq3| {
                let inv = y1two.invert();
                if inv.is_some().into() {
                    inv.unwrap() * &x1sq3
                } else {
                    // This is the identity + identity case; set lambda = 0
                    C::Base::zero()
                }
            })
        });

        let (k_var, lambda_same_var, l_var) = cs.multiply(|| {
            let y1two = k_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1sq3 = l_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_same = lambda_same_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y1two, lambda_same, x1sq3))
        })?;
        cs.enforce_zero(y1_lc.clone() + &y1_lc - k_var);
        cs.enforce_zero(
            LinearCombination::zero() + (Coeff::Full(C::Base::from_u64(3)), h_var) - l_var,
        );

        // lambda * lambda = x1 + x2 + x3
        // m = lambda
        // n = lambda^2 (= x1 + x2 + x3 if p1 != identity and p2 != identity)
        //
        // Constrain this here so we have a variable for lambda

        let lambda_val = x2mx1_val.and_then(|x2mx1| {
            if x2mx1.is_zero().into() {
                lambda_same_val
            } else {
                lambda_diff_val
            }
        });

        // We compute the value of lambda^2 directly here, because if p1 or
        // p2 is the identity then this constraint doesn't work, so we need
        // to only constrain it to the actual p3 value if p1 and p2 are not
        // the identity.
        let lambda_sq_val = lambda_val.map(|lambda| lambda * &lambda);

        let (lambda_var, m_var, n_var) = cs.multiply(|| {
            let lambda = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_sq = lambda_sq_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda, lambda, lambda_sq))
        })?;
        cs.enforce_zero(LinearCombination::from(lambda_var) - m_var);
        let x3_lc = LinearCombination::from(n_var) - &x1_lc - &x2_lc;

        // x_is_same * (lambda_same - lambda_diff) = (lambda - lambda_diff)
        let (o_var, p_var, q_var) = cs.multiply(|| {
            let x_is_same = x_is_same_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_diff = lambda_diff_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_same = lambda_same_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_is_same, lambda_same - &lambda_diff, lambda - &lambda_diff))
        })?;
        cs.enforce_zero(LinearCombination::from(x_is_same_var) - o_var);
        cs.enforce_zero(LinearCombination::from(lambda_same_var) - lambda_diff_var - p_var);
        cs.enforce_zero(LinearCombination::from(lambda_var) - lambda_diff_var - q_var);

        // (x1 - x3) * lambda = y1 + y3
        //
        // Use x3 = lambda^2 - x1 - x2 here, instead of the outer-calculated
        // x3_val (so that the constraint works).
        let (r_var, s_var, t_var) = cs.multiply(|| {
            let lambda = lambda_val.ok_or(SynthesisError::AssignmentMissing)?;
            let lambda_sq = lambda_sq_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x1 = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x2 = x2_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((
                x1 - &lambda_sq + &x1 + &x2,
                lambda,
                (x1 - &lambda_sq + &x1 + &x2) * &lambda,
            ))
        })?;
        cs.enforce_zero(x1_lc.clone() - &x3_lc - r_var);
        cs.enforce_zero(LinearCombination::from(lambda_var) - s_var);
        let y3_lc = LinearCombination::from(t_var) - &y1_lc;

        // (y2 + y1) * p3_is_identity = 0
        let (u_var, p3_is_identity_var, v_var) = cs.multiply(|| {
            let y1 = y1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y2 = y2_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p3_is_identity = p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y2 + &y1, p3_is_identity.into(), C::Base::zero()))
        })?;
        cs.enforce_zero(y2_lc.clone() + &y1_lc - u_var);
        cs.enforce_zero(
            LinearCombination::from(p3_is_identity.get_variable()) - p3_is_identity_var,
        );
        cs.enforce_zero(LinearCombination::from(v_var));

        // // (y1 + y2) * (y1 + y2)^-1 = (x_is_same - p3_is_identity)
        // let (w_var, _, x_var) = cs.multiply(|| {
        //     let y1 = y1_val.ok_or(SynthesisError::AssignmentMissing)?;
        //     let y2 = y2_val.ok_or(SynthesisError::AssignmentMissing)?;
        //     let x_is_same = x_is_same_val.ok_or(SynthesisError::AssignmentMissing)?;
        //     let p3_is_identity = p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

        //     let y1y2inv = (y1 + &y2).invert().unwrap_or(C::Base::zero());

        //     let p3_is_identity: C::Base = p3_is_identity.into();

        //     Ok((y1 + &y2, y1y2inv, x_is_same - &p3_is_identity))
        // })?;
        // cs.enforce_zero(y1_lc.clone() + &y2_lc - w_var);
        // cs.enforce_zero(LinearCombination::from(x_is_same_var) - p3_is_identity_var - x_var);

        // x4 = x3 * (1 - p3_is_identity)
        let (y_var, z_var, x4_var) = cs.multiply(|| {
            let x3 = x3_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x4 = x4_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p3_is_identity = p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x3, (!p3_is_identity).into(), x4))
        })?;
        // TODO: Fix
        // cs.enforce_zero(x3_lc - y_var);
        cs.enforce_zero(LinearCombination::from(CS::ONE) - p3_is_identity_var - z_var);

        // y4 = y3 * (1 - p3_is_identity)
        let (aa_var, bb_var, y4_var) = cs.multiply(|| {
            let y3 = y3_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y4 = y4_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p3_is_identity = p3_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y3, (!p3_is_identity).into(), y4))
        })?;
        // TODO: Fix
        // cs.enforce_zero(y3_lc - aa_var);
        cs.enforce_zero(LinearCombination::from(CS::ONE) - p3_is_identity_var - bb_var);

        // (x5 - x4) = p1_is_identity * (x2 - x4)
        let (cc_var, dd_var, ee_var) = cs.multiply(|| {
            let x2 = x2_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x4 = x4_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x5 = x5_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((p1_is_identity.into(), x2 - &x4, x5 - &x4))
        })?;
        cs.enforce_zero(self.is_identity.lc(CS::ONE, Coeff::One) - cc_var);
        cs.enforce_zero(x2_lc - x4_var - dd_var);
        let x5_lc = LinearCombination::from(ee_var) + x4_var;

        // (y5 - y4) = p1_is_identity * (y2 - y4)
        let (ff_var, gg_var, hh_var) = cs.multiply(|| {
            let y2 = y2_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y4 = y4_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y5 = y5_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p1_is_identity = p1_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((p1_is_identity.into(), y2 - &y4, y5 - &y4))
        })?;
        cs.enforce_zero(self.is_identity.lc(CS::ONE, Coeff::One) - ff_var);
        cs.enforce_zero(y2_lc - y4_var - gg_var);
        let y5_lc = LinearCombination::<C::Base>::from(hh_var) + y4_var;

        // (x_out - x5) = p2_is_identity * (x1 - x5)
        let (ii_var, jj_var, kk_var) = cs.multiply(|| {
            let x1 = x1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x5 = x5_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_out = x_out_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p2_is_identity = p2_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((p2_is_identity.into(), x1 - &x5, x_out - &x5))
        })?;
        cs.enforce_zero(other.is_identity.lc(CS::ONE, Coeff::One) - ii_var);
        cs.enforce_zero(x1_lc - &x5_lc - jj_var);
        cs.enforce_zero(x_out.lc() - &x5_lc - kk_var);

        // (y_out - y5) = p2_is_identity * (y1 - y5)
        let (ll_var, mm_var, nn_var) = cs.multiply(|| {
            let y1 = y1_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y5 = y5_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_out = y_out_val.ok_or(SynthesisError::AssignmentMissing)?;
            let p2_is_identity = p2_is_identity_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((p2_is_identity.into(), y1 - &y5, y_out - &y5))
        })?;
        cs.enforce_zero(other.is_identity.lc(CS::ONE, Coeff::One) - ll_var);
        cs.enforce_zero(y1_lc - &y5_lc - mm_var);
        cs.enforce_zero(y_out.lc() - &y5_lc - nn_var);

        Ok(CurvePoint {
            x: x_out.into(),
            y: y_out.into(),
            is_identity: p3_is_identity.into(),
        })
    }

    /// Adds `self` to `other`, returning the result unless
    /// condition is false, in which case it returns `self`.
    ///
    /// Handles all edge cases.
    pub fn add_conditionally<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        // Output conditions:
        //
        // - If condition is false, return self
        // - If condition is true, return self + other

        let sum = self.add(cs.namespace(|| "unconditional add"), other)?;

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

        let x_out = AllocatedNum::alloc(cs.namespace(|| "x_out"), || {
            x_out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_out = AllocatedNum::alloc(cs.namespace(|| "y_out"), || {
            y_out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let out_is_identity = AllocatedBit::alloc(cs.namespace(|| "out_is_identity"), || {
            out_is_identity_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let x1_lc = x1.lc(&mut cs);
        let y1_lc = y1.lc(&mut cs);
        let xsum_lc = xsum.lc(&mut cs);
        let ysum_lc = ysum.lc(&mut cs);

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

            Ok((bit.into(), x3 - &x1, x_out - &x1))
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

            Ok((bit.into(), y3 - &y1, y_out - &y1))
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

            let self_is_identity: C::Base = self_is_identity.into();
            let sum_is_identity: C::Base = sum_is_identity.into();
            let out_is_identity: C::Base = out_is_identity.into();

            Ok((
                bit.into(),
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
        mut cs: CS,
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

        let x_out = AllocatedNum::alloc(cs.namespace(|| "x_out"), || {
            Ok(p_out.ok_or(SynthesisError::AssignmentMissing)?.0)
        })?;
        let y_out = AllocatedNum::alloc(cs.namespace(|| "y_out"), || {
            Ok(p_out.ok_or(SynthesisError::AssignmentMissing)?.1)
        })?;

        let x1_lc = x1.lc(&mut cs);
        let y1_lc = y1.lc(&mut cs);
        let x2_lc = x2.lc(&mut cs);
        let y2_lc = y2.lc(&mut cs);

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

            Ok((bit.into(), x3_val - &x1_val, x_out_val - &x1_val))
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

            Ok((bit.into(), y3_val - &y1_val, y_out_val - &y1_val))
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

    /// Returns [2] P.
    pub fn double<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let x_p_val = self.x.value();
        let y_p_val = self.y.value();

        // lambda = (3 x_p^2)/(2 y_p)
        let lambda_val = match (x_p_val, y_p_val) {
            (Some(x_p), Some(y_p)) => {
                let inv_2yp = (y_p + &y_p).invert();
                if inv_2yp.is_some().into() {
                    let xx_p = x_p * &x_p;
                    Ok(inv_2yp.unwrap() * &(xx_p + &xx_p + &xx_p))
                } else {
                    // Set lambda to zero, and then constrain to zero
                    Ok(C::Base::zero())
                }
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        // x_dbl = lambda^2 - 2 x_p
        let x_dbl_val = if let Some(x_p) = x_p_val {
            lambda_val.map(|lambda| (lambda * &lambda) - &x_p - &x_p)
        } else {
            Err(SynthesisError::AssignmentMissing)
        };

        // y_dbl = lambda (x_p - x_dbl) - y_p
        let y_dbl_val = match (x_p_val, y_p_val) {
            (Some(x_p), Some(y_p)) => x_dbl_val
                .and_then(|x_dbl| lambda_val.map(|lambda| (lambda * &(x_p - &x_dbl)) - &y_p)),
            _ => Err(SynthesisError::AssignmentMissing),
        };

        let x_dbl = AllocatedNum::alloc(cs.namespace(|| "x_dbl"), || x_dbl_val)?;
        let y_dbl = AllocatedNum::alloc(cs.namespace(|| "y_dbl"), || y_dbl_val)?;

        //
        // Constraints:
        //

        let x_p_lc = self.x.lc(&mut cs);
        let y_p_lc = self.y.lc(&mut cs);

        // x_p * x_p = xx_p
        let xx_p_val = x_p_val.map(|x_p| x_p * &x_p);
        let (a_var, b_var, xx_p) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let xx_p = xx_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            Ok((x_p, x_p, xx_p))
        })?;
        cs.enforce_zero(x_p_lc.clone() - a_var);
        cs.enforce_zero(x_p_lc.clone() - b_var);

        // (2 y_p) * lambda = (3 xx_p)
        //
        // y_p can only be zero if p is the identity (because the curve is
        // prime-order), in which case xx_p is zero, so this is satisfiable.
        let (c_var, lambda, d_var) = cs.multiply(|| {
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let xx_p = xx_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            Ok((y_p + &y_p, lambda_val?, xx_p + &xx_p + &xx_p))
        })?;
        cs.enforce_zero(y_p_lc.clone() + &y_p_lc - c_var);
        cs.enforce_zero(LinearCombination::zero() + xx_p + xx_p + xx_p - d_var);

        // lambda * lambda = (2 x_p + x_dbl)
        //
        // In the identity case, if lambda == 0 then this constrains x_dbl to 0,
        // and then the constraint below constrains y_dbl to 0.
        let (d_var, e_var, f_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda_val?, lambda_val?, x_p + &x_p + &x_dbl_val?))
        })?;
        cs.enforce_zero(LinearCombination::from(lambda) - d_var);
        cs.enforce_zero(LinearCombination::from(lambda) - e_var);
        cs.enforce_zero(x_p_lc.clone() + &x_p_lc + &x_dbl.lc() - f_var);

        // (x_p - x_dbl) * lambda = (y_p + y_dbl)
        let (g_var, h_var, i_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_p - &x_dbl_val?, lambda_val?, y_p + &y_dbl_val?))
        })?;
        cs.enforce_zero(x_p_lc - &x_dbl.lc() - g_var);
        cs.enforce_zero(LinearCombination::from(lambda) - h_var);
        cs.enforce_zero(y_p_lc + &y_dbl.lc() - i_var);

        // lambda * is_identity = 0
        let (j_var, k_var, l_var) = cs.multiply(|| {
            let is_identity = self
                .is_identity
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda_val?, is_identity.into(), C::Base::zero()))
        })?;
        cs.enforce_zero(LinearCombination::from(lambda) - j_var);
        cs.enforce_zero(self.is_identity.lc(CS::ONE, Coeff::One) - k_var);
        cs.enforce_zero(LinearCombination::from(l_var));

        Ok(CurvePoint {
            x: x_dbl.into(),
            y: y_dbl.into(),
            is_identity: self.is_identity.clone(),
        })
    }

    /// Returns [2] P + Q.
    ///
    /// Requires either:
    /// - P != Q, P != -Q, and neither being the identity, in which case the
    ///   output is fully constrained.
    /// - P and Q are both the identity, in which case the caller MUST NOT rely
    ///   on the output being constrained to the identity.
    pub fn double_and_add_incomplete<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        // Compute [2] P + Q as (P + Q) + P:
        // R = P + Q
        // S = R + P
        // See https://github.com/zcash/zcash/issues/3924 for details.

        let x_p = self.x;
        let y_p = self.y;
        let x_p_val = self.x.value();
        let y_p_val = self.y.value();
        let x_p_lc = x_p.lc(&mut cs);
        let y_p_lc = y_p.lc(&mut cs);

        let x_q = other.x;
        let y_q = other.y;
        let x_q_val = other.x.value();
        let y_q_val = other.y.value();
        let x_q_lc = x_q.lc(&mut cs);
        let y_q_lc = y_q.lc(&mut cs);

        // lambda_1 = (y_q - y_p)/(x_q - x_p)
        let lambda_1_val = match (x_q_val, y_q_val, x_p_val, y_p_val) {
            (Some(x_q), Some(y_q), Some(x_p), Some(y_p)) => {
                let inv_xqxp = (x_q - &x_p).invert();
                if inv_xqxp.is_some().into() {
                    Ok(inv_xqxp.unwrap() * &(y_q - &y_p))
                } else {
                    // We handle both points being the identity as a special
                    // case within the constraints
                    match (self.is_identity.get_value(), other.is_identity.get_value()) {
                        (Some(true), Some(true)) => Ok(C::Base::zero()),
                        _ => Err(SynthesisError::DivisionByZero),
                    }
                }
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        // x_r = lambda_1^2 - x_p - x_q
        let x_r_val = match (x_p_val, x_q_val) {
            (Some(x_p), Some(x_q)) => {
                lambda_1_val.map(|lambda_1| (lambda_1 * &lambda_1) - &x_p - &x_q)
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        // lambda_2 = 2 y_p /(x_p - x_r) - lambda_1
        let lambda_2_val = match (x_p_val, y_p_val) {
            (Some(x_p), Some(y_p)) => x_r_val.and_then(|x_r| {
                lambda_1_val.and_then(|lambda_1| {
                    let inv_xpxr = (x_p - &x_r).invert();
                    if inv_xpxr.is_some().into() {
                        Ok((inv_xpxr.unwrap() * &(y_p + &y_p)) - &lambda_1)
                    } else {
                        // We handle both points being the identity as a special
                        // case within the constraints
                        match (self.is_identity.get_value(), other.is_identity.get_value()) {
                            (Some(true), Some(true)) => Ok(C::Base::zero()),
                            _ => Err(SynthesisError::DivisionByZero),
                        }
                    }
                })
            }),
            _ => Err(SynthesisError::AssignmentMissing),
        };

        // x_s = lambda_2^2 - x_r - x_p
        // y_s = lambda_2 (x_p - x_s) - y_p
        let x_s_val = x_p_val
            .ok_or(SynthesisError::AssignmentMissing)
            .and_then(|x_p| {
                x_r_val.and_then(|x_r| {
                    lambda_2_val.map(|lambda_2| (lambda_2 * &lambda_2) - &x_r - &x_p)
                })
            });
        let y_s_val = match (x_p_val, y_p_val) {
            (Some(x_p), Some(y_p)) => x_s_val
                .and_then(|x_s| lambda_2_val.map(|lambda_2| (lambda_2 * &(x_p - &x_s)) - &y_p)),
            _ => Err(SynthesisError::AssignmentMissing),
        };

        let x_s = AllocatedNum::alloc(cs.namespace(|| "x_s"), || x_s_val)?;
        let y_s = AllocatedNum::alloc(cs.namespace(|| "y_s"), || y_s_val)?;

        //
        // Constraints:
        //

        // (x_q - x_p) * lambda_1 = (y_q - y_p)
        let (a_var, lambda_1, c_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_q = x_q_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_q = y_q_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_q - &x_p, lambda_1_val?, y_q - &y_p))
        })?;
        cs.enforce_zero(x_q_lc.clone() - &x_p_lc - a_var);
        cs.enforce_zero(y_q_lc - &y_p_lc - c_var);

        // lambda_1 * lambda_1 = (x_p + x_q + x_r)
        let (d_var, e_var, f_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_q = x_q_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda_1_val?, lambda_1_val?, x_p + &x_q + &x_r_val?))
        })?;
        cs.enforce_zero(LinearCombination::from(lambda_1) - d_var);
        cs.enforce_zero(LinearCombination::from(lambda_1) - e_var);

        // lambda_2 * lambda_2 = (x_r + x_p + x_s)
        let (lambda_2, k_var, l_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lambda_2_val?, lambda_2_val?, x_r_val? + &x_p + &x_s_val?))
        })?;
        cs.enforce_zero(LinearCombination::from(lambda_2) - k_var);
        cs.enforce_zero(x_s.lc() + f_var - &x_q_lc - l_var);

        // (x_p - x_r) × (lambda_1 + lambda_2) = (2 y_p)
        let (g_var, h_var, i_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_p - &x_r_val?, lambda_1_val? + &lambda_2_val?, y_p + &y_p))
        })?;
        cs.enforce_zero(x_p_lc.clone() - f_var + &x_p_lc + &x_q_lc - g_var);
        cs.enforce_zero(LinearCombination::from(lambda_1) + lambda_2 - h_var);
        cs.enforce_zero(y_p_lc.clone() + &y_p_lc - i_var);

        // (x_p - x_s) × lambda_2 = (y_p + y_s)
        let (g_var, h_var, i_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_p - &x_s_val?, lambda_2_val?, y_p + &y_s_val?))
        })?;
        cs.enforce_zero(x_p_lc - &x_s.lc() - g_var);
        cs.enforce_zero(LinearCombination::from(lambda_2) - h_var);
        cs.enforce_zero(y_p_lc + &y_s.lc() - i_var);

        Ok(CurvePoint {
            x: x_s.into(),
            y: y_s.into(),
            is_identity: self.is_identity.clone(),
        })
    }

    /// Multiply by a little-endian scalar.
    pub fn multiply<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        let mut ret = CurvePoint::identity();

        for (i, bit) in other.iter().enumerate().rev() {
            let mut cs = cs.namespace(|| format!("bit {}", i));

            let dbl = ret.double(cs.namespace(|| "double"))?;
            let sum = dbl.add(cs.namespace(|| "add"), &self)?;

            let bit_val = bit.get_value();

            let x_out = AllocatedNum::alloc(cs.namespace(|| "x_out"), || {
                bit_val
                    .and_then(|b| if b { sum.x.value() } else { dbl.x.value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            let y_out = AllocatedNum::alloc(cs.namespace(|| "y_out"), || {
                bit_val
                    .and_then(|b| if b { sum.y.value() } else { dbl.y.value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            let is_identity_out = AllocatedBit::alloc(cs.namespace(|| "out_is_identity"), || {
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

                Ok((bit.into(), x_sum - &x_dbl, x_out - &x_dbl))
            })?;
            let x_dbl_lc = dbl.x.lc(&mut cs);
            let x_sum_lc = sum.x.lc(&mut cs);
            cs.enforce_zero(LinearCombination::from(bit.get_variable()) - a_var);
            cs.enforce_zero(x_sum_lc - &x_dbl_lc - b_var);
            cs.enforce_zero(x_out.lc() - &x_dbl_lc - c_var);

            // (y_out - y_dbl) = bit * (y_sum - y_dbl)
            let (d_var, e_var, f_var) = cs.multiply(|| {
                let bit = bit_val.ok_or(SynthesisError::AssignmentMissing)?;
                let y_dbl = dbl.y.value().ok_or(SynthesisError::AssignmentMissing)?;
                let y_sum = sum.y.value().ok_or(SynthesisError::AssignmentMissing)?;
                let y_out = y_out.get_value().ok_or(SynthesisError::AssignmentMissing)?;

                Ok((bit.into(), y_sum - &y_dbl, y_out - &y_dbl))
            })?;
            let y_dbl_lc = dbl.y.lc(&mut cs);
            let y_sum_lc = sum.y.lc(&mut cs);
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

                let is_identity_dbl: C::Base = is_identity_dbl.into();
                let is_identity_sum: C::Base = is_identity_sum.into();
                let is_identity_out: C::Base = is_identity_out.into();

                Ok((
                    bit.into(),
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

    /// Multiply by a little-endian scalar.
    ///
    /// Requires that the top bit of other is set.
    pub fn multiply_fast<CS: ConstraintSystem<C::Base>>(
        &self,
        mut cs: CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        // From https://github.com/zcash/zcash/issues/3924
        //
        // Goal: [other] self = [2^n + k] T
        //
        // Acc := [3] T
        // for i from n-2 down to 0 {
        //     Q := k[i+1] ? T : −T
        //     Acc := (Acc + Q) + Acc
        // }
        // return (k[0] = 0) ? (Acc - T) : Acc
        //
        // Note that k is still n + 1 bits, i.e. k[n] = 0

        let k_0_var = other[0].get_variable();
        let k_0_val = other[0].get_value();

        // We must have a scalar, and the top bit must be set
        if let Some(b) = other.last().unwrap().get_value() {
            assert_eq!(b, true);
        }
        let mut acc = self.double(cs.namespace(|| "[2] Acc"))?;
        acc = acc.add_incomplete(cs.namespace(|| "[3] Acc"), self)?;

        for (i, bit) in other
            .iter()
            .cloned()
            .map(Boolean::from)
            .enumerate()
            // Skip the LSB (we handle it after the loop)
            .skip(1)
            // Scan over the scalar bits in big-endian order
            .rev()
            // Skip the MSB (already accumulated)
            .skip(1)
        {
            let mut cs = cs.namespace(|| format!("bit {}", i));
            let t = self.conditional_neg(cs.namespace(|| "conditional negation"), &bit.not())?;
            acc = acc.double_and_add_incomplete(cs.namespace(|| "double and add"), &t)?;
        }

        // Compute Acc - T = P + (-T)

        let acc_minus_t = acc.add_incomplete(
            cs.namespace(|| "Acc - T"),
            &CurvePoint {
                x: self.x.clone(),
                y: -self.y,
                is_identity: self.is_identity.clone(),
            },
        )?;

        let x_p = acc.x;
        let y_p = acc.y;
        let x_p_val = x_p.value();
        let y_p_val = y_p.value();

        let x_r = acc_minus_t.x;
        let y_r = acc_minus_t.y;
        let x_r_val = x_r.value();
        let y_r_val = y_r.value();

        // x_s = k[0] ? x_p : x_r
        // y_s = k[0] ? y_p : y_r
        let x_s_val = match (x_p_val, x_r_val, k_0_val) {
            (Some(x_p), Some(x_r), Some(k_0)) => Some(if k_0 { x_p } else { x_r }),
            _ => None,
        };
        let y_s_val = match (y_p_val, y_r_val, k_0_val) {
            (Some(y_p), Some(y_r), Some(k_0)) => Some(if k_0 { y_p } else { y_r }),
            _ => None,
        };

        // The output is the identity if the input is the identity
        let x_out_val = x_s_val.and_then(|x_s| {
            self.is_identity
                .get_value()
                .map(|b| if b { C::Base::zero() } else { x_s })
        });
        let y_out_val = y_s_val.and_then(|y_s| {
            self.is_identity
                .get_value()
                .map(|b| if b { C::Base::zero() } else { y_s })
        });

        let x_out = AllocatedNum::alloc(cs.namespace(|| "x_out"), || {
            x_out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_out = AllocatedNum::alloc(cs.namespace(|| "y_out"), || {
            y_out_val.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let x_p_lc = x_p.lc(&mut cs);
        let y_p_lc = y_p.lc(&mut cs);
        let x_r_lc = x_r.lc(&mut cs);
        let y_r_lc = y_r.lc(&mut cs);

        //
        // Constraints
        //

        // (x_p - x_r) * k_0 = (x_s - x_r)
        let (j_var, k_var, l_var) = cs.multiply(|| {
            let x_p = x_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_r = x_r_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_s = x_s_val.ok_or(SynthesisError::AssignmentMissing)?;
            let k_0 = k_0_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_p - &x_r, k_0.into(), x_s - &x_r))
        })?;
        cs.enforce_zero(x_p_lc - &x_r_lc - j_var);
        cs.enforce_zero(LinearCombination::from(k_0_var) - k_var);
        let x_s_lc = LinearCombination::from(l_var) + &x_r_lc;

        // (y_p - y_r) * k_0 = (y_s - y_r)
        let (m_var, n_var, o_var) = cs.multiply(|| {
            let y_p = y_p_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_r = y_r_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_s = y_s_val.ok_or(SynthesisError::AssignmentMissing)?;
            let k_0 = k_0_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y_p - &y_r, k_0.into(), y_s - &y_r))
        })?;
        cs.enforce_zero(y_p_lc - &y_r_lc - m_var);
        cs.enforce_zero(LinearCombination::from(k_0_var) - n_var);
        let y_s_lc = LinearCombination::from(o_var) + &y_r_lc;

        // x_s * (1 - is_identity) = x_out
        let (p_var, q_var, r_var) = cs.multiply(|| {
            let x_s = x_s_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_out = x_out_val.ok_or(SynthesisError::AssignmentMissing)?;
            let is_identity = self
                .is_identity
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;

            Ok((x_s, (!is_identity).into(), x_out))
        })?;
        cs.enforce_zero(x_s_lc - p_var);
        cs.enforce_zero(self.is_identity.not().lc(CS::ONE, Coeff::One) - q_var);
        cs.enforce_zero(x_out.lc() - r_var);

        // y_s * (1 - is_identity) = x_out
        let (s_var, t_var, u_var) = cs.multiply(|| {
            let y_s = y_s_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_out = y_out_val.ok_or(SynthesisError::AssignmentMissing)?;
            let is_identity = self
                .is_identity
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;

            Ok((y_s, (!is_identity).into(), y_out))
        })?;
        cs.enforce_zero(y_s_lc - s_var);
        cs.enforce_zero(self.is_identity.not().lc(CS::ONE, Coeff::One) - t_var);
        cs.enforce_zero(y_out.lc() - u_var);

        Ok(CurvePoint {
            x: x_out.into(),
            y: y_out.into(),
            is_identity: self.is_identity.clone(),
        })
    }

    fn inv_helper<CS: ConstraintSystem<C::Base>, F>(
        &self,
        mut cs: CS,
        other: &[AllocatedBit],
        mul_func: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce(&mut CS, &Self) -> Result<Self, SynthesisError>,
    {
        let p = self
            .x
            .value()
            .and_then(|x| self.y.value().map(|y| C::from_xy(x, y).unwrap()))
            .ok_or(SynthesisError::AssignmentMissing);

        let mut mulby = C::Scalar::zero();
        for bit in other.iter().rev() {
            mulby = mulby + &mulby;
            if let Some(bit) = bit.get_value() {
                if bit {
                    mulby = mulby + &C::Scalar::one();
                }
            }
        }

        let inverted_val = p.map(|p| {
            let inv = p * mulby.invert().unwrap();
            let coords = inv.get_xy();
            if coords.is_some().into() {
                let (x, y) = coords.unwrap();
                (x, y, false)
            } else {
                (C::Base::zero(), C::Base::zero(), true)
            }
        });

        let x_inv_val = inverted_val.map(|(x, _, _)| x);
        let y_inv_val = inverted_val.map(|(_, y, _)| y);
        let is_identity_inv_val = inverted_val.map(|(_, _, b)| b);

        let x_inv = AllocatedNum::alloc(cs.namespace(|| "x_inv"), || x_inv_val)?;
        let y_inv = AllocatedNum::alloc(cs.namespace(|| "y_inv"), || y_inv_val)?;
        let is_identity_inv =
            AllocatedBit::alloc(cs.namespace(|| "inv_is_identity"), || is_identity_inv_val)?;

        let inverted = CurvePoint {
            x: x_inv.into(),
            y: y_inv.into(),
            is_identity: is_identity_inv.into(),
        };

        let calculated = mul_func(&mut cs, &inverted)?;

        let orig_x_lc = self.x.lc(&mut cs);
        let orig_y_lc = self.y.lc(&mut cs);
        let calculated_x_lc = calculated.x.lc(&mut cs);
        let calculated_y_lc = calculated.y.lc(&mut cs);

        cs.enforce_zero(orig_x_lc - &calculated_x_lc);
        cs.enforce_zero(orig_y_lc - &calculated_y_lc);
        cs.enforce_zero(
            self.is_identity.lc(CS::ONE, Coeff::One)
                - &calculated.is_identity.lc(CS::ONE, Coeff::One),
        );

        Ok(inverted)
    }

    /// Multiply by the inverse of a little-endian scalar.
    pub fn multiply_inv<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        self.inv_helper(cs, other, |cs, inverted| inverted.multiply(cs, other))
    }

    /// Multiply by the inverse of a little-endian scalar.
    ///
    /// Requires that the top bit of other is set.
    pub fn multiply_inv_fast<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: CS,
        other: &[AllocatedBit],
    ) -> Result<Self, SynthesisError> {
        self.inv_helper(cs, other, |cs, inverted| inverted.multiply_fast(cs, other))
    }
}

#[cfg(test)]
mod test {
    use super::CurvePoint;
    use crate::{
        circuits::{is_satisfied, Circuit, Coeff, ConstraintSystem, SynthesisError},
        curves::{Curve, Ec1},
        fields::{Field, Fp, Fq},
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
                let _ = CurvePoint::witness(cs.namespace(|| "one"), || Ok(Ec1::one()))?;
                let _ = CurvePoint::witness(cs.namespace(|| "zero"), || Ok(Ec1::zero()))?;

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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let one_coords = one.get_xy().unwrap();

                let p1 = CurvePoint::witness(cs.namespace(|| "one"), || Ok(one))?;
                let (x1, y1) = p1.get_xy();
                let x1_lc = x1.lc(&mut cs);
                let y1_lc = y1.lc(&mut cs);
                cs.enforce_zero(x1_lc - (Coeff::Full(one_coords.0), CS::ONE));
                cs.enforce_zero(y1_lc - (Coeff::Full(one_coords.1), CS::ONE));

                let p2 = CurvePoint::witness(cs.namespace(|| "zero"), || Ok(Ec1::zero()))?;
                let (x2, y2) = p2.get_xy();
                let x2_lc = x2.lc(&mut cs);
                let y2_lc = y2.lc(&mut cs);
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
    fn conditional_negation() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let two = Ec1::one().double();
                let negtwo = -two;

                let (two_x, two_y) = two.get_xy().unwrap();
                let (negtwo_x, negtwo_y) = negtwo.get_xy().unwrap();

                let p = CurvePoint::<Ec1>::constant(two_x, two_y);

                let ppos =
                    p.conditional_neg(cs.namespace(|| "no negation"), &Boolean::constant(false))?;
                let (ppos_x, ppos_y) = ppos.get_xy();
                let ppos_x_lc = ppos_x.lc(&mut cs);
                let ppos_y_lc = ppos_y.lc(&mut cs);
                cs.enforce_zero(ppos_x_lc - (Coeff::Full(two_x), CS::ONE));
                cs.enforce_zero(ppos_y_lc - (Coeff::Full(two_y), CS::ONE));

                let pneg =
                    p.conditional_neg(cs.namespace(|| "negation"), &Boolean::constant(true))?;
                let (pneg_x, pneg_y) = pneg.get_xy();
                let pneg_x_lc = pneg_x.lc(&mut cs);
                let pneg_y_lc = pneg_y.lc(&mut cs);
                cs.enforce_zero(pneg_x_lc - (Coeff::Full(negtwo_x), CS::ONE));
                cs.enforce_zero(pneg_y_lc - (Coeff::Full(negtwo_y), CS::ONE));

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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let three = one + two;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (three_x, three_y) = three.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p3 = p1.add(cs.namespace(|| "1 + 2"), &p2)?;
                let (p3_x, p3_y) = p3.get_xy();
                let p3_x_lc = p3_x.lc(&mut cs);
                let p3_y_lc = p3_y.lc(&mut cs);
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
    fn two_plus_negative_two() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let two = Ec1::one().double();
                let negtwo = -two;

                let (two_x, two_y) = two.get_xy().unwrap();
                let (negtwo_x, negtwo_y) = negtwo.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(two_x, two_y);
                let p2 = CurvePoint::<Ec1>::constant(negtwo_x, negtwo_y);

                let psum = p1.add(cs.namespace(|| "2 + (-2)"), &p2)?;
                let (psum_x, psum_y) = psum.get_xy();
                let psum_x_lc = psum_x.lc(&mut cs);
                let psum_y_lc = psum_y.lc(&mut cs);
                cs.enforce_zero(psum_x_lc);
                cs.enforce_zero(psum_y_lc);

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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let zero = Ec1::zero();
                let one = Ec1::one();

                let (one_x, one_y) = one.get_xy().unwrap();

                let p0 = CurvePoint::witness(cs.namespace(|| "0"), || Ok(zero))?;
                let p1 = CurvePoint::witness(cs.namespace(|| "1"), || Ok(one))?;

                let psum = p1.add(cs.namespace(|| "1 + 0"), &p0)?;
                let (psum_x, psum_y) = psum.get_xy();
                let psum_x_lc = psum_x.lc(&mut cs);
                let psum_y_lc = psum_y.lc(&mut cs);
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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let zero = Ec1::zero();
                let one = Ec1::one();
                let two = one.double();

                let (two_x, two_y) = two.get_xy().unwrap();

                let p0 = CurvePoint::witness(cs.namespace(|| "0"), || Ok(zero))?;
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let psum = p0.add(cs.namespace(|| "0 + 2"), &p2)?;
                let (psum_x, psum_y) = psum.get_xy();
                let psum_x_lc = psum_x.lc(&mut cs);
                let psum_y_lc = psum_y.lc(&mut cs);
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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let zero = Ec1::zero();
                let p0 = CurvePoint::witness(cs.namespace(|| "0"), || Ok(zero))?;

                let psum = p0.add(cs.namespace(|| "0 + 0"), &p0)?;
                let (psum_x, psum_y) = psum.get_xy();
                let psum_x_lc = psum_x.lc(&mut cs);
                let psum_y_lc = psum_y.lc(&mut cs);
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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let three = one + two;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (three_x, three_y) = three.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p3a = p1.add_conditionally(
                    cs.namespace(|| "true ? 1 + 2"),
                    &p2,
                    &Boolean::constant(true),
                )?;
                let (p3a_x, p3a_y) = p3a.get_xy();
                let p3a_x_lc = p3a_x.lc(&mut cs);
                let p3a_y_lc = p3a_y.lc(&mut cs);
                cs.enforce_zero(p3a_x_lc - (Coeff::Full(three_x), CS::ONE));
                cs.enforce_zero(p3a_y_lc - (Coeff::Full(three_y), CS::ONE));

                let p3b = p1.add_conditionally(
                    cs.namespace(|| "false ? 1 + 2"),
                    &p2,
                    &Boolean::constant(false),
                )?;
                let (p3b_x, p3b_y) = p3b.get_xy();
                let p3b_x_lc = p3b_x.lc(&mut cs);
                let p3b_y_lc = p3b_y.lc(&mut cs);
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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let three = one + two;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (three_x, three_y) = three.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p3a = p1.add_conditionally_incomplete(
                    cs.namespace(|| "true ? 1 + 2"),
                    &p2,
                    &Boolean::constant(true),
                )?;
                let (p3a_x, p3a_y) = p3a.get_xy();
                let p3a_x_lc = p3a_x.lc(&mut cs);
                let p3a_y_lc = p3a_y.lc(&mut cs);
                cs.enforce_zero(p3a_x_lc - (Coeff::Full(three_x), CS::ONE));
                cs.enforce_zero(p3a_y_lc - (Coeff::Full(three_y), CS::ONE));

                let p3b = p1.add_conditionally_incomplete(
                    cs.namespace(|| "false ? 1 + 2"),
                    &p2,
                    &Boolean::constant(false),
                )?;
                let (p3b_x, p3b_y) = p3b.get_xy();
                let p3b_x_lc = p3b_x.lc(&mut cs);
                let p3b_y_lc = p3b_y.lc(&mut cs);
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
    fn double() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let two = Ec1::one().double();
                let four = two.double();

                let (two_x, two_y) = two.get_xy().unwrap();
                let (four_x, four_y) = four.get_xy().unwrap();

                let p = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p_dbl = p.double(cs.namespace(|| "[2] 2"))?;
                let (p_dbl_x, p_dbl_y) = p_dbl.get_xy();
                let p_dbl_x_lc = p_dbl_x.lc(&mut cs);
                let p_dbl_y_lc = p_dbl_y.lc(&mut cs);
                cs.enforce_zero(p_dbl_x_lc - (Coeff::Full(four_x), CS::ONE));
                cs.enforce_zero(p_dbl_y_lc - (Coeff::Full(four_y), CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn double_identity() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let p = CurvePoint::<Ec1>::identity();

                let p_dbl = p.double(cs.namespace(|| "[2] 0"))?;
                let (p_dbl_x, p_dbl_y) = p_dbl.get_xy();
                let p_dbl_x_lc = p_dbl_x.lc(&mut cs);
                let p_dbl_y_lc = p_dbl_y.lc(&mut cs);
                cs.enforce_zero(p_dbl_x_lc);
                cs.enforce_zero(p_dbl_y_lc);

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn double_and_add() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let two = one.double();
                let five = two.double() + one;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (two_x, two_y) = two.get_xy().unwrap();
                let (five_x, five_y) = five.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);
                let p2 = CurvePoint::<Ec1>::constant(two_x, two_y);

                let p5 = p2.double_and_add_incomplete(cs.namespace(|| "[2] 2 + 1"), &p1)?;

                let (p5_x, p5_y) = p5.get_xy();
                let p5_x_lc = p5_x.lc(&mut cs);
                let p5_y_lc = p5_y.lc(&mut cs);
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
    fn double_identity_and_add_identity() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let p = CurvePoint::<Ec1>::identity();

                let p_res = p.double_and_add_incomplete(cs.namespace(|| "[2] 0 + 0"), &p)?;

                let (p_res_x, p_res_y) = p_res.get_xy();
                let p_res_x_lc = p_res_x.lc(&mut cs);
                let p_res_y_lc = p_res_y.lc(&mut cs);
                cs.enforce_zero(p_res_x_lc);
                cs.enforce_zero(p_res_y_lc);

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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let five = one.double().double() + one;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (five_x, five_y) = five.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);

                let scalar5 = [
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 0"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 1"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 2"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 3"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 4"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 5"), || Ok(false))?,
                ];

                let p5 = p1.multiply(cs.namespace(|| "[5] 1"), &scalar5)?;
                let (p5_x, p5_y) = p5.get_xy();
                let p5_x_lc = p5_x.lc(&mut cs);
                let p5_y_lc = p5_y.lc(&mut cs);
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
    fn multiply_fast() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let five = one.double().double() + one;

                let (one_x, one_y) = one.get_xy().unwrap();
                let (five_x, five_y) = five.get_xy().unwrap();
                println!("five.x = {:?}", five_x);
                println!("five.y = {:?}", five_y);

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);

                let scalar5 = [
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 0"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 1"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 2"), || Ok(true))?,
                ];

                let p5 = p1.multiply_fast(cs.namespace(|| "[5] 1"), &scalar5)?;
                let (p5_x, p5_y) = p5.get_xy();
                if let (Some(x), Some(y)) = (p5_x.value(), p5_y.value()) {
                    println!("p5.x = {:?}", x);
                    println!("p5.y = {:?}", y);
                }
                let p5_x_lc = p5_x.lc(&mut cs);
                let p5_y_lc = p5_y.lc(&mut cs);
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
    fn multiply_fast_identity() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let p = CurvePoint::<Ec1>::identity();

                let scalar5 = [
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 0"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 1"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 2"), || Ok(true))?,
                ];

                let p_res = p.multiply_fast(cs.namespace(|| "[5] 0"), &scalar5)?;
                let (p_res_x, p_res_y) = p_res.get_xy();
                let p_res_x_lc = p_res_x.lc(&mut cs);
                let p_res_y_lc = p_res_y.lc(&mut cs);
                cs.enforce_zero(p_res_x_lc);
                cs.enforce_zero(p_res_y_lc);

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
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let invfive = one * Fq::from(5).invert().unwrap();

                let (one_x, one_y) = one.get_xy().unwrap();
                let (invfive_x, invfive_y) = invfive.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);

                let scalar5 = [
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 0"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 1"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 2"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 3"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 4"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 5"), || Ok(false))?,
                ];

                let pinv5 = p1.multiply_inv(cs.namespace(|| "[5^-1] 1"), &scalar5)?;
                let (pinv5_x, pinv5_y) = pinv5.get_xy();
                let pinv5_x_lc = pinv5_x.lc(&mut cs);
                let pinv5_y_lc = pinv5_y.lc(&mut cs);
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

    #[test]
    fn multiply_inv_fast() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let one = Ec1::one();
                let invfive = one * Fq::from(5).invert().unwrap();

                let (one_x, one_y) = one.get_xy().unwrap();
                let (invfive_x, invfive_y) = invfive.get_xy().unwrap();

                let p1 = CurvePoint::<Ec1>::constant(one_x, one_y);

                let scalar5 = [
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 0"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 1"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 2"), || Ok(true))?,
                ];

                let pinv5 = p1.multiply_inv_fast(cs.namespace(|| "[5^-1] 1"), &scalar5)?;
                let (pinv5_x, pinv5_y) = pinv5.get_xy();
                let pinv5_x_lc = pinv5_x.lc(&mut cs);
                let pinv5_y_lc = pinv5_y.lc(&mut cs);
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

    #[test]
    fn multiply_inv_fast_identity() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                mut cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let p = CurvePoint::<Ec1>::identity();

                let scalar5 = [
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 0"), || Ok(true))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 1"), || Ok(false))?,
                    AllocatedBit::alloc(cs.namespace(|| "5 bit 2"), || Ok(true))?,
                ];

                let pinv5 = p.multiply_inv_fast(cs.namespace(|| "[5^-1] 0"), &scalar5)?;
                let (pinv5_x, pinv5_y) = pinv5.get_xy();
                let pinv5_x_lc = pinv5_x.lc(&mut cs);
                let pinv5_y_lc = pinv5_y.lc(&mut cs);
                cs.enforce_zero(pinv5_x_lc);
                cs.enforce_zero(pinv5_y_lc);

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }
}
