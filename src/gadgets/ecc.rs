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
/// Internally it is represented with coordinates that always satisfy the curve
/// equation, and a [`Boolean`] tracking whether it is the identity.
#[derive(Debug)]
pub struct CurvePoint<C: Curve> {
    x: Num<C::Base>,
    y: Num<C::Base>,

    /// Whether or not this curve point actually represents the identity.
    is_identity: Boolean,
}

impl<C: Curve> CurvePoint<C> {
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
        // it internally as C::one() which does satisfy the curve equation.
        let point = point().map(|p| {
            let coords = p.get_xy();
            if coords.is_some().into() {
                let (x, y) = coords.unwrap();
                (x, y, false)
            } else {
                let (x, y) = C::one().get_xy().unwrap();
                (x, y, true)
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

        cs.enforce_zero(LinearCombination::from(i_var) + (Coeff::Full(C::b()), CS::ONE) - c_var);

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
    ) -> Result<(AllocatedNum<C::Base>, AllocatedNum<C::Base>), SynthesisError> {
        // We want to constrain the output to (0, 0) if is_identity is true, and
        // (x, y) if is_identity is false. We do this with two selection constraints:
        //
        // x_out = (1 - b) * x
        // y_out = (1 - b) * y

        let x_val = self.x.value();
        let y_val = self.y.value();
        let bit_val = self.is_identity.not().get_value().map(|b| {
            if b {
                C::Base::one()
            } else {
                C::Base::zero()
            }
        });
        let x_out_val = self
            .is_identity
            .not()
            .get_value()
            .and_then(|b| x_val.map(|x| if b { x } else { C::Base::zero() }));
        let y_out_val = self
            .is_identity
            .not()
            .get_value()
            .and_then(|b| y_val.map(|y| if b { y } else { C::Base::zero() }));

        let x_out = AllocatedNum::alloc(cs, || x_out_val.ok_or(SynthesisError::AssignmentMissing))?;
        let y_out = AllocatedNum::alloc(cs, || y_out_val.ok_or(SynthesisError::AssignmentMissing))?;

        let x_lc = self.x.lc(cs);
        let y_lc = self.y.lc(cs);
        let is_identity_lc = self.is_identity.not().lc(CS::ONE, Coeff::One);

        let (a_var, b_var, c_var) = cs.multiply(|| {
            let x = x_val.ok_or(SynthesisError::AssignmentMissing)?;
            let x_out = x_out_val.ok_or(SynthesisError::AssignmentMissing)?;
            let b = bit_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((b, x, x_out))
        })?;
        cs.enforce_zero(is_identity_lc.clone() - a_var);
        cs.enforce_zero(x_lc - b_var);
        cs.enforce_zero(x_out.lc() - c_var);

        let (s_var, t_var, u_var) = cs.multiply(|| {
            let y = y_val.ok_or(SynthesisError::AssignmentMissing)?;
            let y_out = y_out_val.ok_or(SynthesisError::AssignmentMissing)?;
            let b = bit_val.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((b, y, y_out))
        })?;
        cs.enforce_zero(is_identity_lc - s_var);
        cs.enforce_zero(y_lc - t_var);
        cs.enforce_zero(y_out.lc() - u_var);

        Ok((x_out, y_out))
    }

    /// Adds `self` to `other`, returning the result unless
    /// condition is false, in which case it returns `self`.
    ///
    /// Assumes no edge cases will occur.
    pub fn add_conditionally<CS: ConstraintSystem<C::Base>>(
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

    /// Adds a point to another point and handles all
    /// edge cases
    pub fn add<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        // If one is identity, return the other
        unimplemented!()
    }

    /// Multiply by a scalar
    pub fn multiply<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    /// Multiply by the inverse of a scalar
    pub fn multiply_inv<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        // Will run into edge cases if during it we have an addition that runs into an edge case
        unimplemented!()
    }
}

#[cfg(test)]
mod test {
    use super::CurvePoint;
    use crate::{
        circuits::{is_satisfied, Circuit, Coeff, ConstraintSystem, SynthesisError},
        curves::{Curve, Ec1},
        fields::Fp,
        gadgets::boolean::Boolean,
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
    fn test_add_conditionally() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let p1 = {
                    let (x1, y1) = Ec1::one().get_xy().unwrap();
                    CurvePoint::<Ec1>::constant(x1, y1)
                };
                let p2 = {
                    let (x1, y1) = Ec1::one().double().get_xy().unwrap();
                    CurvePoint::<Ec1>::constant(x1, y1)
                };

                let p3a = p1.add_conditionally(cs, &p2, &Boolean::constant(true))?;
                let p3b = p1.add_conditionally(cs, &p2, &Boolean::constant(false))?;

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
                cs.enforce_zero(x1.lc() - (Coeff::Full(one_coords.0), CS::ONE));
                cs.enforce_zero(y1.lc() - (Coeff::Full(one_coords.1), CS::ONE));

                let p2 = CurvePoint::witness(cs, || Ok(Ec1::zero()))?;
                let (x2, y2) = p2.get_xy(cs)?;
                cs.enforce_zero(x2.lc() - (Coeff::Zero, CS::ONE));
                cs.enforce_zero(y2.lc() - (Coeff::Zero, CS::ONE));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }
}
