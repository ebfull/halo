use super::AllocatedNum;
use super::{Boolean, Num};
use crate::{
    circuits::{Coeff, ConstraintSystem, LinearCombination, SynthesisError},
    fields::Field,
    Curve,
};
use subtle::CtOption;

#[derive(Debug)]
pub struct CurvePoint<C: Curve> {
    x: Num<C::Base>,
    y: Num<C::Base>,
}

impl<C: Curve> CurvePoint<C> {
    pub fn constant(x: C::Base, y: C::Base) -> Self {
        CurvePoint {
            x: Num::constant(x),
            y: Num::constant(y),
        }
    }

    fn get_point(&self) -> Option<CtOption<C>> {
        self.x
            .value()
            .and_then(|x| self.y.value().and_then(|y| Some(C::from_xy(x, y))))
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
        })
    }
}

#[cfg(test)]
mod test {
    use super::CurvePoint;
    use crate::{
        circuits::{is_satisfied, Circuit, ConstraintSystem, SynthesisError},
        curves::{Curve, Ec1},
        fields::Fp,
        gadgets::boolean::Boolean,
        Basic,
    };

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
}
