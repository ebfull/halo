use crate::*;

#[derive(Debug)]
pub struct AllocatedBit {
    value: Option<bool>,
    var: Variable,
}

impl AllocatedBit {
    pub fn alloc<F: Field, CS: ConstraintSystem<F>, FF>(
        cs: &mut CS,
        value: FF,
    ) -> Result<Self, SynthesisError>
    where
        FF: FnOnce() -> Result<bool, SynthesisError>,
    {
        let mut final_value = None;
        let (a, b, c) = cs.multiply(|| {
            let v = value()?;
            final_value = Some(v);
            let fe = if v { F::one() } else { F::zero() };

            Ok((fe, fe, fe))
        })?;

        cs.enforce_zero(LinearCombination::from(a) - b);
        cs.enforce_zero(LinearCombination::from(b) - c);

        Ok(AllocatedBit {
            value: final_value,
            var: a,
        })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor<F, CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "xor result",
            || {
                let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

                if a_val ^ b_val {
                    result_value = Some(true);

                    Ok(F::one())
                } else {
                    result_value = Some(false);

                    Ok(F::zero())
                }
            },
        )?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        //
        // d * e = f
        // d = 2a
        // e = b
        // f = a + b - c
        let (d_var, e_var, f_var) = cs.multiply(|| {
            let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;
            let c_val = result_value.ok_or(SynthesisError::AssignmentMissing)?;

            let a_val = if a_val { F::one() } else { F::zero() };
            let b_val = if b_val { F::one() } else { F::zero() };
            let c_val = if c_val { F::one() } else { F::zero() };

            let d_val = a_val + a_val;
            let e_val = b_val;
            let f_val = a_val + b_val - c_val;

            Ok((d_val, e_val, f_val))
        })?;
        cs.enforce_zero(LinearCombination::from(a.var) + a.var - d_var);
        cs.enforce_zero(LinearCombination::from(b.var) - e_var);
        cs.enforce_zero(LinearCombination::from(a.var) + b.var - result_var - f_var);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and<F, CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        let (a_var, b_var, result_var) = cs.multiply(|| {
            let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

            if a_val & b_val {
                result_value = Some(true);

                Ok((F::one(), F::one(), F::one()))
            } else {
                result_value = Some(false);

                Ok((
                    if a_val { F::one() } else { F::zero() },
                    if b_val { F::one() } else { F::zero() },
                    F::zero(),
                ))
            }
        })?;
        cs.enforce_zero(LinearCombination::from(a_var) - a.var);
        cs.enforce_zero(LinearCombination::from(b_var) - b.var);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<F, CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        let (a_var, not_b_var, result_var) = cs.multiply(|| {
            let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

            result_value = Some(a_val & !b_val);

            Ok((
                if a_val { F::one() } else { F::zero() },
                if b_val { F::zero() } else { F::one() },
                if result_value.unwrap() {
                    F::one()
                } else {
                    F::zero()
                },
            ))
        })?;
        cs.enforce_zero(LinearCombination::from(a_var) - a.var);
        cs.enforce_zero(LinearCombination::from(not_b_var) + b.var - CS::ONE);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<F, CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        let (not_a_var, not_b_var, result_var) = cs.multiply(|| {
            let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

            result_value = Some(!a_val & !b_val);

            Ok((
                if a_val { F::zero() } else { F::one() },
                if b_val { F::zero() } else { F::one() },
                if result_value.unwrap() {
                    F::one()
                } else {
                    F::zero()
                },
            ))
        })?;
        cs.enforce_zero(LinearCombination::from(not_a_var) + a.var - CS::ONE);
        cs.enforce_zero(LinearCombination::from(not_b_var) + b.var - CS::ONE);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }
}

pub fn unpack_fe<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    num: &AllocatedNum<F>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let values = match num.value {
        Some(value) => {
            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);
            let bytes = value.to_bytes();

            for byte in &bytes[0..] {
                for i in 0..8 {
                    let bit = ((*byte >> i) & 1) == 1;
                    tmp.push(Some(bit));
                }
            }

            tmp
        }
        None => vec![None; F::NUM_BITS as usize],
    };

    let mut bools = vec![];
    for value in values {
        bools.push(AllocatedBit::alloc(cs, || {
            value.ok_or(SynthesisError::AssignmentMissing)
        })?);
    }

    // Check that it's equal.
    let mut lc = LinearCombination::zero();
    let mut cur = F::one();
    for b in &bools {
        lc = lc + (Coeff::from(cur), b.var);
        cur = cur + cur;
    }
    cs.enforce_zero(lc - num.var);

    Ok(bools)
}

#[cfg(test)]
mod test {
    use super::AllocatedBit;
    use crate::{fields::Fp, is_satisfied, Basic, Circuit, ConstraintSystem, SynthesisError};

    #[test]
    fn test_allocated_bit() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let _ = AllocatedBit::alloc(cs, || Ok(true))?;

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn test_xor() {
        struct TestCircuit {
            a_val: bool,
            b_val: bool,
        };

        impl TestCircuit {
            fn new(a_val: bool, b_val: bool) -> Self {
                TestCircuit { a_val, b_val }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), || Ok(self.a_val))?;
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), || Ok(self.b_val))?;
                let c = AllocatedBit::xor(cs, &a, &b)?;
                assert_eq!(c.value.unwrap(), self.a_val ^ self.b_val);

                Ok(())
            }
        }

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                assert_eq!(
                    is_satisfied::<_, _, Basic>(&TestCircuit::new(*a_val, *b_val), &[]),
                    Ok(true)
                );
            }
        }
    }

    #[test]
    fn test_and() {
        struct TestCircuit {
            a_val: bool,
            b_val: bool,
        };

        impl TestCircuit {
            fn new(a_val: bool, b_val: bool) -> Self {
                TestCircuit { a_val, b_val }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), || Ok(self.a_val))?;
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), || Ok(self.b_val))?;
                let c = AllocatedBit::and(cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), self.a_val & self.b_val);

                Ok(())
            }
        }

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                assert_eq!(
                    is_satisfied::<_, _, Basic>(&TestCircuit::new(*a_val, *b_val), &[]),
                    Ok(true)
                );
            }
        }
    }

    #[test]
    fn test_and_not() {
        struct TestCircuit {
            a_val: bool,
            b_val: bool,
        };

        impl TestCircuit {
            fn new(a_val: bool, b_val: bool) -> Self {
                TestCircuit { a_val, b_val }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), || Ok(self.a_val))?;
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), || Ok(self.b_val))?;
                let c = AllocatedBit::and_not(cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), self.a_val & !self.b_val);

                Ok(())
            }
        }

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                assert_eq!(
                    is_satisfied::<_, _, Basic>(&TestCircuit::new(*a_val, *b_val), &[]),
                    Ok(true)
                );
            }
        }
    }

    #[test]
    fn test_nor() {
        struct TestCircuit {
            a_val: bool,
            b_val: bool,
        };

        impl TestCircuit {
            fn new(a_val: bool, b_val: bool) -> Self {
                TestCircuit { a_val, b_val }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), || Ok(self.a_val))?;
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), || Ok(self.b_val))?;
                let c = AllocatedBit::nor(cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !self.a_val & !self.b_val);

                Ok(())
            }
        }

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                assert_eq!(
                    is_satisfied::<_, _, Basic>(&TestCircuit::new(*a_val, *b_val), &[]),
                    Ok(true)
                );
            }
        }
    }
}
