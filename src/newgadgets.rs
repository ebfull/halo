use crate::*;
use crate::newcircuits::*;
use crate::fields::*;

#[derive(Clone, Debug)]
pub struct AllocatedBit {
    value: Option<bool>,
    var: Variable,
}

impl AllocatedBit {
    pub fn one<F, CS>(_cs: CS) -> Self
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        AllocatedBit {
            value: Some(true),
            var: CS::ONE,
        }
    }

    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.var
    }

    /// Allocates this bit but does not check that it's a bit, call
    /// `checked()` to do this later. This is a hack to ensure that
    /// the first linear constraints in our proof verification circuits
    /// are always input constraints.
    pub fn alloc_unchecked<F: Field, CS: ConstraintSystem<F>, FF>(
        mut cs: CS,
        value: FF,
    ) -> Result<Self, SynthesisError>
    where
        FF: FnOnce() -> Result<bool, SynthesisError>,
    {
        let mut final_value = None;
        let var = cs.alloc(
            || {
                let v = value()?;
                final_value = Some(v);
                Ok(v.into())
            },
        )?;

        Ok(AllocatedBit {
            value: final_value,
            var,
        })
    }

    pub fn check<F: Field, CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let (a, b, c) = cs.multiply(
            || {
                let val = self.value.ok_or(SynthesisError::AssignmentMissing)?;
                let val: F = val.into();

                Ok((val, val, val))
            },
        )?;

        cs.enforce_zero(LinearCombination::from(a) - self.var);
        cs.enforce_zero(LinearCombination::from(b) - self.var);
        cs.enforce_zero(LinearCombination::from(c) - self.var);

        Ok(())
    }

    pub fn alloc<F: Field, CS: ConstraintSystem<F>, FF>(
        mut cs: CS,
        value: FF,
    ) -> Result<Self, SynthesisError>
    where
        FF: FnOnce() -> Result<bool, SynthesisError>,
    {
        let mut final_value = None;
        let (a, b, c) = cs.multiply(
            || {
                let v = value()?;
                final_value = Some(v);
                let fe: F = v.into();

                Ok((fe, fe, fe))
            },
        )?;

        cs.enforce_zero(LinearCombination::from(a) - b);
        cs.enforce_zero(LinearCombination::from(b) - c);

        Ok(AllocatedBit {
            value: final_value,
            var: a,
        })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
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
        let (d_var, e_var, f_var) = cs.multiply(
            || {
                let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;
                let c_val = result_value.ok_or(SynthesisError::AssignmentMissing)?;

                let a_val: F = a_val.into();
                let b_val: F = b_val.into();
                let c_val: F = c_val.into();

                let d_val = a_val + a_val;
                let e_val = b_val;
                let f_val = a_val + b_val - c_val;

                Ok((d_val, e_val, f_val))
            },
        )?;
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
    pub fn and<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        let (a_var, b_var, result_var) = cs.multiply(
            || {
                let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

                if a_val & b_val {
                    result_value = Some(true);

                    Ok((F::one(), F::one(), F::one()))
                } else {
                    result_value = Some(false);

                    Ok((a_val.into(), b_val.into(), F::zero()))
                }
            },
        )?;
        cs.enforce_zero(LinearCombination::from(a_var) - a.var);
        cs.enforce_zero(LinearCombination::from(b_var) - b.var);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        let (a_var, not_b_var, result_var) = cs.multiply(
            || {
                let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

                result_value = Some(a_val & !b_val);

                Ok((a_val.into(), (!b_val).into(), result_value.unwrap().into()))
            },
        )?;
        cs.enforce_zero(LinearCombination::from(a_var) - a.var);
        cs.enforce_zero(LinearCombination::from(not_b_var) + b.var - CS::ONE);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        let (not_a_var, not_b_var, result_var) = cs.multiply(
            || {
                let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

                result_value = Some(!a_val & !b_val);

                Ok((
                    (!a_val).into(),
                    (!b_val).into(),
                    result_value.unwrap().into(),
                ))
            },
        )?;
        cs.enforce_zero(LinearCombination::from(not_a_var) + a.var - CS::ONE);
        cs.enforce_zero(LinearCombination::from(not_b_var) + b.var - CS::ONE);

        Ok(AllocatedBit {
            var: result_var,
            value: result_value,
        })
    }
}

/*
pub fn unpack_fe<F: Field, CS: ConstraintSystem<F>>(
    mut cs: CS,
    num: &Num<F>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let values = match num.value() {
        Some(value) => {
            let mut tmp = Vec::with_capacity(256);
            let bytes = value.to_bytes();

            for byte in &bytes[0..] {
                for i in 0..8 {
                    let bit = ((*byte >> i) & 1) == 1;
                    tmp.push(Some(bit));
                }
            }

            tmp
        }
        None => vec![None; 256],
    };

    let mut bools = vec![];
    for (i, value) in values.iter().enumerate() {
        bools.push(AllocatedBit::alloc(
            cs,
            || value.ok_or(SynthesisError::AssignmentMissing),
        )?);
    }

    // Check that it's equal.
    let mut lc = LinearCombination::zero();
    let mut cur = F::one();
    for b in &bools {
        lc = lc + (Coeff::from(cur), b.var);
        cur = cur + cur;
    }
    let num_lc = num.lc(&mut cs);
    cs.enforce_zero(lc - &num_lc);

    Ok(bools)
}
*/

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone, Debug)]
pub enum Boolean {
    /// Existential view of the boolean variable
    Is(AllocatedBit),
    /// Negated view of the boolean variable
    Not(AllocatedBit),
    /// Constant (not an allocated variable)
    Constant(bool),
}

impl Boolean {
    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false,
        }
    }

    pub fn enforce_equal<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        match (a, b) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(SynthesisError::Unsatisfiable)
                }
            }
            (&Boolean::Constant(true), a) | (a, &Boolean::Constant(true)) => {
                cs.enforce_zero(a.lc(CS::ONE, Coeff::One) - CS::ONE);

                Ok(())
            }
            (&Boolean::Constant(false), a) | (a, &Boolean::Constant(false)) => {
                cs.enforce_zero(a.lc(CS::ONE, Coeff::One));

                Ok(())
            }
            (a, b) => {
                cs.enforce_zero(a.lc(CS::ONE, Coeff::One) - &b.lc(CS::ONE, Coeff::One));

                Ok(())
            }
        }
    }

    pub fn get_value(&self) -> Option<bool> {
        match *self {
            Boolean::Constant(c) => Some(c),
            Boolean::Is(ref v) => v.get_value(),
            Boolean::Not(ref v) => v.get_value().map(|b| !b),
        }
    }

    pub fn lc<F: Field>(&self, one: Variable, coeff: Coeff<F>) -> LinearCombination<F> {
        match *self {
            Boolean::Constant(c) => {
                if c {
                    LinearCombination::<F>::zero() + (coeff, one)
                } else {
                    LinearCombination::<F>::zero()
                }
            }
            Boolean::Is(ref v) => LinearCombination::<F>::zero() + (coeff, v.get_variable()),
            Boolean::Not(ref v) => {
                LinearCombination::<F>::zero() + (coeff, one) - (coeff, v.get_variable())
            }
        }
    }

    /// Construct a boolean from a known constant
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// Return a negated interpretation of this boolean.
    pub fn not(&self) -> Self {
        match *self {
            Boolean::Constant(c) => Boolean::Constant(!c),
            Boolean::Is(ref v) => Boolean::Not(v.clone()),
            Boolean::Not(ref v) => Boolean::Is(v.clone()),
        }
    }

    /// Perform XOR over two boolean operands
    pub fn xor<'a, F, CS>(cs: CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_))
            | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Ok(Boolean::xor(cs, is, &not.not())?.not())
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b))
            | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::xor(cs, a, b)?))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a, F, CS>(cs: CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => {
                Ok(Boolean::Constant(false))
            }
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.clone()),
            // a AND (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not))
            | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Ok(Boolean::Is(AllocatedBit::and_not(cs, is, not)?))
            }
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::nor(cs, a, b)?))
            }
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::and(cs, a, b)?))
            }
        }
    }

    /// Computes (a and b) xor ((not a) and c)
    pub fn sha256_ch<'a, F, CS>(
        mut cs: CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self,
    ) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let ch_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor ((not a) and c)
                Some((a & b) ^ ((!a) & c))
            }
            _ => None,
        };

        match (a, b, c) {
            (&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(ch_value.expect("they're all constants")));
            }
            (&Boolean::Constant(false), _, c) => {
                // If a is false
                // (a and b) xor ((not a) and c)
                // equals
                // (false) xor (c)
                // equals
                // c
                return Ok(c.clone());
            }
            (a, &Boolean::Constant(false), c) => {
                // If b is false
                // (a and b) xor ((not a) and c)
                // equals
                // ((not a) and c)
                return Boolean::and(cs, &a.not(), &c);
            }
            (a, b, &Boolean::Constant(false)) => {
                // If c is false
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b)
                return Boolean::and(cs, &a, &b);
            }
            (a, b, &Boolean::Constant(true)) => {
                // If c is true
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b) xor (not a)
                // equals
                // not (a and (not b))
                return Ok(Boolean::and(cs, &a, &b.not())?.not());
            }
            (a, &Boolean::Constant(true), c) => {
                // If b is true
                // (a and b) xor ((not a) and c)
                // equals
                // a xor ((not a) and c)
                // equals
                // not ((not a) and (not c))
                return Ok(Boolean::and(cs, &a.not(), &c.not())?.not());
            }
            (&Boolean::Constant(true), _, _) => {
                // If a is true
                // (a and b) xor ((not a) and c)
                // equals
                // b xor ((not a) and c)
                // So we just continue!
            }
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_)) => {}
        }

        let ch = cs.alloc(
            || {
                ch_value
                    .ok_or(SynthesisError::AssignmentMissing)
                    .map(F::from)
            },
        )?;

        // a(b - c) = ch - c
        //
        // d * e = f
        // d = a
        // e = b - c
        // f = ch - c
        let (d_var, e_var, f_var) = cs.multiply(
            || {
                let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let c_val = c.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let ch_val = ch_value.ok_or(SynthesisError::AssignmentMissing)?;

                let a_val: F = a_val.into();
                let b_val: F = b_val.into();
                let c_val: F = c_val.into();
                let ch_val: F = ch_val.into();

                let d_val = a_val;
                let e_val = b_val - c_val;
                let f_val = ch_val - c_val;

                Ok((d_val, e_val, f_val))
            },
        )?;
        cs.enforce_zero(a.lc(CS::ONE, Coeff::One) - d_var);
        cs.enforce_zero(b.lc(CS::ONE, Coeff::One) - &c.lc(CS::ONE, Coeff::One) - e_var);
        cs.enforce_zero(LinearCombination::from(ch) - &c.lc(CS::ONE, Coeff::One) - f_var);

        Ok(AllocatedBit {
            value: ch_value,
            var: ch,
        }
        .into())
    }

    /// Computes (a and b) xor (a and c) xor (b and c)
    pub fn sha256_maj<'a, F, CS>(
        mut cs: CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self,
    ) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let maj_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor (a and c) xor (b and c)
                Some((a & b) ^ (a & c) ^ (b & c))
            }
            _ => None,
        };

        match (a, b, c) {
            (&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(maj_value.expect("they're all constants")));
            }
            (&Boolean::Constant(false), b, c) => {
                // If a is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b and c)
                return Boolean::and(cs, b, c);
            }
            (a, &Boolean::Constant(false), c) => {
                // If b is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and c)
                return Boolean::and(cs, a, c);
            }
            (a, b, &Boolean::Constant(false)) => {
                // If c is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b)
                return Boolean::and(cs, a, b);
            }
            (a, b, &Boolean::Constant(true)) => {
                // If c is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b) xor (a) xor (b)
                // equals
                // not ((not a) and (not b))
                return Ok(Boolean::and(cs, &a.not(), &b.not())?.not());
            }
            (a, &Boolean::Constant(true), c) => {
                // If b is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a) xor (a and c) xor (c)
                return Ok(Boolean::and(cs, &a.not(), &c.not())?.not());
            }
            (&Boolean::Constant(true), b, c) => {
                // If a is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b) xor (c) xor (b and c)
                return Ok(Boolean::and(cs, &b.not(), &c.not())?.not());
            }
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_)) => {}
        }

        let maj = cs.alloc(
            || {
                maj_value
                    .ok_or(SynthesisError::AssignmentMissing)
                    .map(F::from)
            },
        )?;

        // ¬(¬a ∧ ¬b) ∧ ¬(¬a ∧ ¬c) ∧ ¬(¬b ∧ ¬c)
        // (1 - ((1 - a) * (1 - b))) * (1 - ((1 - a) * (1 - c))) * (1 - ((1 - b) * (1 - c)))
        // (a + b - ab) * (a + c - ac) * (b + c - bc)
        // -2abc + ab + ac + bc
        // a (-2bc + b + c) + bc
        //
        // (b) * (c) = (bc)
        // (2bc - b - c) * (a) = bc - maj
        //
        // d * e = f
        // d = 2bc - b - c
        // e = a
        // f = bc - maj

        let bc = Self::and(&mut cs, b, c)?;

        let (d_var, e_var, f_var) = cs.multiply(
            || {
                let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let c_val = c.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let bc_val = bc.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let maj_val = maj_value.ok_or(SynthesisError::AssignmentMissing)?;

                let a_val: F = a_val.into();
                let b_val: F = b_val.into();
                let c_val: F = c_val.into();
                let bc_val: F = bc_val.into();
                let maj_val: F = maj_val.into();

                let d_val = bc_val + bc_val - b_val - c_val;
                let e_val = a_val;
                let f_val = bc_val - maj_val;

                Ok((d_val, e_val, f_val))
            },
        )?;
        cs.enforce_zero(
            bc.lc(CS::ONE, Coeff::One) + &bc.lc(CS::ONE, Coeff::One)
                - &b.lc(CS::ONE, Coeff::One)
                - &c.lc(CS::ONE, Coeff::One)
                - d_var,
        );
        cs.enforce_zero(a.lc(CS::ONE, Coeff::One) - e_var);
        cs.enforce_zero(bc.lc(CS::ONE, Coeff::One) - maj - f_var);

        Ok(AllocatedBit {
            value: maj_value,
            var: maj,
        }
        .into())
    }
}

impl From<AllocatedBit> for Boolean {
    fn from(b: AllocatedBit) -> Boolean {
        Boolean::Is(b)
    }
}