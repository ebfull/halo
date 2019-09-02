use crate::gadgets::num::AllocatedNum;
use crate::*;

#[derive(Clone, Debug)]
pub struct AllocatedBit {
    value: Option<bool>,
    var: Variable,
}

impl AllocatedBit {
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
    pub fn alloc_input_unchecked<F: Field, CS: ConstraintSystem<F>, FF>(
        cs: &mut CS,
        value: FF,
    ) -> Result<Self, SynthesisError>
    where
        FF: FnOnce() -> Result<bool, SynthesisError>,
    {
        let mut final_value = None;
        let var = cs.alloc_input(|| "", || {
            let v = value()?;
            final_value = Some(v);
            let fe = if v { F::one() } else { F::zero() };

            Ok(fe)
        })?;

        Ok(AllocatedBit {
            value: final_value,
            var: var,
        })
    }

    pub fn check<F: Field, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let (a, b, c) = cs.multiply(|| {
            let val = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let val = if val { F::one() } else { F::zero() };

            Ok((val, val, val))
        })?;

        cs.enforce_zero(LinearCombination::from(a) - self.var);
        cs.enforce_zero(LinearCombination::from(b) - self.var);
        cs.enforce_zero(LinearCombination::from(c) - self.var);

        Ok(())
    }

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
    let values = match num.get_value() {
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
    cs.enforce_zero(lc - num.get_variable());

    Ok(bools)
}

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone)]
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

    pub fn enforce_equal<F, CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
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
    pub fn xor<'a, F, CS>(cs: &mut CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
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
    pub fn and<'a, F, CS>(cs: &mut CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
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
        cs: &mut CS,
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
            || "ch",
            || {
                ch_value.ok_or(SynthesisError::AssignmentMissing).map(|v| {
                    if v {
                        F::one()
                    } else {
                        F::zero()
                    }
                })
            },
        )?;

        // a(b - c) = ch - c
        //
        // d * e = f
        // d = a
        // e = b - c
        // f = ch - c
        let (d_var, e_var, f_var) = cs.multiply(|| {
            let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let c_val = c.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let ch_val = ch_value.ok_or(SynthesisError::AssignmentMissing)?;

            let a_val = if a_val { F::one() } else { F::zero() };
            let b_val = if b_val { F::one() } else { F::zero() };
            let c_val = if c_val { F::one() } else { F::zero() };
            let ch_val = if ch_val { F::one() } else { F::zero() };

            let d_val = a_val;
            let e_val = b_val - c_val;
            let f_val = ch_val - c_val;

            Ok((d_val, e_val, f_val))
        })?;
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
        cs: &mut CS,
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
            || "maj",
            || {
                maj_value.ok_or(SynthesisError::AssignmentMissing).map(|v| {
                    if v {
                        F::one()
                    } else {
                        F::zero()
                    }
                })
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

        let bc = Self::and(cs.namespace(|| "b and c"), b, c)?;

        let (d_var, e_var, f_var) = cs.multiply(|| {
            let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let c_val = c.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let bc_val = bc.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let maj_val = maj_value.ok_or(SynthesisError::AssignmentMissing)?;

            let a_val = if a_val { F::one() } else { F::zero() };
            let b_val = if b_val { F::one() } else { F::zero() };
            let c_val = if c_val { F::one() } else { F::zero() };
            let bc_val = if bc_val { F::one() } else { F::zero() };
            let maj_val = if maj_val { F::one() } else { F::zero() };

            let d_val = bc_val + bc_val - b_val - c_val;
            let e_val = a_val;
            let f_val = bc_val - maj_val;

            Ok((d_val, e_val, f_val))
        })?;
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

#[cfg(test)]
mod test {
    use super::{AllocatedBit, Boolean};
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

    #[test]
    fn test_enforce_equal() {
        struct TestCircuit {
            a_const: bool,
            b_const: bool,
            a_bool: bool,
            b_bool: bool,
            a_neg: bool,
            b_neg: bool,
        };

        impl TestCircuit {
            fn new(
                a_const: bool,
                b_const: bool,
                a_bool: bool,
                b_bool: bool,
                a_neg: bool,
                b_neg: bool,
            ) -> Self {
                TestCircuit {
                    a_const,
                    b_const,
                    a_bool,
                    b_bool,
                    a_neg,
                    b_neg,
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut a = if self.a_const {
                    Boolean::Constant(self.a_bool)
                } else {
                    Boolean::from(AllocatedBit::alloc(cs.namespace(|| "a"), || {
                        Ok(self.a_bool)
                    })?)
                };
                let mut b = if self.b_const {
                    Boolean::Constant(self.b_bool)
                } else {
                    Boolean::from(AllocatedBit::alloc(cs.namespace(|| "b"), || {
                        Ok(self.b_bool)
                    })?)
                };

                if self.a_neg {
                    a = a.not();
                }
                if self.b_neg {
                    b = b.not();
                }

                Boolean::enforce_equal(cs, &a, &b)?;

                Ok(())
            }
        }

        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        assert_eq!(
                            is_satisfied::<_, _, Basic>(
                                &TestCircuit::new(false, false, a_bool, b_bool, a_neg, b_neg),
                                &[]
                            ),
                            Ok((a_bool ^ a_neg) == (b_bool ^ b_neg))
                        );

                        assert_eq!(
                            is_satisfied::<_, _, Basic>(
                                &TestCircuit::new(true, false, a_bool, b_bool, a_neg, b_neg),
                                &[]
                            ),
                            Ok((a_bool ^ a_neg) == (b_bool ^ b_neg))
                        );

                        assert_eq!(
                            is_satisfied::<_, _, Basic>(
                                &TestCircuit::new(false, true, a_bool, b_bool, a_neg, b_neg),
                                &[]
                            ),
                            Ok((a_bool ^ a_neg) == (b_bool ^ b_neg))
                        );

                        let circuit = TestCircuit::new(true, true, a_bool, b_bool, a_neg, b_neg);
                        if (a_bool ^ a_neg) == (b_bool ^ b_neg) {
                            assert_eq!(is_satisfied::<_, _, Basic>(&circuit, &[]), Ok(true));
                        } else {
                            assert_eq!(
                                is_satisfied::<_, _, Basic>(&circuit, &[]),
                                Err(SynthesisError::Unsatisfiable)
                            );
                        };
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_negation() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut b = Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?);

                match b {
                    Boolean::Is(_) => {}
                    _ => panic!("unexpected value"),
                }

                b = b.not();

                match b {
                    Boolean::Not(_) => {}
                    _ => panic!("unexpected value"),
                }

                b = b.not();

                match b {
                    Boolean::Is(_) => {}
                    _ => panic!("unexpected value"),
                }

                b = Boolean::constant(true);

                match b {
                    Boolean::Constant(true) => {}
                    _ => panic!("unexpected value"),
                }

                b = b.not();

                match b {
                    Boolean::Constant(false) => {}
                    _ => panic!("unexpected value"),
                }

                b = b.not();

                match b {
                    Boolean::Constant(true) => {}
                    _ => panic!("unexpected value"),
                }

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[derive(Copy, Clone, Debug)]
    enum OperandType {
        True,
        False,
        AllocatedTrue,
        AllocatedFalse,
        NegatedAllocatedTrue,
        NegatedAllocatedFalse,
    }

    impl OperandType {
        fn is_constant(&self) -> bool {
            match *self {
                OperandType::True => true,
                OperandType::False => true,
                OperandType::AllocatedTrue => false,
                OperandType::AllocatedFalse => false,
                OperandType::NegatedAllocatedTrue => false,
                OperandType::NegatedAllocatedFalse => false,
            }
        }

        fn val(&self) -> bool {
            match *self {
                OperandType::True => true,
                OperandType::False => false,
                OperandType::AllocatedTrue => true,
                OperandType::AllocatedFalse => false,
                OperandType::NegatedAllocatedTrue => false,
                OperandType::NegatedAllocatedFalse => true,
            }
        }
    }

    #[test]
    fn test_boolean_xor() {
        struct TestCircuit {
            first_operand: OperandType,
            second_operand: OperandType,
        };

        impl TestCircuit {
            fn new(first_operand: OperandType, second_operand: OperandType) -> Self {
                TestCircuit {
                    first_operand,
                    second_operand,
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Ok(Boolean::constant(true)),
                            OperandType::False => Ok(Boolean::constant(false)),
                            OperandType::AllocatedTrue => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?))
                            }
                            OperandType::AllocatedFalse => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?))
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?).not())
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?).not())
                            }
                        }
                    };

                    a = dyn_construct(self.first_operand, "a")?;
                    b = dyn_construct(self.second_operand, "b")?;
                }

                let c = Boolean::xor(cs, &a, &b)?;

                match (self.first_operand, self.second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Is(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    _ => panic!("this should never be encountered"),
                }

                Ok(())
            }
        }

        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                assert_eq!(
                    is_satisfied::<_, _, Basic>(
                        &TestCircuit::new(first_operand, second_operand),
                        &[]
                    ),
                    Ok(true)
                );
            }
        }
    }

    #[test]
    fn test_boolean_and() {
        struct TestCircuit {
            first_operand: OperandType,
            second_operand: OperandType,
        };

        impl TestCircuit {
            fn new(first_operand: OperandType, second_operand: OperandType) -> Self {
                TestCircuit {
                    first_operand,
                    second_operand,
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Ok(Boolean::constant(true)),
                            OperandType::False => Ok(Boolean::constant(false)),
                            OperandType::AllocatedTrue => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?))
                            }
                            OperandType::AllocatedFalse => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?))
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?).not())
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?).not())
                            }
                        }
                    };

                    a = dyn_construct(self.first_operand, "a")?;
                    b = dyn_construct(self.second_operand, "b")?;
                }

                let c = Boolean::and(cs, &a, &b)?;

                match (self.first_operand, self.second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::False,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::False,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Constant(false),
                    ) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Constant(false)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::False,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::False,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }

                    _ => {
                        panic!(
                            "unexpected behavior at {:?} AND {:?}",
                            self.first_operand, self.second_operand
                        );
                    }
                }

                Ok(())
            }
        }

        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                assert_eq!(
                    is_satisfied::<_, _, Basic>(
                        &TestCircuit::new(first_operand, second_operand),
                        &[]
                    ),
                    Ok(true)
                );
            }
        }
    }

    #[test]
    fn test_boolean_sha256_ch() {
        struct TestCircuit {
            first_operand: OperandType,
            second_operand: OperandType,
            third_operand: OperandType,
        };

        impl TestCircuit {
            fn new(
                first_operand: OperandType,
                second_operand: OperandType,
                third_operand: OperandType,
            ) -> Self {
                TestCircuit {
                    first_operand,
                    second_operand,
                    third_operand,
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a;
                let b;
                let c;

                // ch = (a and b) xor ((not a) and c)
                let expected = (self.first_operand.val() & self.second_operand.val())
                    ^ ((!self.first_operand.val()) & self.third_operand.val());

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Ok(Boolean::constant(true)),
                            OperandType::False => Ok(Boolean::constant(false)),
                            OperandType::AllocatedTrue => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?))
                            }
                            OperandType::AllocatedFalse => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?))
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?).not())
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?).not())
                            }
                        }
                    };

                    a = dyn_construct(self.first_operand, "a")?;
                    b = dyn_construct(self.second_operand, "b")?;
                    c = dyn_construct(self.third_operand, "c")?;
                }

                let ch = Boolean::sha256_ch(cs, &a, &b, &c).unwrap();

                assert_eq!(ch.get_value().unwrap(), expected);

                Ok(())
            }
        }

        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    assert_eq!(
                        is_satisfied::<_, _, Basic>(
                            &TestCircuit::new(first_operand, second_operand, third_operand),
                            &[]
                        ),
                        Ok(true)
                    );
                }
            }
        }
    }

    #[test]
    fn test_boolean_sha256_maj() {
        struct TestCircuit {
            first_operand: OperandType,
            second_operand: OperandType,
            third_operand: OperandType,
        };

        impl TestCircuit {
            fn new(
                first_operand: OperandType,
                second_operand: OperandType,
                third_operand: OperandType,
            ) -> Self {
                TestCircuit {
                    first_operand,
                    second_operand,
                    third_operand,
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a;
                let b;
                let c;

                // maj = (a and b) xor (a and c) xor (b and c)
                let expected = (self.first_operand.val() & self.second_operand.val())
                    ^ (self.first_operand.val() & self.third_operand.val())
                    ^ (self.second_operand.val() & self.third_operand.val());

                {
                    let mut dyn_construct = |operand| match operand {
                        OperandType::True => Ok(Boolean::constant(true)),
                        OperandType::False => Ok(Boolean::constant(false)),
                        OperandType::AllocatedTrue => {
                            Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?))
                        }
                        OperandType::AllocatedFalse => {
                            Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?))
                        }
                        OperandType::NegatedAllocatedTrue => {
                            Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(true))?).not())
                        }
                        OperandType::NegatedAllocatedFalse => {
                            Ok(Boolean::from(AllocatedBit::alloc(cs, || Ok(false))?).not())
                        }
                    };

                    a = dyn_construct(self.first_operand)?;
                    b = dyn_construct(self.second_operand)?;
                    c = dyn_construct(self.third_operand)?;
                }

                let maj = Boolean::sha256_maj(cs, &a, &b, &c)?;

                assert_eq!(maj.get_value().unwrap(), expected);

                Ok(())
            }
        }

        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    assert_eq!(
                        is_satisfied::<_, _, Basic>(
                            &TestCircuit::new(first_operand, second_operand, third_operand),
                            &[]
                        ),
                        Ok(true)
                    );
                }
            }
        }
    }
}
