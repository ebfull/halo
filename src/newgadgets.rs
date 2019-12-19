use crate::fields::*;
use crate::newcircuits::*;
use crate::*;
use std::ops::{Add, AddAssign, Neg, Sub};

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
        let (a, _, _) = cs.multiply(|| {
            let v = value()?;
            final_value = Some(v);

            Ok((v.into(), v.into(), v.into()))
        })?;

        Ok(AllocatedBit {
            value: final_value,
            var: a,
        })
    }

    pub fn check<F: Field, CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let index = if let Variable::A(index) = self.var {
            index
        } else {
            panic!("should not happen");
        };
        let a = Variable::A(index);
        let b = Variable::B(index);
        let c = Variable::C(index);

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
        let (a, b, c) = cs.multiply(|| {
            let v = value()?;
            final_value = Some(v);
            let fe: F = v.into();

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
    pub fn xor<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| {
            let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

            if a_val ^ b_val {
                result_value = Some(true);

                Ok(F::one())
            } else {
                result_value = Some(false);

                Ok(F::zero())
            }
        })?;

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

            let a_val: F = a_val.into();
            let b_val: F = b_val.into();
            let c_val: F = c_val.into();

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
    pub fn and<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
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

                Ok((a_val.into(), b_val.into(), F::zero()))
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
    pub fn and_not<F, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
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

            Ok((a_val.into(), (!b_val).into(), result_value.unwrap().into()))
        })?;
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
        let (not_a_var, not_b_var, result_var) = cs.multiply(|| {
            let a_val = a.value.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b.value.ok_or(SynthesisError::AssignmentMissing)?;

            result_value = Some(!a_val & !b_val);

            Ok((
                (!a_val).into(),
                (!b_val).into(),
                result_value.unwrap().into(),
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

        let ch = cs.alloc(|| {
            ch_value
                .ok_or(SynthesisError::AssignmentMissing)
                .map(F::from)
        })?;

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

            let a_val: F = a_val.into();
            let b_val: F = b_val.into();
            let c_val: F = c_val.into();
            let ch_val: F = ch_val.into();

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

        let maj = cs.alloc(|| {
            maj_value
                .ok_or(SynthesisError::AssignmentMissing)
                .map(F::from)
        })?;

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

        let (d_var, e_var, f_var) = cs.multiply(|| {
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

/// Constrain (x)^5 = (x^5), and return variables for x and (x^5).
///
/// We can do so with three multiplication constraints and five linear constraints:
///
/// a * b = c
/// a := x
/// b = a
/// c := x^2
///
/// d * e = f
/// d = c
/// e = c
/// f := x^4
///
/// g * h = i
/// g = f
/// h = x
/// i := x^5
fn constrain_pow_five<F, CS>(
    mut cs: CS,
    x: Option<F>,
) -> Result<(Variable, Variable), SynthesisError>
where
    F: Field,
    CS: ConstraintSystem<F>,
{
    let x2 = x.and_then(|x| Some(x.square()));
    let x4 = x2.and_then(|x2| Some(x2.square()));
    let x5 = x4.and_then(|x4| x.and_then(|x| Some(x4 * x)));

    let (base_var, b_var, c_var) = cs.multiply(|| {
        let x = x.ok_or(SynthesisError::AssignmentMissing)?;
        let x2 = x2.ok_or(SynthesisError::AssignmentMissing)?;

        Ok((x, x, x2))
    })?;
    cs.enforce_zero(LinearCombination::from(base_var) - b_var);

    let (d_var, e_var, f_var) = cs.multiply(|| {
        let x2 = x2.ok_or(SynthesisError::AssignmentMissing)?;
        let x4 = x4.ok_or(SynthesisError::AssignmentMissing)?;

        Ok((x2, x2, x4))
    })?;
    cs.enforce_zero(LinearCombination::from(c_var) - d_var);
    cs.enforce_zero(LinearCombination::from(c_var) - e_var);

    let (g_var, h_var, result_var) = cs.multiply(|| {
        let x = x.ok_or(SynthesisError::AssignmentMissing)?;
        let x4 = x4.ok_or(SynthesisError::AssignmentMissing)?;
        let x5 = x5.ok_or(SynthesisError::AssignmentMissing)?;

        Ok((x4, x, x5))
    })?;
    cs.enforce_zero(LinearCombination::from(f_var) - g_var);
    cs.enforce_zero(LinearCombination::from(base_var) - h_var);

    Ok((base_var, result_var))
}

#[derive(Clone, Copy, Debug)]
pub struct AllocatedNum<F: Field> {
    value: Option<F>,
    var: Variable,
}

impl<F: Field> AllocatedNum<F> {
    pub fn one<CS>(cs: CS) -> AllocatedNum<F>
    where
        CS: ConstraintSystem<F>,
    {
        AllocatedNum {
            value: Some(F::one()),
            var: CS::ONE,
        }
    }

    pub fn alloc<CS, FF>(mut cs: CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut final_value = None;

        let var = cs.alloc(|| {
            let value = value()?;
            final_value = Some(value);
            Ok(value)
        })?;

        Ok(AllocatedNum {
            value: final_value,
            var,
        })
    }

    pub fn alloc_input<CS, FF>(mut cs: CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut final_value = None;

        let var = cs.alloc_input(|| {
            let value = value()?;
            final_value = Some(value);
            Ok(value)
        })?;

        Ok(AllocatedNum {
            value: final_value,
            var,
        })
    }

    pub fn inputize<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let var = cs.alloc_input(|| self.value.ok_or(SynthesisError::AssignmentMissing))?;

        cs.enforce_zero(LinearCombination::from(self.var) - var);

        Ok(AllocatedNum {
            value: self.value,
            var,
        })
    }

    pub fn mul<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let product = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a * b)));

        let (l, r, o) = cs.multiply(|| {
            let l = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let r = other.value.ok_or(SynthesisError::AssignmentMissing)?;
            let o = product.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((l, r, o))
        })?;

        cs.enforce_zero(LinearCombination::from(self.var) - l);
        cs.enforce_zero(LinearCombination::from(other.var) - r);

        Ok(AllocatedNum {
            value: product,
            var: o,
        })
    }

    pub fn from_raw_unchecked(value: Option<F>, var: Variable) -> Self {
        AllocatedNum { value, var }
    }

    pub fn alloc_and_square<FF, CS>(mut cs: CS, value: FF) -> Result<(Self, Self), SynthesisError>
    where
        CS: ConstraintSystem<F>,
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let mut value_sq = None;
        let (a, b, c) = cs.multiply(|| {
            let value = value?;
            value_sq = Some(value.square());

            Ok((value, value, value_sq.unwrap()))
        })?;
        cs.enforce_zero(LinearCombination::from(a) - b);

        Ok((
            AllocatedNum {
                value: value.ok(),
                var: a,
            },
            AllocatedNum {
                value: value_sq,
                var: c,
            },
        ))
    }

    pub fn rescue_alpha<CS>(mut cs: CS, base: &Combination<F>) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let base_value = base.get_value();
        let result_value = base_value.and_then(|num| Some(num.pow(&[F::RESCUE_ALPHA, 0, 0, 0])));

        // base^5 --> Constrain base^5 = result
        assert_eq!(F::RESCUE_ALPHA, 5);
        let (base_var, result_var) = constrain_pow_five(&mut cs, base_value)?;

        let base_lc = base.lc(&mut cs);
        cs.enforce_zero(base_lc - base_var);

        Ok(AllocatedNum {
            value: result_value,
            var: result_var,
        })
    }

    pub fn rescue_invalpha<CS>(mut cs: CS, base: &Combination<F>) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let base_value = base.get_value();
        let result_value = base_value.and_then(|num| Some(num.pow(&F::RESCUE_INVALPHA)));

        // base^(1/5) --> Constrain result^5 = base
        assert_eq!(F::RESCUE_ALPHA, 5);
        let (result_var, base_var) = constrain_pow_five(&mut cs, result_value)?;

        let base_lc = base.lc(&mut cs);
        cs.enforce_zero(base_lc - base_var);

        Ok(AllocatedNum {
            value: result_value,
            var: result_var,
        })
    }

    pub fn get_value(&self) -> Option<F> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.var
    }

    pub fn lc(&self) -> LinearCombination<F> {
        LinearCombination::from(self.var)
    }

    pub fn invert<CS>(&self, mut cs: CS) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut newval = None;
        let newnum = AllocatedNum::alloc(&mut cs, || {
            let inv = self
                .value
                .ok_or(SynthesisError::AssignmentMissing)?
                .invert();
            if bool::from(inv.is_some()) {
                let tmp = inv.unwrap();
                newval = Some(tmp);
                Ok(tmp)
            } else {
                Err(SynthesisError::Unsatisfiable)
            }
        })?;

        let (a, b, c) = cs.multiply(|| {
            Ok((
                newval.ok_or(SynthesisError::AssignmentMissing)?,
                self.value.ok_or(SynthesisError::AssignmentMissing)?,
                F::one(),
            ))
        })?;

        cs.enforce_zero(LinearCombination::from(a) - newnum.get_variable());
        cs.enforce_zero(LinearCombination::from(b) - self.get_variable());
        cs.enforce_zero(LinearCombination::from(c) - CS::ONE);

        Ok(newnum)
    }

    pub fn sqrt<CS>(&self, mut cs: CS) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut newval = None;
        let newnum = AllocatedNum::alloc(&mut cs, || {
            let sqrt = self.value.ok_or(SynthesisError::AssignmentMissing)?.sqrt();
            if bool::from(sqrt.is_some()) {
                let tmp = sqrt.unwrap();
                newval = Some(tmp);
                Ok(tmp)
            } else {
                Err(SynthesisError::Unsatisfiable)
            }
        })?;

        let (a, b, c) = cs.multiply(|| {
            Ok((
                newval.ok_or(SynthesisError::AssignmentMissing)?,
                newval.ok_or(SynthesisError::AssignmentMissing)?,
                self.value.ok_or(SynthesisError::AssignmentMissing)?,
            ))
        })?;

        cs.enforce_zero(LinearCombination::from(a) - newnum.get_variable());
        cs.enforce_zero(LinearCombination::from(b) - newnum.get_variable());
        cs.enforce_zero(LinearCombination::from(c) - self.get_variable());

        Ok(newnum)
    }
}

impl<F: Field> From<AllocatedBit> for AllocatedNum<F> {
    fn from(bit: AllocatedBit) -> AllocatedNum<F> {
        AllocatedNum {
            var: bit.get_variable(),
            value: bit
                .get_value()
                .map(|v| if v { F::one() } else { F::zero() }),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Num<F: Field> {
    Constant(Coeff<F>),
    Allocated(Coeff<F>, AllocatedNum<F>),
}

impl<F: Field> Neg for Num<F> {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Num::Constant(coeff) => Num::Constant(-coeff),
            Num::Allocated(coeff, var) => Num::Allocated(-coeff, var),
        }
    }
}

impl<F: Field> From<AllocatedNum<F>> for Num<F> {
    fn from(num: AllocatedNum<F>) -> Self {
        Num::Allocated(Coeff::One, num)
    }
}

impl<F: Field> From<(Coeff<F>, AllocatedNum<F>)> for Num<F> {
    fn from(num: (Coeff<F>, AllocatedNum<F>)) -> Self {
        Num::Allocated(num.0, num.1)
    }
}

impl<F: Field> From<(Coeff<F>, Num<F>)> for Num<F> {
    fn from(num: (Coeff<F>, Num<F>)) -> Self {
        match num.1 {
            Num::Constant(coeff) => Num::Constant(num.0 * coeff),
            Num::Allocated(coeff, n) => Num::Allocated(num.0 * coeff, n),
        }
    }
}

impl<F: Field> Num<F> {
    pub fn scale(self, val: F) -> Self {
        match self {
            Num::Constant(coeff) => Num::Constant(coeff * val),
            Num::Allocated(coeff, var) => Num::Allocated(coeff * val, var),
        }
    }

    pub fn constant(val: F) -> Self {
        Num::Constant(Coeff::from(val))
    }

    pub fn is_constant(&self) -> bool {
        match *self {
            Num::Constant(_) => true,
            _ => false,
        }
    }

    pub fn value(&self) -> Option<F> {
        match *self {
            Num::Constant(v) => Some(v.value()),
            Num::Allocated(coeff, var) => var.value.map(|v| (coeff * v).value()),
        }
    }

    pub fn lc<CS: ConstraintSystem<F>>(&self, mut _cs: CS) -> LinearCombination<F> {
        LinearCombination::zero()
            + match self {
                Num::Constant(v) => (*v, CS::ONE),
                Num::Allocated(coeff, num) => (*coeff, num.var),
            }
    }

    pub fn alloc<CS, FF>(cs: CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        Ok(AllocatedNum::alloc(cs, value)?.into())
    }

    pub fn mul<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        match (*self, *other) {
            (Num::Constant(val), Num::Allocated(coeff, var))
            | (Num::Allocated(coeff, var), Num::Constant(val)) => {
                Ok(Num::Allocated(coeff * val, var))
            }
            (Num::Allocated(c1, v1), Num::Allocated(c2, v2)) => {
                let mut outvalue = None;
                let (a, b, c) = cs.multiply(|| {
                    let left = c1.value() * v1.get_value().unwrap();
                    let right = c2.value() * v2.get_value().unwrap();
                    let out = left * right;
                    outvalue = Some(out);

                    Ok((left, right, out))
                })?;

                cs.enforce_zero(LinearCombination::zero() + (c1, v1.get_variable()) - a);
                cs.enforce_zero(LinearCombination::zero() + (c2, v2.get_variable()) - b);

                Ok(AllocatedNum {
                    value: outvalue,
                    var: c,
                }
                .into())
            }
            _ => unimplemented!(),
        }
    }

    pub fn sqrt<CS>(&self, mut cs: CS) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        match self {
            Num::Constant(v) => Ok(Num::Constant(Coeff::Full(v.value().sqrt().unwrap()))), // TODO
            Num::Allocated(_, _) => {
                let mut sqrt_value = None;

                let (sqrt_a, sqrt_b, square) = cs.multiply(|| {
                    let square = self.value().unwrap();
                    let sqrt = square.sqrt(); // TODO
                    if bool::from(sqrt.is_none()) {
                        panic!("nonsquare");
                    }
                    let sqrt = sqrt.unwrap();

                    sqrt_value = Some(sqrt);

                    Ok((sqrt, sqrt, square))
                })?;

                cs.enforce_zero(LinearCombination::from(sqrt_a) - sqrt_b);
                let lc = self.lc(&mut cs);
                cs.enforce_zero(lc - square);

                Ok(AllocatedNum::from_raw_unchecked(sqrt_value, sqrt_a).into())
            }
        }
    }

    pub fn invert<CS>(&self, mut cs: CS) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        match self {
            Num::Constant(v) => Ok(Num::Constant(Coeff::Full(v.value().sqrt().unwrap()))), // TODO
            Num::Allocated(_, _) => {
                let mut inv_value = None;

                let (inv_a, inv_b, one) = cs.multiply(|| {
                    let value = self.value().unwrap();
                    let inv = value.invert().unwrap(); // TODO

                    inv_value = Some(inv);

                    Ok((inv, value, F::one()))
                })?;

                cs.enforce_zero(LinearCombination::from(CS::ONE) - one);
                let lc = self.lc(&mut cs);
                cs.enforce_zero(lc - inv_b);

                Ok(AllocatedNum::from_raw_unchecked(inv_value, inv_a).into())
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Combination<F: Field> {
    value: Option<F>,
    terms: Vec<Num<F>>,
}

impl<F: Field> From<AllocatedNum<F>> for Combination<F> {
    fn from(num: AllocatedNum<F>) -> Self {
        Combination {
            value: num.value,
            terms: vec![num.into()],
        }
    }
}

impl<F: Field> From<Num<F>> for Combination<F> {
    fn from(num: Num<F>) -> Self {
        Combination {
            value: num.value(),
            terms: vec![num],
        }
    }
}

impl<F: Field> Add<Combination<F>> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: Combination<F>) -> Combination<F> {
        let new_value = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a + b)));

        self.terms.extend(other.terms);

        Combination {
            value: new_value,
            terms: self.terms,
        }
    }
}

impl<F: Field> Add<AllocatedNum<F>> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: AllocatedNum<F>) -> Combination<F> {
        self += other;
        self
    }
}

impl<'a, F: Field> AddAssign<AllocatedNum<F>> for Combination<F> {
    fn add_assign(&mut self, other: AllocatedNum<F>) {
        self.value = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a + b)));

        self.terms.push(other.into());
    }
}

impl<F: Field> Sub<AllocatedNum<F>> for Combination<F> {
    type Output = Combination<F>;

    fn sub(mut self, other: AllocatedNum<F>) -> Combination<F> {
        let new_value = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a - b)));

        self.terms.push(-Num::from(other));

        Combination {
            value: new_value,
            terms: self.terms,
        }
    }
}

impl<F: Field> Add<Num<F>> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: Num<F>) -> Combination<F> {
        self += other;
        self
    }
}

impl<'a, F: Field> AddAssign<Num<F>> for Combination<F> {
    fn add_assign(&mut self, other: Num<F>) {
        self.value = self
            .value
            .and_then(|a| other.value().and_then(|b| Some(a + b)));

        self.terms.push(other);
    }
}

impl<F: Field> Add<(Coeff<F>, AllocatedNum<F>)> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: (Coeff<F>, AllocatedNum<F>)) -> Combination<F> {
        let new_value = self
            .value
            .and_then(|a| other.1.value.and_then(|b| Some(a + (other.0.value() * b))));

        self.terms.push(other.into());

        Combination {
            value: new_value,
            terms: self.terms,
        }
    }
}

impl<F: Field> Add<(Coeff<F>, Num<F>)> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: (Coeff<F>, Num<F>)) -> Combination<F> {
        let new_value = self.value.and_then(|a| {
            other
                .1
                .value()
                .and_then(|b| Some(a + (other.0.value() * b)))
        });

        self.terms.push(other.into());

        Combination {
            value: new_value,
            terms: self.terms,
        }
    }
}

impl<F: Field> Combination<F> {
    pub fn zero() -> Self {
        Combination {
            value: Some(F::zero()),
            terms: vec![],
        }
    }

    pub fn scale(self, by: F) -> Self {
        let value = self.value.map(|v| v * by);
        let terms = self.terms.into_iter().map(|t| t.scale(by)).collect();

        Combination { value, terms }
    }

    pub fn get_value(&self) -> Option<F> {
        self.value
    }

    pub fn lc<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> LinearCombination<F> {
        let mut acc = LinearCombination::zero();

        for term in &self.terms {
            acc = acc + &term.lc(&mut cs);
        }

        acc
    }

    pub fn conditional_multiply<CS>(
        self,
        cs: CS,
        condition: &AllocatedBit,
        coeff: F,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // result = (1 - condition) self + condition * coeff * self
        // result = self - condition * self + condition * coeff * self
        // result = self + (condition) * ((coeff - 1) self)
        let rhs = self.clone().scale(coeff - F::one());
        let product = rhs.mul(
            cs,
            &Combination::from(AllocatedNum::from(condition.clone())),
        )?;
        Ok(self + product)
    }

    pub fn evaluate<CS>(&self, mut cs: CS) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());

        if any_allocated {
            let out = AllocatedNum::alloc(&mut cs, || {
                self.value.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let lc = self.lc(&mut cs);
            cs.enforce_zero(out.lc() - &lc);
            Ok(out.into())
        } else {
            // We can just return a constant
            let base_value = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(Num::constant(base_value))
        }
    }

    pub fn mul<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Combination<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let mut value = None;
        let (l, r, o) = cs.multiply(|| {
            let l = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let r = other.value.ok_or(SynthesisError::AssignmentMissing)?;
            let o = l * &r;
            value = Some(o);

            Ok((l, r, o))
        })?;

        let lc = self.lc(&mut cs);
        cs.enforce_zero(lc - l);
        let lc = other.lc(&mut cs);
        cs.enforce_zero(lc - r);

        Ok(AllocatedNum { value, var: o })
    }

    pub fn div<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Combination<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let mut value = None;

        let (quotient, denominator, numerator) = cs.multiply(|| {
            let numerator = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let denominator = other.value.ok_or(SynthesisError::AssignmentMissing)?;
            let quotient = numerator * denominator.invert().unwrap(); // TODO
            value = Some(quotient);

            Ok((quotient, denominator, numerator))
        })?;

        let lc = self.lc(&mut cs);
        cs.enforce_zero(lc - numerator);
        let lc = other.lc(&mut cs);
        cs.enforce_zero(lc - denominator);

        Ok(AllocatedNum {
            value,
            var: quotient,
        })
    }

    pub fn square<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let mut value = None;
        let (l, r, o) = cs.multiply(|| {
            let l = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let c = l.square();
            value = Some(c);

            Ok((l, l, c))
        })?;

        let lc = self.lc(&mut cs);
        cs.enforce_zero(lc.clone() - l);
        cs.enforce_zero(lc - r);

        Ok(AllocatedNum { value, var: o })
    }

    pub fn rescue_alpha<CS>(&self, cs: CS) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());

        if any_allocated {
            AllocatedNum::rescue_alpha(cs, self).map(|n| n.into())
        } else {
            // We can just return a constant
            let base_value = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(Num::constant(base_value.pow(&[F::RESCUE_ALPHA, 0, 0, 0])))
        }
    }

    pub fn rescue_invalpha<CS>(&self, cs: CS) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());

        if any_allocated {
            AllocatedNum::rescue_invalpha(cs, self).map(|n| n.into())
        } else {
            // We can just return a constant
            let base_value = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(Num::constant(base_value.pow(&F::RESCUE_INVALPHA)))
        }
    }
}
