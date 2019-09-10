use crate::{fields::Field, Coeff, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use std::ops::{Add, AddAssign, Neg, Sub};

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
    cs: &mut CS,
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
    pub fn alloc<CS, FF>(cs: &mut CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let var = cs.alloc(|| "num", || value)?;

        Ok(AllocatedNum {
            value: value.ok(),
            var,
        })
    }

    pub fn alloc_input<CS, FF>(cs: &mut CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let var = cs.alloc_input(|| "input variable", || value)?;

        Ok(AllocatedNum {
            value: value.ok(),
            var,
        })
    }

    pub fn inputize<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let var = cs.alloc_input(
            || "input variable",
            || self.value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce_zero(LinearCombination::from(self.var) - var);

        Ok(AllocatedNum {
            value: self.value,
            var,
        })
    }

    pub fn mul<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
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

    pub fn alloc_and_square<FF, CS>(cs: &mut CS, value: FF) -> Result<(Self, Self), SynthesisError>
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

    pub fn rescue_alpha<CS>(cs: &mut CS, base: &Combination<F>) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let base_value = base.get_value();
        let result_value = base_value.and_then(|num| Some(num.pow(&[F::RESCUE_ALPHA, 0, 0, 0])));

        // base^5 --> Constrain base^5 = result
        assert_eq!(F::RESCUE_ALPHA, 5);
        let (base_var, result_var) = constrain_pow_five(cs, base_value)?;

        let base_lc = base.lc(cs);
        cs.enforce_zero(base_lc - base_var);

        Ok(AllocatedNum {
            value: result_value,
            var: result_var,
        })
    }

    pub fn rescue_invalpha<CS>(cs: &mut CS, base: &Combination<F>) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let base_value = base.get_value();
        let result_value = base_value.and_then(|num| Some(num.pow(&F::RESCUE_INVALPHA)));

        // base^(1/5) --> Constrain result^5 = base
        assert_eq!(F::RESCUE_ALPHA, 5);
        let (result_var, base_var) = constrain_pow_five(cs, result_value)?;

        let base_lc = base.lc(cs);
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

    pub fn invert<CS>(&self, cs: &mut CS) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut newval = None;
        let newnum = AllocatedNum::alloc(cs, || {
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

    pub fn lc<CS: ConstraintSystem<F>>(&self, _cs: &mut CS) -> LinearCombination<F> {
        LinearCombination::zero()
            + match self {
                Num::Constant(v) => (*v, CS::ONE),
                Num::Allocated(coeff, num) => (*coeff, num.var),
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
    pub fn get_value(&self) -> Option<F> {
        self.value
    }

    pub fn lc<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> LinearCombination<F> {
        let mut acc = LinearCombination::zero();

        for term in &self.terms {
            acc = acc + &term.lc(cs);
        }

        acc
    }

    pub fn evaluate<CS>(&self, cs: &mut CS) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());

        if any_allocated {
            let out =
                AllocatedNum::alloc(cs, || self.value.ok_or(SynthesisError::AssignmentMissing))?;
            let lc = self.lc(cs);
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
        cs: &mut CS,
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

        let lc = self.lc(cs);
        cs.enforce_zero(lc - l);
        let lc = other.lc(cs);
        cs.enforce_zero(lc - r);

        Ok(AllocatedNum { value, var: o })
    }

    pub fn square<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let mut value = None;
        let (l, r, o) = cs.multiply(|| {
            let l = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let c = l.square();
            value = Some(c);

            Ok((l, l, c))
        })?;

        let lc = self.lc(cs);
        cs.enforce_zero(lc.clone() - l);
        cs.enforce_zero(lc - r);

        Ok(AllocatedNum { value, var: o })
    }

    pub fn rescue_alpha<CS>(&self, cs: &mut CS) -> Result<Num<F>, SynthesisError>
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

    pub fn rescue_invalpha<CS>(&self, cs: &mut CS) -> Result<Num<F>, SynthesisError>
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

#[cfg(test)]
mod test {
    use super::AllocatedNum;
    use crate::{
        circuits::{is_satisfied, Circuit, ConstraintSystem, SynthesisError},
        fields::Fp,
        Basic,
    };

    #[test]
    fn test_allocated_num() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let _ = AllocatedNum::alloc(cs, || Ok(Fp::one()))?;

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn test_num_alloc_and_square() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let (n, n2) = AllocatedNum::alloc_and_square(cs, || Ok(Fp::from(3)))?;

                assert!(n.value.unwrap() == Fp::from(3));
                assert!(n2.value.unwrap() == Fp::from(9));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }

    #[test]
    fn test_num_multiplication() {
        #[derive(Default)]
        struct TestCircuit;

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let n = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fp::from(12)))?;
                let n2 = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fp::from(10)))?;
                let n3 = n.mul(cs, &n2)?;
                assert!(n3.value.unwrap() == Fp::from(120));

                Ok(())
            }
        }

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit::default(), &[]),
            Ok(true)
        );
    }
}
