use crate::{fields::Field, Coeff, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use std::ops::Add;

#[derive(Clone, Copy)]
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

    pub fn get_value(&self) -> Option<F> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.var
    }

    pub fn lc(&self) -> LinearCombination<F> {
        LinearCombination::from(self.var)
    }
}

#[derive(Clone, Copy)]
pub enum Num<F: Field> {
    Constant(Coeff<F>),
    Allocated(Coeff<F>, AllocatedNum<F>),
}

impl<F: Field> From<AllocatedNum<F>> for Num<F> {
    fn from(num: AllocatedNum<F>) -> Self {
        Num::Allocated(Coeff::One, num)
    }
}

impl<F: Field> Num<F> {
    pub fn constant(val: F) -> Self {
        Num::Constant(Coeff::from(val))
    }

    pub fn value(&self) -> Option<F> {
        match *self {
            Num::Constant(v) => Some(v.value()),
            Num::Allocated(coeff, var) => var.value.map(|v| (coeff * v).value()),
        }
    }
}

#[derive(Clone)]
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

impl<F: Field> Add<AllocatedNum<F>> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: AllocatedNum<F>) -> Combination<F> {
        let new_value = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a + b)));

        self.terms.push(other.into());

        Combination {
            value: new_value,
            terms: self.terms,
        }
    }
}

impl<F: Field> Combination<F> {
    pub fn lc<CS: ConstraintSystem<F>>(&self, _cs: &mut CS) -> LinearCombination<F> {
        let mut acc = LinearCombination::zero();

        for term in &self.terms {
            let tmp = match term {
                Num::Constant(v) => (Coeff::from(*v), CS::ONE),
                Num::Allocated(coeff, num) => (Coeff::from(*coeff), num.var),
            };

            acc = acc + tmp;
        }

        acc
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