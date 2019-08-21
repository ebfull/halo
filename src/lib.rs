mod curves;
mod fields;
mod synthesis;
mod util;

pub use curves::{Curve, Ec1};
pub use fields::{Field, Fp};
pub use synthesis::{Backend, Basic, SynthesisDriver};

use std::ops::{Add, Neg, Sub};

#[derive(Copy, Clone, Debug)]
pub enum Variable {
    A(usize),
    B(usize),
    C(usize),
}

#[derive(Copy, Clone, Debug)]
pub enum SynthesisError {
    AssignmentMissing,
    Violation,
}

pub trait Circuit<F: Field> {
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

pub trait ConstraintSystem<FF: Field> {
    const ONE: Variable;

    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>;

    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>;

    fn enforce_zero(&mut self, lc: LinearCombination<FF>);

    fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>;
}

impl Variable {
    fn get_index(&self) -> usize {
        match *self {
            Variable::A(index) => index,
            Variable::B(index) => index,
            Variable::C(index) => index,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Coeff<F: Field> {
    Zero,
    One,
    NegativeOne,
    Full(F),
}

impl<F: Field> Coeff<F> {
    pub fn multiply(&self, with: &mut F) {
        match self {
            Coeff::Zero => {
                *with = F::zero();
            }
            Coeff::One => {}
            Coeff::NegativeOne => {
                *with = -*with;
            }
            Coeff::Full(val) => {
                *with = *with * (*val);
            }
        }
    }
}

impl<F: Field> Neg for Coeff<F> {
    type Output = Coeff<F>;

    fn neg(self) -> Self {
        match self {
            Coeff::Zero => Coeff::Zero,
            Coeff::One => Coeff::NegativeOne,
            Coeff::NegativeOne => Coeff::One,
            Coeff::Full(mut a) => {
                a = -a;
                Coeff::Full(a)
            }
        }
    }
}

#[derive(Clone)]
pub struct LinearCombination<F: Field>(Vec<(Variable, Coeff<F>)>);

impl<F: Field> From<Variable> for LinearCombination<F> {
    fn from(var: Variable) -> LinearCombination<F> {
        LinearCombination::<F>::zero() + var
    }
}

impl<F: Field> AsRef<[(Variable, Coeff<F>)]> for LinearCombination<F> {
    fn as_ref(&self) -> &[(Variable, Coeff<F>)] {
        &self.0
    }
}

impl<F: Field> LinearCombination<F> {
    pub fn zero() -> LinearCombination<F> {
        LinearCombination(vec![])
    }
}

impl<F: Field> Add<(Coeff<F>, Variable)> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn add(mut self, (coeff, var): (Coeff<F>, Variable)) -> LinearCombination<F> {
        self.0.push((var, coeff));

        self
    }
}

impl<F: Field> Sub<(Coeff<F>, Variable)> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn sub(self, (coeff, var): (Coeff<F>, Variable)) -> LinearCombination<F> {
        self + (-coeff, var)
    }
}

impl<F: Field> Add<Variable> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: Variable) -> LinearCombination<F> {
        self + (Coeff::One, other)
    }
}

impl<F: Field> Sub<Variable> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: Variable) -> LinearCombination<F> {
        self - (Coeff::One, other)
    }
}

impl<'a, F: Field> Add<&'a LinearCombination<F>> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn add(mut self, other: &'a LinearCombination<F>) -> LinearCombination<F> {
        for s in &other.0 {
            self = self + (s.1, s.0);
        }

        self
    }
}

impl<'a, F: Field> Sub<&'a LinearCombination<F>> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn sub(mut self, other: &'a LinearCombination<F>) -> LinearCombination<F> {
        for s in &other.0 {
            self = self - (s.1, s.0);
        }

        self
    }
}
