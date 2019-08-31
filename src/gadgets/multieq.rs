use crate::{
    Coeff, ConstraintSystem, LinearCombination, SynthesisError, Variable,
    fields::Field,
};

pub struct MultiEq<F: Field, CS: ConstraintSystem<F>> {
    cs: CS,
    ops: usize,
    bits_used: usize,
    lhs: LinearCombination<F>,
    rhs: LinearCombination<F>,
}

impl<F: Field, CS: ConstraintSystem<F>> MultiEq<F, CS> {
    pub fn new(cs: CS) -> Self {
        MultiEq {
            cs,
            ops: 0,
            bits_used: 0,
            lhs: LinearCombination::zero(),
            rhs: LinearCombination::zero(),
        }
    }

    fn accumulate(&mut self) {
        let ops = self.ops;
        let lhs = self.lhs.clone();
        let rhs = self.rhs.clone();
        self.cs.enforce_zero(lhs - &rhs);
        self.lhs = LinearCombination::zero();
        self.rhs = LinearCombination::zero();
        self.bits_used = 0;
        self.ops += 1;
    }

    pub fn enforce_equal(
        &mut self,
        num_bits: usize,
        lhs: &LinearCombination<F>,
        rhs: &LinearCombination<F>,
    ) {
        // Check if we will exceed the capacity
        if (F::CAPACITY as usize) <= (self.bits_used + num_bits) {
            self.accumulate();
        }

        assert!((F::CAPACITY as usize) > (self.bits_used + num_bits));

        let two = F::one() + F::one();
        let coeff: Coeff<F> = two.pow(&[self.bits_used as u64, 0, 0, 0]).into();
        self.lhs = self.lhs.clone() + (coeff, lhs);
        self.rhs = self.rhs.clone() + (coeff, rhs);
        self.bits_used += num_bits;
    }
}

impl<F: Field, CS: ConstraintSystem<F>> Drop for MultiEq<F, CS> {
    fn drop(&mut self) {
        if self.bits_used > 0 {
            self.accumulate();
        }
    }
}

impl<FF: Field, CS: ConstraintSystem<FF>> ConstraintSystem<FF> for MultiEq<FF, CS> {
    const ONE: Variable = CS::ONE;

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.cs.alloc(annotation, f)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.cs.alloc_input(annotation, f)
    }

    fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
        self.cs.enforce_zero(lc)
    }

    fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>
    {
        self.cs.multiply(values)
    }
}
