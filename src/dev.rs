//! Tools for developing circuits.

use crate::{
    circuits::{Circuit, Coeff, ConstraintSystem, LinearCombination, SynthesisError, Variable},
    fields::Field,
    synthesis::{Backend, SynthesisDriver},
};

impl Variable {
    fn get_index(&self) -> usize {
        match *self {
            Variable::A(index) => index,
            Variable::B(index) => index,
            Variable::C(index) => index,
        }
    }
}

/// Checks if the circuit produces a satisfying assignment for the
/// constraint system, given the particular public inputs.
pub fn is_satisfied<F: Field, C: Circuit<F>, S: SynthesisDriver>(
    circuit: &C,
    inputs: &[F],
) -> Result<bool, SynthesisError> {
    struct Assignment<F: Field> {
        n: usize,
        q: usize,
        a: Vec<F>,
        b: Vec<F>,
        c: Vec<F>,
        lc: Vec<(LinearCombination<F>, F)>,
        inputs: Vec<usize>,
    }

    impl<'a, F: Field> Backend<F> for &'a mut Assignment<F> {
        type LinearConstraintIndex = usize;

        /// Get the value of a variable. Can return None if we don't know.
        fn get_var(&self, var: Variable) -> Option<F> {
            Some(match var {
                Variable::A(index) => self.a[index - 1],
                Variable::B(index) => self.b[index - 1],
                Variable::C(index) => self.c[index - 1],
            })
        }

        /// Set the value of a variable. Might error if this backend expects to know it.
        fn set_var<FF, A, AR>(
            &mut self,
            _annotation: Option<A>,
            var: Variable,
            value: FF,
        ) -> Result<(), SynthesisError>
        where
            FF: FnOnce() -> Result<F, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            let value = value()?;

            match var {
                Variable::A(index) => {
                    self.a[index - 1] = value;
                }
                Variable::B(index) => {
                    self.b[index - 1] = value;
                }
                Variable::C(index) => {
                    self.c[index - 1] = value;
                }
            }

            Ok(())
        }

        /// Create a new multiplication gate.
        fn new_multiplication_gate<A, AR>(&mut self, _annotation: Option<A>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.n += 1;
            self.a.push(F::zero());
            self.b.push(F::zero());
            self.c.push(F::zero());
        }

        /// Create a new linear constraint, returning a cached index.
        fn new_linear_constraint<A, AR>(&mut self, _annotation: A) -> Self::LinearConstraintIndex
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.q += 1;
            self.lc.push((LinearCombination::zero(), F::zero()));
            self.lc.len()
        }

        /// Insert a term into a linear constraint.
        fn insert_coefficient(
            &mut self,
            var: Variable,
            coeff: Coeff<F>,
            y: &Self::LinearConstraintIndex,
        ) {
            use std::mem;

            let index = *y - 1;
            let mut lc = LinearCombination::zero();
            mem::swap(&mut lc, &mut self.lc[index].0);
            lc = lc + (coeff, var);
            mem::swap(&mut lc, &mut self.lc[index].0);
        }

        /// Compute a `LinearConstraintIndex` from `q`.
        fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
            q
        }

        /// Mark y^{_index} as the power of y cooresponding to the public input
        /// coefficient for the next public input, in the k(Y) polynomial.
        fn new_k_power(&mut self, index: usize, _: Option<F>) -> Result<(), SynthesisError> {
            self.inputs.push(index);

            Ok(())
        }
    }

    let mut assignment = Assignment::<F> {
        n: 0,
        q: 0,
        a: vec![],
        b: vec![],
        c: vec![],
        lc: vec![],
        inputs: vec![],
    };

    S::synthesize(&mut assignment, circuit)?;

    // Check consistency of sizes
    assert_eq!(assignment.n, assignment.a.len());
    assert_eq!(assignment.n, assignment.b.len());
    assert_eq!(assignment.n, assignment.c.len());
    assert_eq!(assignment.q, assignment.lc.len());

    if (inputs.len() + 1) != assignment.inputs.len() {
        return Ok(false);
    }

    {
        let idx = assignment.inputs[0];
        assignment.lc[idx - 1].1 = F::one();
    }

    for (input, idx) in inputs.iter().zip(assignment.inputs.iter().skip(1)) {
        assignment.lc[*idx - 1].1 = *input;
    }

    // Check all multiplication gates are satisfied
    for ((a, b), c) in assignment
        .a
        .iter()
        .zip(assignment.b.iter())
        .zip(assignment.c.iter())
    {
        if (*a) * (*b) != (*c) {
            return Ok(false);
        }
    }

    // Check all linear constraints are satisfied
    for lc in assignment.lc.iter() {
        let lhs = lc.0.evaluate(&assignment.a, &assignment.b, &assignment.c);
        if lhs != lc.1 {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Checks if the circuit produces a satisfying assignment for the
/// constraint system, given the particular public inputs.
pub fn determinism_check<F: Field, C: Circuit<F>>(circuit: &C) -> Result<(), SynthesisError> {
    enum Event<F: Field> {
        Alloc,
        InputAlloc,
        Multiplication,
        EnforceZero(LinearCombination<F>),
    }

    struct Record<F: Field> {
        vars: usize,
        events: Vec<Event<F>>,
    }

    impl<FF: Field> ConstraintSystem<FF> for Record<FF> {
        type Root = Self;

        const ONE: Variable = Variable::A(0);

        fn alloc<F, A, AR>(&mut self, _annotation: A, _value: F) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<FF, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.events.push(Event::Alloc);

            let var = Variable::A(self.vars);
            self.vars += 1;
            Ok(var)
        }

        fn alloc_input<F, A, AR>(
            &mut self,
            _annotation: A,
            _value: F,
        ) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<FF, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.events.push(Event::InputAlloc);

            let var = Variable::A(self.vars);
            self.vars += 1;
            Ok(var)
        }

        fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
            self.events.push(Event::EnforceZero(lc));
        }

        fn multiply<F, A, AR>(
            &mut self,
            _annotation: A,
            _values: F,
        ) -> Result<(Variable, Variable, Variable), SynthesisError>
        where
            F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.events.push(Event::Multiplication);

            let a = Variable::A(self.vars);
            self.vars += 1;
            let b = Variable::A(self.vars);
            self.vars += 1;
            let c = Variable::A(self.vars);
            self.vars += 1;

            Ok((a, b, c))
        }

        fn push_namespace<NR, N>(&mut self, _: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            // Do nothing; we don't care about namespaces in this context.
        }

        fn pop_namespace(&mut self) {
            // Do nothing; we don't care about namespaces in this context.
        }

        fn get_root(&mut self) -> &mut Self::Root {
            self
        }
    }

    let mut record = Record {
        events: vec![],
        vars: 1,
    };

    circuit.synthesize(&mut record)?;

    struct Enforce<F: Field, I: Iterator<Item = Event<F>>> {
        vars: usize,
        events: I,
    }

    impl<FF: Field, I: Iterator<Item = Event<FF>>> ConstraintSystem<FF> for Enforce<FF, I> {
        type Root = Self;

        const ONE: Variable = Variable::A(0);

        fn alloc<F, A, AR>(&mut self, _annotation: A, value: F) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<FF, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            value()?;
            match self.events.next().unwrap() {
                Event::Alloc => {}
                _ => panic!("wrong"),
            }

            let var = Variable::A(self.vars);
            self.vars += 1;
            Ok(var)
        }

        fn alloc_input<F, A, AR>(
            &mut self,
            _annotation: A,
            value: F,
        ) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<FF, SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            value()?;
            match self.events.next().unwrap() {
                Event::InputAlloc => {}
                _ => panic!("wrong"),
            }

            let var = Variable::A(self.vars);
            self.vars += 1;
            Ok(var)
        }

        fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
            let other_lc = self.events.next().unwrap();
            match other_lc {
                Event::EnforceZero(other_lc) => {
                    let a = other_lc.as_ref();
                    let b = lc.as_ref();
                    assert_eq!(a.len(), b.len());

                    for (a, b) in a.iter().zip(b.iter()) {
                        assert!(a.0.get_index() == b.0.get_index());
                        assert!(a.1 == b.1);
                    }
                }
                _ => panic!("wrong"),
            }
        }

        fn multiply<F, A, AR>(
            &mut self,
            _annotation: A,
            values: F,
        ) -> Result<(Variable, Variable, Variable), SynthesisError>
        where
            F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            values()?;

            match self.events.next().unwrap() {
                Event::Multiplication => {}
                _ => panic!("wrong"),
            }

            let a = Variable::A(self.vars);
            self.vars += 1;
            let b = Variable::A(self.vars);
            self.vars += 1;
            let c = Variable::A(self.vars);
            self.vars += 1;

            Ok((a, b, c))
        }

        fn push_namespace<NR, N>(&mut self, _: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            // Do nothing; we don't care about namespaces in this context.
        }

        fn pop_namespace(&mut self) {
            // Do nothing; we don't care about namespaces in this context.
        }

        fn get_root(&mut self) -> &mut Self::Root {
            self
        }
    }

    let mut enforce = Enforce {
        events: record.events.into_iter(),
        vars: 1,
    };

    circuit.synthesize(&mut enforce)?;

    Ok(())
}
