//! Tools for developing circuits.

use crate::{
    circuits::{
        Circuit, Coeff, ConstraintSystem, LinearCombination, RecursiveCircuit, SynthesisError,
        Variable,
    },
    curves::Curve,
    fields::Field,
    proofs::{Deferred, Leftovers, Params},
    recursion::{RecursiveProof, VerificationCircuit},
    synthesis::{Backend, SynthesisDriver},
};
use std::collections::BTreeMap;
use std::marker::PhantomData;

impl Variable {
    fn get_index(&self) -> usize {
        match *self {
            Variable::A(index) => index,
            Variable::B(index) => index,
            Variable::C(index) => index,
        }
    }
}

fn compute_path(ns: &[String], this: String) -> String {
    if this.chars().any(|a| a == '/') {
        panic!("'/' is not allowed in names");
    }

    let mut name = String::new();

    let mut needs_separation = false;
    for ns in ns.iter().chain(Some(&this).into_iter()) {
        if needs_separation {
            name += "/";
        }

        name += ns;
        needs_separation = true;
    }

    name
}

#[derive(Clone, Debug, PartialEq)]
pub enum SatisfactionError<F: Field> {
    Synthesis(SynthesisError),
    InputLength(usize, usize),
    Multiplication(String, F, F, F),
    Linear(String, F, F),
}

impl<F: Field> From<SynthesisError> for SatisfactionError<F> {
    fn from(e: SynthesisError) -> Self {
        SatisfactionError::Synthesis(e)
    }
}

/// Checks if the circuit produces a satisfying assignment for the
/// constraint system, given the particular public inputs.
pub fn is_satisfied<F: Field, C: Circuit<F>, S: SynthesisDriver>(
    circuit: &C,
    inputs: &[F],
) -> Result<bool, SatisfactionError<F>> {
    enum MultType {
        Allocation(String, String),
        Constraint(String),
    }

    struct Assignment<F: Field> {
        current_namespace: Vec<String>,
        n: usize,
        q: usize,
        a: Vec<F>,
        b: Vec<F>,
        c: Vec<F>,
        mults: Vec<MultType>,
        lc: Vec<(LinearCombination<F>, F, String)>,
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
            annotation: Option<A>,
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

                    if let Some(annotation) = annotation {
                        match self.mults[index - 1] {
                            MultType::Allocation(ref mut a, _) => {
                                *a = compute_path(&self.current_namespace, annotation().into());
                            }
                            _ => return Err(SynthesisError::Violation),
                        }
                    }
                }
                Variable::B(index) => {
                    self.b[index - 1] = value;

                    if let Some(annotation) = annotation {
                        match self.mults[index - 1] {
                            MultType::Allocation(_, ref mut b) => {
                                *b = compute_path(&self.current_namespace, annotation().into());
                            }
                            _ => return Err(SynthesisError::Violation),
                        }
                    }
                }
                Variable::C(index) => {
                    self.c[index - 1] = value;

                    if annotation.is_some() {
                        // C variable should never be used for an allocation
                        return Err(SynthesisError::Violation);
                    }
                }
            };

            Ok(())
        }

        /// Create a new multiplication gate.
        fn new_multiplication_gate<A, AR>(&mut self, annotation: Option<A>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.n += 1;
            self.a.push(F::zero());
            self.b.push(F::zero());
            self.c.push(F::zero());
            if let Some(annotation) = annotation {
                let path = compute_path(&self.current_namespace, annotation().into());
                self.mults.push(MultType::Constraint(path));
            } else {
                self.mults.push(MultType::Allocation(
                    "unused".to_owned(),
                    "unused".to_owned(),
                ));
            }
        }

        /// Create a new linear constraint, returning a cached index.
        fn new_linear_constraint<A, AR>(&mut self, annotation: A) -> Self::LinearConstraintIndex
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.q += 1;
            let path = compute_path(&self.current_namespace, annotation().into());
            self.lc.push((LinearCombination::zero(), F::zero(), path));
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

        fn push_namespace<NR, N>(&mut self, name_fn: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            let name = name_fn().into();
            self.current_namespace.push(name);
        }

        fn pop_namespace(&mut self, _gadget_name: Option<String>) {
            assert!(self.current_namespace.pop().is_some());
        }
    }

    let mut assignment = Assignment::<F> {
        current_namespace: vec![],
        n: 0,
        q: 0,
        a: vec![],
        b: vec![],
        c: vec![],
        mults: vec![],
        lc: vec![],
        inputs: vec![],
    };

    S::synthesize(&mut assignment, circuit)?;

    // Check consistency of sizes
    assert_eq!(assignment.n, assignment.a.len());
    assert_eq!(assignment.n, assignment.b.len());
    assert_eq!(assignment.n, assignment.c.len());
    assert_eq!(assignment.n, assignment.mults.len());
    assert_eq!(assignment.q, assignment.lc.len());

    if (inputs.len() + 1) != assignment.inputs.len() {
        return Err(SatisfactionError::InputLength(
            inputs.len(),
            assignment.inputs.len() - 1,
        ));
    }

    {
        let idx = assignment.inputs[0];
        assignment.lc[idx - 1].1 = F::one();
    }

    for (input, idx) in inputs.iter().zip(assignment.inputs.iter().skip(1)) {
        assignment.lc[*idx - 1].1 = *input;
    }

    // Check all multiplication gates are satisfied
    for (i, ((a, b), c)) in assignment
        .a
        .iter()
        .zip(assignment.b.iter())
        .zip(assignment.c.iter())
        .enumerate()
    {
        if (*a) * (*b) != (*c) {
            let path = match &assignment.mults[i] {
                MultType::Allocation(a, b) => format!("allocation({}, {})", a, b),
                MultType::Constraint(path) => path.clone(),
            };
            return Err(SatisfactionError::Multiplication(path, *a, *b, *c));
        }
    }

    // Check all linear constraints are satisfied
    for lc in assignment.lc.iter() {
        let lhs = lc.0.evaluate(&assignment.a, &assignment.b, &assignment.c);
        if lhs != lc.1 {
            return Err(SatisfactionError::Linear(lc.2.clone(), lhs, lc.1));
        }
    }

    Ok(true)
}

/// Checks if the recursive circuit produces a satisfying assignment for the
/// constraint system, given the previous proof and new payload.
pub fn recursive_is_satisfied<
    E1,
    E2,
    C: RecursiveCircuit<E1::Scalar> + RecursiveCircuit<E2::Scalar>,
    S: SynthesisDriver,
>(
    e1params: &Params<E1>,
    e2params: &Params<E2>,
    old_proof: Option<&RecursiveProof<E2, E1>>,
    circuit: &C,
    new_payload: &[u8],
) -> Result<bool, SatisfactionError<E1::Scalar>>
where
    E1: Curve<Base = <E2 as Curve>::Scalar>,
    E2: Curve<Base = <E1 as Curve>::Scalar>,
{
    let (newdeferred, new_leftovers, old_leftovers) = match old_proof {
        Some(old_proof) => {
            let (_, newdeferred, l1, l2) = old_proof.verify_inner(e2params, e1params, circuit)?;

            (newdeferred, l1, l2)
        }
        None => (
            Deferred::dummy(e2params.k),
            Leftovers::dummy(e2params),
            Leftovers::dummy(e1params),
        ),
    };

    let mut circuit = VerificationCircuit::<E1, E2, _> {
        _marker: PhantomData,
        params: e2params,
        base_case: None,
        proof: None,
        inner_circuit: circuit,
        new_payload,
        old_leftovers: Some(old_leftovers.clone()),
        new_leftovers: Some(new_leftovers.clone()),
        deferred: Some(newdeferred.clone()),
    };

    if old_proof.is_some() {
        circuit.base_case = Some(false);
        circuit.proof = old_proof;
    } else {
        circuit.base_case = Some(true);
    }

    let mut inputs = vec![];
    inputs.extend(new_payload.iter().cloned());
    inputs.extend(old_leftovers.to_bytes());
    inputs.extend(new_leftovers.to_bytes());
    inputs.extend(newdeferred.to_bytes());

    let mut bitinputs = vec![];
    for byte in inputs {
        for i in 0..8 {
            let b = ((byte >> i) & 1) == 1;
            if b {
                bitinputs.push(E1::Scalar::one());
            } else {
                bitinputs.push(E1::Scalar::zero());
            }
        }
    }

    is_satisfied::<_, _, S>(&circuit, &bitinputs)
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

        fn pop_namespace(&mut self, _gadget_name: Option<String>) {
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

        fn pop_namespace(&mut self, _gadget_name: Option<String>) {
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

/// Counts the constraints within each namespace of a circuit.
pub fn constraint_count<F: Field, C: Circuit<F>, S: SynthesisDriver>(
    circuit: &C,
) -> Result<BTreeMap<String, (usize, usize)>, SynthesisError> {
    struct Assignment {
        counts: BTreeMap<String, (usize, usize)>,
        current_namespace: Vec<String>,
        n_stack: Vec<usize>,
        q_stack: Vec<usize>,
        current_n: usize,
        current_q: usize,
    }

    impl<'a, F: Field> Backend<F> for &'a mut Assignment {
        type LinearConstraintIndex = usize;

        /// Create a new multiplication gate.
        fn new_multiplication_gate<A, AR>(&mut self, _annotation: Option<A>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.current_n += 1;
        }

        /// Create a new linear constraint, returning a cached index.
        fn new_linear_constraint<A, AR>(&mut self, _annotation: A) -> Self::LinearConstraintIndex
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            self.current_q += 1;
            self.current_q
        }

        /// Compute a `LinearConstraintIndex` from `q`.
        fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
            q
        }

        fn push_namespace<NR, N>(&mut self, name_fn: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            let name = name_fn().into();
            self.current_namespace.push(name);

            // Save the current counts for the parent namespace.
            self.n_stack.push(self.current_n);
            self.q_stack.push(self.current_q);

            // Re-initialize counts for the current node.
            self.current_n = 0;
            self.current_q = 0;
        }

        fn pop_namespace(&mut self, _gadget_name: Option<String>) {
            // Store the counts for the node we are leaving.
            let node = self
                .current_namespace
                .pop()
                .expect("Should be leaving a namespace we entered");
            let path = compute_path(&self.current_namespace, node);
            self.counts.insert(path, (self.current_n, self.current_q));

            // Accumulate counts from this node into its parent.
            self.current_n += self.n_stack.pop().unwrap_or(0);
            self.current_q += self.q_stack.pop().unwrap_or(0);
        }
    }

    let mut assignment = Assignment {
        counts: BTreeMap::default(),
        current_namespace: vec![],
        n_stack: vec![],
        q_stack: vec![],
        current_n: 0,
        current_q: 0,
    };

    S::synthesize(&mut assignment, circuit)?;

    // Insert counts for the root circuit.
    assignment.counts.insert(
        String::default(),
        (assignment.current_n, assignment.current_q),
    );

    Ok(assignment.counts)
}

/// Counts the constraints within each namespace of a recursive circuit.
pub fn recursive_constraint_count<
    E1,
    E2,
    C: RecursiveCircuit<E1::Scalar> + RecursiveCircuit<E2::Scalar>,
    S: SynthesisDriver,
>(
    e2params: &Params<E2>,
    circuit: &C,
    new_payload: &[u8],
) -> Result<BTreeMap<String, (usize, usize)>, SynthesisError>
where
    E1: Curve<Base = <E2 as Curve>::Scalar>,
    E2: Curve<Base = <E1 as Curve>::Scalar>,
{
    let circuit = VerificationCircuit::<E1, E2, _> {
        _marker: PhantomData,
        params: e2params,
        base_case: None,
        proof: None,
        inner_circuit: circuit,
        new_payload,
        old_leftovers: None,
        new_leftovers: None,
        deferred: None,
    };

    constraint_count::<_, _, S>(&circuit)
}
