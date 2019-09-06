use crate::{Backend, Field, SynthesisDriver};
use std::ops::{Add, Mul, Neg, Sub};

#[derive(Copy, Clone, Debug)]
pub enum Variable {
    A(usize),
    B(usize),
    C(usize),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum SynthesisError {
    AssignmentMissing,
    DivisionByZero,
    Unsatisfiable,
    Violation,
}

pub trait Circuit<F: Field> {
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

pub trait ConstraintSystem<FF: Field> {
    const ONE: Variable;

    fn alloc<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        value: F,
    ) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    fn enforce_zero(&mut self, lc: LinearCombination<FF>);

    fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>;

    fn namespace<NR, N>(&mut self, name_fn: N) -> &mut Self
    where
        N: FnOnce() -> NR,
        NR: Into<String>,
    {
        self
    }
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Coeff<F: Field> {
    Zero,
    One,
    NegativeOne,
    Full(F),
}

impl<F: Field> From<F> for Coeff<F> {
    fn from(coeff: F) -> Coeff<F> {
        Coeff::Full(coeff)
    }
}

impl<F: Field> Mul<F> for Coeff<F> {
    type Output = Coeff<F>;

    fn mul(self, other: F) -> Self {
        match self {
            Coeff::Zero => Coeff::Zero,
            Coeff::One => Coeff::Full(other),
            Coeff::NegativeOne => Coeff::Full(-other),
            Coeff::Full(val) => Coeff::Full(val * other),
        }
    }
}

impl<F: Field> Mul<Coeff<F>> for Coeff<F> {
    type Output = Coeff<F>;

    fn mul(self, other: Coeff<F>) -> Self {
        match (self, other) {
            (Coeff::Zero, _) | (_, Coeff::Zero) => Coeff::Zero,
            (Coeff::One, a) | (a, Coeff::One) => a,
            (Coeff::NegativeOne, a) | (a, Coeff::NegativeOne) => -a,
            (Coeff::Full(a), Coeff::Full(b)) => Coeff::Full(a * b),
        }
    }
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

    pub fn double(self) -> Self {
        match self {
            Coeff::Zero => Coeff::Zero,
            Coeff::One => Coeff::Full(F::one() + F::one()),
            Coeff::NegativeOne => Coeff::Full(-(F::one() + F::one())),
            Coeff::Full(val) => Coeff::Full(val + val),
        }
    }

    pub fn value(&self) -> F {
        match *self {
            Coeff::Zero => F::zero(),
            Coeff::One => F::one(),
            Coeff::NegativeOne => -F::one(),
            Coeff::Full(val) => val,
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

impl<F: Field> LinearCombination<F> {
    pub fn evaluate(&self, a: &[F], b: &[F], c: &[F]) -> F {
        let mut acc = F::zero();
        for &(var, ref coeff) in self.as_ref() {
            let mut var = match var {
                Variable::A(index) => a[index - 1],
                Variable::B(index) => b[index - 1],
                Variable::C(index) => c[index - 1],
            };
            coeff.multiply(&mut var);
            acc = acc + var;
        }
        acc
    }
}

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

impl<'a, F: Field> Add<(Coeff<F>, &'a LinearCombination<F>)> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn add(mut self, (coeff, other): (Coeff<F>, &'a LinearCombination<F>)) -> LinearCombination<F> {
        for s in &other.0 {
            self = self + (s.1 * coeff, s.0);
        }

        self
    }
}

impl<'a, F: Field> Sub<(Coeff<F>, &'a LinearCombination<F>)> for LinearCombination<F> {
    type Output = LinearCombination<F>;

    fn sub(mut self, (coeff, other): (Coeff<F>, &'a LinearCombination<F>)) -> LinearCombination<F> {
        for s in &other.0 {
            self = self - (s.1 * coeff, s.0);
        }

        self
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
        fn set_var<FF>(&mut self, var: Variable, value: FF) -> Result<(), SynthesisError>
        where
            FF: FnOnce() -> Result<F, SynthesisError>,
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
        fn new_multiplication_gate(&mut self) {
            self.n += 1;
            self.a.push(F::zero());
            self.b.push(F::zero());
            self.c.push(F::zero());
        }

        /// Create a new linear constraint, returning a cached index.
        fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex {
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
        const ONE: Variable = Variable::A(0);

        fn alloc<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
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
            annotation: A,
            value: F,
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

        fn multiply<F>(
            &mut self,
            values: F,
        ) -> Result<(Variable, Variable, Variable), SynthesisError>
        where
            F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
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
        const ONE: Variable = Variable::A(0);

        fn alloc<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
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
            annotation: A,
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

        fn multiply<F>(
            &mut self,
            values: F,
        ) -> Result<(Variable, Variable, Variable), SynthesisError>
        where
            F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
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
    }

    let mut enforce = Enforce {
        events: record.events.into_iter(),
        vars: 1,
    };

    circuit.synthesize(&mut enforce)?;

    return Ok(());
}
