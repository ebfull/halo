use crate::{Backend, Curve, Field, SynthesisDriver};
use std::ops::{Add, Mul, Neg, Sub};

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

// impl Variable {
//     fn get_index(&self) -> usize {
//         match *self {
//             Variable::A(index) => index,
//             Variable::B(index) => index,
//             Variable::C(index) => index,
//         }
//     }
// }

#[derive(Clone, Copy, Debug)]
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
        fn new_k_power(&mut self, index: usize) {
            self.inputs.push(index);
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

#[derive(Copy, Clone)]
pub struct AllocatedNum<F> {
    value: Option<F>,
    var: Variable,
}

impl<F: Field> AllocatedNum<F> {
    pub fn alloc<FF, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let var = cs.alloc(|| value)?;

        Ok(AllocatedNum {
            value: value.ok(),
            var,
        })
    }

    pub fn alloc_input<FF, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let var = cs.alloc_input(|| value)?;

        Ok(AllocatedNum {
            value: value.ok(),
            var,
        })
    }

    pub fn inputify<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<AllocatedNum<F>, SynthesisError> {
        let var = cs.alloc_input(|| {
            self.value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        cs.enforce_zero(LinearCombination::from(self.var) - var);

        Ok(AllocatedNum {
            value: self.value,
            var
        })
    }

    pub fn mul<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let product = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a + b)));

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
}

#[derive(Copy, Clone)]
enum Num<F: Field> {
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

    pub fn scale(&self, by: F) -> Num<F> {
        match self {
            Num::Constant(v) => Num::Constant(*v * by),
            Num::Allocated(coeff, var) => Num::Allocated(*coeff * by, *var),
        }
    }

    pub fn value(&self) -> Option<F> {
        match *self {
            Num::Constant(v) => Some(v.value()),
            Num::Allocated(coeff, var) => var.value.map(|v| (coeff * v).value()),
        }
    }
}

#[derive(Clone)]
struct Combination<F: Field> {
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

pub fn rescue_gadget<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    inputs: &[AllocatedNum<F>],
) -> Result<AllocatedNum<F>, SynthesisError> {
    let mut cur = Combination::from(Num::constant(F::ALPHA));
    for input in inputs {
        for _ in 0..30 {
            cur = cur + *input;
            cur = Combination::from(cur.square(cs)?);
        }
    }

    cur.square(cs)
}

pub fn rescue<F: Field>(inputs: &[F]) -> F {
    let mut cur = F::ALPHA;
    for input in inputs {
        for _ in 0..30 {
            cur = cur + *input;
            cur = cur.square()
        }
    }

    cur.square()
}
