use crate::Field;
use std::marker::PhantomData;
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

/// Represents a constraint system which can have new variables
/// allocated and constrains between them formed.
pub trait ConstraintSystem<FF: Field> {
    const ONE: Variable;

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable. The given `annotation` function is invoked
    /// in testing contexts in order to derive a unique name for this variable in the current
    /// namespace.
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>;

    /// Allocate a public variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>;

    /// Create a linear constraint from the provided LinearCombination.
    fn enforce_zero(&mut self, lc: LinearCombination<FF>);

    /// Create a multiplication gate. The provided function is used to determine the
    /// assignments.
    fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>;
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
            acc += var;
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

/// This is a backend for the `SynthesisDriver` to relay information about
/// the concrete circuit. One backend might just collect basic information
/// about the circuit for verification, while another actually constructs
/// a witness.
pub trait Backend<FF: Field> {
    type LinearConstraintIndex;

    /// Get the value of a variable. Can return None if we don't know.
    fn get_var(&self, _var: Variable) -> Option<FF> {
        None
    }

    /// Set the value of a variable.
    ///
    /// `allocation` will be Some if this multiplication gate is being used for
    /// variable allocation, and None if it is being used as a constraint.
    ///
    /// Might error if this backend expects to know it.
    fn set_var<F>(&mut self, _var: Variable, _value: F) -> Result<(), SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
    {
        Ok(())
    }

    /// Create a new multiplication gate.
    ///
    /// `allocation` will be Some if this multiplication gate is being used as a
    /// constraint, and None if it is being used for variable allocation.
    fn new_multiplication_gate(&mut self) {}

    /// Create a new linear constraint, returning a cached index.
    fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex;

    /// Insert a term into a linear constraint.
    fn insert_coefficient(
        &mut self,
        _var: Variable,
        _coeff: Coeff<FF>,
        _y: &Self::LinearConstraintIndex,
    ) {
    }

    /// Compute a `LinearConstraintIndex` from `q`.
    fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex;

    /// Mark y^{_index} as the power of y cooresponding to the public input
    /// coefficient for the next public input, in the k(Y) polynomial. Also
    /// gives the value of the public input.
    fn new_k_power(&mut self, _index: usize, _value: Option<FF>) -> Result<(), SynthesisError> {
        Ok(())
    }
}

/// This is an abstraction which synthesizes circuits.
pub trait SynthesisDriver {
    fn synthesize<F: Field, C: Circuit<F>, B: Backend<F>>(
        backend: B,
        circuit: &C,
    ) -> Result<(), SynthesisError>;
}

pub struct Basic;

impl SynthesisDriver for Basic {
    fn synthesize<F: Field, C: Circuit<F>, B: Backend<F>>(
        backend: B,
        circuit: &C,
    ) -> Result<(), SynthesisError> {
        struct Synthesizer<F: Field, B: Backend<F>> {
            backend: B,
            current_variable: Option<usize>,
            _marker: PhantomData<F>,
            q: usize,
            n: usize,
        }

        impl<FF: Field, B: Backend<FF>> ConstraintSystem<FF> for Synthesizer<FF, B> {
            const ONE: Variable = Variable::A(1);

            fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<FF, SynthesisError>,
            {
                match self.current_variable.take() {
                    Some(index) => {
                        let var_a = Variable::A(index);
                        let var_b = Variable::B(index);
                        let var_c = Variable::C(index);

                        let mut product = None;

                        let value_a = self.backend.get_var(var_a);

                        self.backend.set_var(var_b, || {
                            let value_b = value()?;
                            product = Some(value_a.ok_or(SynthesisError::AssignmentMissing)?);
                            product.as_mut().map(|product| {
                                *product = (*product) * value_b;
                            });

                            Ok(value_b)
                        })?;

                        self.backend
                            .set_var(var_c, || product.ok_or(SynthesisError::AssignmentMissing))?;

                        self.current_variable = None;

                        Ok(var_b)
                    }
                    None => {
                        self.n += 1;
                        let index = self.n;
                        self.backend.new_multiplication_gate();

                        let var_a = Variable::A(index);

                        self.backend.set_var(var_a, value)?;

                        self.current_variable = Some(index);

                        Ok(var_a)
                    }
                }
            }

            fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<FF, SynthesisError>,
            {
                let value = value();
                let input_var = self.alloc(|| value)?;

                self.enforce_zero(LinearCombination::zero() + input_var);
                self.backend.new_k_power(self.q, value.ok())?;

                Ok(input_var)
            }

            fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
                self.q += 1;
                // TODO: Don't create a new linear constraint if lc is empty
                let y = self.backend.new_linear_constraint();

                for (var, coeff) in lc.as_ref() {
                    self.backend.insert_coefficient(*var, *coeff, &y);
                }
            }

            fn multiply<F>(
                &mut self,
                values: F,
            ) -> Result<(Variable, Variable, Variable), SynthesisError>
            where
                F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
            {
                self.n += 1;
                let index = self.n;
                self.backend.new_multiplication_gate();

                let a = Variable::A(index);
                let b = Variable::B(index);
                let c = Variable::C(index);

                let mut b_val = None;
                let mut c_val = None;

                self.backend.set_var(a, || {
                    let (a, b, c) = values()?;

                    b_val = Some(b);
                    c_val = Some(c);

                    Ok(a)
                })?;

                self.backend
                    .set_var(b, || b_val.ok_or(SynthesisError::AssignmentMissing))?;

                self.backend
                    .set_var(c, || c_val.ok_or(SynthesisError::AssignmentMissing))?;

                Ok((a, b, c))
            }
        }

        let mut tmp: Synthesizer<F, B> = Synthesizer {
            backend: backend,
            current_variable: None,
            _marker: PhantomData,
            q: 0,
            n: 0,
        };

        let one = tmp
            .alloc_input(|| Ok(F::one()))
            .expect("should have no issues");

        match (one, <Synthesizer<F, B> as ConstraintSystem<F>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {}
            _ => panic!("ONE variable is incorrect"),
        }

        circuit.synthesize(&mut tmp)?;

        // println!("n = {}", tmp.n);
        // println!("q = {}", tmp.q);

        Ok(())
    }
}

/*
s(X, Y) =   \sum\limits_{i=1}^N u_i(Y) X^{-i}
          + \sum\limits_{i=1}^N v_i(Y) X^{i}
          + \sum\limits_{i=1}^N w_i(Y) X^{i+N}
where
    u_i(Y) = \sum\limits_{q=1}^Q Y^{q} u_{i,q}
    v_i(Y) = \sum\limits_{q=1}^Q Y^{q} v_{i,q}
    w_i(Y) = \sum\limits_{q=1}^Q Y^{q} w_{i,q}
*/
#[derive(Clone)]
pub struct SxEval<F: Field> {
    y: F,

    // current value of y^{q}
    cur_y: F,

    // x^{-i} (\sum\limits_{q=1}^Q y^{q} u_{i,q})
    u: Vec<F>,
    // x^{i} (\sum\limits_{q=1}^Q y^{q} v_{i,q})
    v: Vec<F>,
    // x^{i+N} (\sum\limits_{q=1}^Q y^{q} w_{i,q})
    w: Vec<F>,
}

impl<F: Field> SxEval<F> {
    pub fn new(y: F) -> Self {
        let u = vec![];
        let v = vec![];
        let w = vec![];

        SxEval {
            y,
            cur_y: F::one(),
            u,
            v,
            w,
        }
    }

    pub fn poly(self) -> (Vec<F>, Vec<F>, Vec<F>) {
        (self.u, self.v, self.w)
    }
}

impl<'a, F: Field> Backend<F> for &'a mut SxEval<F> {
    type LinearConstraintIndex = F;

    fn new_multiplication_gate(&mut self) {
        self.u.push(F::zero());
        self.v.push(F::zero());
        self.w.push(F::zero());
    }

    fn new_linear_constraint(&mut self) -> F {
        self.cur_y.mul_assign(&self.y);
        self.cur_y
    }

    fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
        self.y.pow(&[q as u64, 0, 0, 0])
    }

    fn insert_coefficient(&mut self, var: Variable, coeff: Coeff<F>, y: &F) {
        let acc = match var {
            Variable::A(index) => &mut self.u[index - 1],
            Variable::B(index) => &mut self.v[index - 1],
            Variable::C(index) => &mut self.w[index - 1],
        };

        let mut tmp = *y;
        coeff.multiply(&mut tmp);
        *acc = *acc + tmp;
    }
}

/*
s(x, Y) =   \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q} u_{i,q} x^{-i}
          + \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q} v_{i,q} x^{i}
          + \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q} w_{i,q} x^{i+N}
*/
pub struct SyEval<F: Field> {
    // x^{-1}, ..., x^{-N}
    a: Vec<F>,

    // x^1, ..., x^{N}
    b: Vec<F>,

    // x^{N+1}, ..., x^{2*N}
    c: Vec<F>,

    // Coefficients of s(x, Y)
    poly: Vec<F>,
}

impl<F: Field> SyEval<F> {
    pub fn new(x: F, n: usize, q: usize) -> Self {
        let xinv = x.invert().unwrap();
        let mut tmp = F::one();
        let mut a = vec![F::zero(); n];
        for a in &mut a {
            tmp.mul_assign(&xinv); // tmp = x^{-i}
            *a = tmp;
        }

        let mut tmp = F::one();
        let mut b = vec![F::zero(); n];
        for b in &mut b {
            tmp.mul_assign(&x); // tmp = x^{i}
            *b = tmp;
        }

        let mut c = vec![F::zero(); n];
        for c in c.iter_mut() {
            tmp.mul_assign(&x); // tmp = x^{i+N}
            *c = tmp;
        }

        let mut poly = Vec::with_capacity(q);
        poly.push(F::zero()); // constant term

        SyEval {
            a,
            b,
            c,
            poly: poly,
        }
    }

    pub fn poly(self) -> Vec<F> {
        self.poly
    }
}

impl<'a, F: Field> Backend<F> for &'a mut SyEval<F> {
    type LinearConstraintIndex = usize;

    fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex {
        let index = self.poly.len();
        self.poly.push(F::zero());
        index
    }

    fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
        q
    }

    fn insert_coefficient(&mut self, var: Variable, coeff: Coeff<F>, q: &usize) {
        match var {
            Variable::A(index) => {
                let index = index - 1;
                // Y^{q} += X^{-i} * coeff
                let mut tmp = self.a[index];
                coeff.multiply(&mut tmp);
                let yindex = *q;
                self.poly[yindex].add_assign(&tmp);
            }
            Variable::B(index) => {
                let index = index - 1;
                // Y^{q} += X^{i} * coeff
                let mut tmp = self.b[index];
                coeff.multiply(&mut tmp);
                let yindex = *q;
                self.poly[yindex].add_assign(&tmp);
            }
            Variable::C(index) => {
                let index = index - 1;
                // Y^{q} += X^{i+N} * coeff
                let mut tmp = self.c[index];
                coeff.multiply(&mut tmp);
                let yindex = *q;
                self.poly[yindex].add_assign(&tmp);
            }
        };
    }
}
