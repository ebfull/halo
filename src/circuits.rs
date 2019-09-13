use crate::fields::Field;
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

use crate::AllocatedBit;

pub trait RecursiveCircuit<F: Field> {
    fn base_payload(&self) -> Vec<bool>;

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        old_payload: &[AllocatedBit],
        new_payload: &[AllocatedBit],
    ) -> Result<(), SynthesisError>;
}

pub trait Circuit<F: Field> {
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

/// Represents a constraint system which can have new variables
/// allocated and constrains between them formed.
pub trait ConstraintSystem<FF: Field> {
    /// Represents the type of the "root" of this constraint system
    /// so that nested namespaces can minimize indirection.
    type Root: ConstraintSystem<FF>;

    const ONE: Variable;

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable. The given `annotation` function is invoked
    /// in testing contexts in order to derive a unique name for this variable in the current
    /// namespace.
    fn alloc<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    /// Allocate a public variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        value: F,
    ) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    /// Create a linear constraint from the provided LinearCombination.
    fn enforce_zero(&mut self, lc: LinearCombination<FF>);

    /// Create a multiplication gate. The provided function is used to determine the
    /// assignments.
    fn multiply<F, A, AR>(
        &mut self,
        annotation: A,
        values: F,
    ) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    /// Create a new (sub)namespace and enter into it. Not intended
    /// for downstream use; use `namespace` instead.
    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR;

    /// Exit out of the existing namespace. Not intended for
    /// downstream use; use `namespace` instead.
    fn pop_namespace(&mut self, gadget_name: Option<String>);

    /// Gets the "root" constraint system, bypassing the namespacing.
    /// Not intended for downstream use; use `namespace` instead.
    fn get_root(&mut self) -> &mut Self::Root;

    /// Begin a namespace for this constraint system.
    fn namespace<'a, NR, N>(&'a mut self, name_fn: N) -> Namespace<'a, FF, Self::Root>
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.get_root().push_namespace(name_fn);

        Namespace(self.get_root(), PhantomData)
    }
}

/// This is a "namespaced" constraint system which borrows a constraint system (pushing
/// a namespace context) and, when dropped, pops out of the namespace context.
pub struct Namespace<'a, FF: Field, CS: ConstraintSystem<FF> + 'a>(&'a mut CS, PhantomData<FF>);

impl<'cs, FF: Field, CS: ConstraintSystem<FF>> ConstraintSystem<FF> for Namespace<'cs, FF, CS> {
    type Root = CS::Root;

    const ONE: Variable = CS::ONE;

    fn alloc<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.0.alloc(annotation, value)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.0.alloc_input(annotation, value)
    }

    fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
        self.0.enforce_zero(lc)
    }

    fn multiply<F, A, AR>(
        &mut self,
        annotation: A,
        values: F,
    ) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.0.multiply(annotation, values)
    }

    // Downstream users who use `namespace` will never interact with these
    // functions and they will never be invoked because the namespace is
    // never a root constraint system.

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        panic!("only the root's push_namespace should be called");
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        panic!("only the root's pop_namespace should be called");
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self.0.get_root()
    }
}

impl<'a, FF: Field, CS: ConstraintSystem<FF>> Drop for Namespace<'a, FF, CS> {
    fn drop(&mut self) {
        let gadget_name = {
            #[cfg(feature = "gadget-traces")]
            {
                let mut gadget_name = None;
                let mut is_second_frame = false;
                backtrace::trace(|frame| {
                    if is_second_frame {
                        // Resolve this instruction pointer to a symbol name
                        backtrace::resolve_frame(frame, |symbol| {
                            gadget_name = symbol.name().map(|name| format!("{:#}", name));
                        });

                        // We are done
                        false
                    } else {
                        // We want the next frame
                        is_second_frame = true;
                        true
                    }
                });
                gadget_name
            }

            #[cfg(not(feature = "gadget-traces"))]
            None
        };

        self.get_root().pop_namespace(gadget_name)
    }
}

/// Convenience implementation of ConstraintSystem<E> for mutable references to
/// constraint systems.
impl<'cs, FF: Field, CS: ConstraintSystem<FF>> ConstraintSystem<FF> for &'cs mut CS {
    type Root = CS::Root;

    const ONE: Variable = CS::ONE;

    fn alloc<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        (**self).alloc(annotation, value)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        (**self).alloc_input(annotation, value)
    }

    fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
        (**self).enforce_zero(lc)
    }

    fn multiply<F, A, AR>(
        &mut self,
        annotation: A,
        values: F,
    ) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(FF, FF, FF), SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        (**self).multiply(annotation, values)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        (**self).push_namespace(name_fn)
    }

    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        (**self).pop_namespace(gadget_name)
    }

    fn get_root(&mut self) -> &mut Self::Root {
        (**self).get_root()
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
