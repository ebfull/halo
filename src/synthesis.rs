use crate::{Circuit, Coeff, ConstraintSystem, Field, LinearCombination, SynthesisError, Variable};
use std::marker::PhantomData;

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

    /// Set the value of a variable. Might error if this backend expects to know it.
    fn set_var<F>(&mut self, _var: Variable, _value: F) -> Result<(), SynthesisError>
    where
        F: FnOnce() -> Result<FF, SynthesisError>,
    {
        Ok(())
    }

    /// Create a new multiplication gate.
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

            fn alloc<F, A, AR>(
                &mut self,
                annotation: A,
                value: F,
            ) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<FF, SynthesisError>,
                A: FnOnce() -> AR,
                AR: Into<String>,
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
                let value = value();
                let input_var = self.alloc(annotation, || value)?;

                self.enforce_zero(LinearCombination::zero() + input_var);
                self.backend.new_k_power(self.q, value.ok())?;

                Ok(input_var)
            }

            fn enforce_zero(&mut self, lc: LinearCombination<FF>) {
                self.q += 1;
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
            .alloc_input(|| "one", || Ok(F::one()))
            .expect("should have no issues");

        match (one, <Synthesizer<F, B> as ConstraintSystem<F>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {}
            _ => panic!("ONE variable is incorrect"),
        }

        circuit.synthesize(&mut tmp)?;

        println!("n = {}", tmp.n);
        println!("q = {}", tmp.q);

        Ok(())
    }
}
