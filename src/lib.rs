mod circuits;
mod commitment;
mod curves;
mod fields;
mod synthesis;
mod transcript;
mod util;

pub use circuits::*;
pub use commitment::*;
pub use curves::{Curve, Ec1};
pub use fields::{Field, Fp};
pub use synthesis::{Backend, Basic, SynthesisDriver};
pub use transcript::*;

trait ProvingSystem<C: Curve> {
    type Parameters;
    type Proof;

    fn new_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        circuit: &CS,
        parameters: &Self::Parameters,
    ) -> Result<Self::Proof, SynthesisError>;
    fn verify_proof(
        proof: &Self::Proof,
        parameters: &Self::Parameters,
        inputs: &[C::Scalar],
    ) -> bool;
}

struct Subsonic<C> {
    g: C,
    m: usize,
    n: usize,
    log_n: usize,
}

impl<C: Curve> Subsonic<C> {
    pub fn new(m: usize, log_n: usize) -> Self {
        Subsonic {
            g: C::one(),
            m,
            log_n,
            n: 1 << log_n,
        }
    }
}

struct SubsonicProof;

impl SubsonicProof {
    pub fn invalid() -> Self {
        SubsonicProof
    }
}

impl<C: Curve> ProvingSystem<C> for Subsonic<C> {
    type Parameters = Self;
    type Proof = SubsonicProof;

    fn new_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        circuit: &CS,
        parameters: &Self::Parameters,
    ) -> Result<Self::Proof, SynthesisError> {
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

        let mut assignment = Assignment::<C::Scalar> {
            n: 0,
            q: 0,
            a: vec![],
            b: vec![],
            c: vec![],
            lc: vec![],
            inputs: vec![],
        };

        S::synthesize(&mut assignment, circuit)?;

        let mut inputs = vec![];

        for idx in assignment.inputs.iter() {
            let val =
                assignment.lc[*idx - 1]
                    .0
                    .evaluate(&assignment.a, &assignment.b, &assignment.c);
            assignment.lc[*idx - 1].1 = val;

            inputs.push((*idx, val))
        }

        // Check all multiplication gates are satisfied
        for ((a, b), c) in assignment
            .a
            .iter()
            .zip(assignment.b.iter())
            .zip(assignment.c.iter())
        {
            if (*a) * (*b) != (*c) {
                return Ok(SubsonicProof::invalid());
            }
        }

        // Check all linear constraints are satisfied
        for lc in assignment.lc.iter() {
            let lhs = lc.0.evaluate(&assignment.a, &assignment.b, &assignment.c);
            if lhs != lc.1 {
                return Ok(SubsonicProof::invalid());
            }
        }

        Ok(SubsonicProof::invalid())
    }
    fn verify_proof(
        proof: &Self::Proof,
        parameters: &Self::Parameters,
        inputs: &[C::Scalar],
    ) -> bool {
        true
    }
}

#[test]
fn test_subsonic() {
    struct DinkyCircuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
    }

    impl<F: Field> Circuit<F> for DinkyCircuit<F> {
        fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc_input(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;

            let (l, r, o) = cs.multiply(|| {
                let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                let c = a * b;

                Ok((a, b, c))
            })?;

            cs.enforce_zero(LinearCombination::from(l) - a);
            cs.enforce_zero(LinearCombination::from(r) - b);

            let c = cs.alloc_input(|| {
                let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                let c = a * b;

                Ok(c)
            })?;

            cs.enforce_zero(LinearCombination::from(o) - c);

            Ok(())
        }
    }

    let params = Subsonic::new(2, 4);
    let mycircuit = DinkyCircuit {
        a: Some(Fp::from_u64(10)),
        b: Some(Fp::from_u64(10)),
    };
    assert!(circuits::is_satisfied::<_, _, Basic>(&mycircuit, &[Fp::from_u64(10), Fp::from_u64(100)]).unwrap());

    let proof = Subsonic::<Ec1>::new_proof::<_, Basic>(
        &mycircuit,
        &params
    ).unwrap();

    assert!(
        Subsonic::<Ec1>::verify_proof(&proof, &params, &[Fp::from_u64(10), Fp::from_u64(100)])
    );
}