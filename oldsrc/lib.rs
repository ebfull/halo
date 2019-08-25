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
    fn verify_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        circuit: &CS,
        proof: &Self::Proof,
        parameters: &Self::Parameters,
        inputs: &[C::Scalar],
    ) -> Result<bool, SynthesisError>;
}

struct Subsonic<C> {
    g: C,
    m: usize,
    n: usize,
    log_n: usize,
    mn: usize,
    generators: Vec<C>,
}

impl<C: Curve> Subsonic<C> {
    pub fn new(m: usize, log_n: usize) -> Self {
        let n = 1 << log_n;

        let mut generators = Vec::with_capacity(n);
        let mut cur = C::Scalar::from_u64(1239847893);
        for _ in 0..n {
            generators.push(C::one() * cur);
            cur = cur * C::Scalar::from_u64(1239847893);
        }

        Subsonic {
            g: C::one(),
            m,
            log_n,
            n,
            mn: m * n,
            generators,
        }
    }
}

struct SubsonicProof<C: Curve> {
    r: GrothCommitment<C>,
    s: C,
}

impl<C: Curve> SubsonicProof<C> {
    pub fn invalid(m: usize, n: usize) -> Self {
        SubsonicProof {
            r: GrothCommitment::dummy_commitment(m, n),
            s: C::one(),
        }
    }
}

fn hash_groth_commitment<C: Curve>(comm: &GrothCommitment<C>) -> C::Base {
    let mut blob = Vec::with_capacity(comm.get_points().len() * 2);
    for (x, y) in comm.get_points().iter().map(|p| p.get_xy()) {
        blob.push(x);
        blob.push(y);
    }

    rescue(&blob)
}

fn get_challenge<F: Field, O: Field>(transcript: F) -> (O, F) {
    let challenge = transcript.get_lower_128();
    let transcript = transcript.square() * transcript;

    (challenge, transcript)
}

impl<C: Curve> ProvingSystem<C> for Subsonic<C> {
    type Parameters = Self;
    type Proof = SubsonicProof<C>;

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
                return Ok(SubsonicProof::invalid(parameters.m, parameters.n));
            }
        }

        // Check all linear constraints are satisfied
        for lc in assignment.lc.iter() {
            let lhs = lc.0.evaluate(&assignment.a, &assignment.b, &assignment.c);
            if lhs != lc.1 {
                return Ok(SubsonicProof::invalid(parameters.m, parameters.n));
            }
        }

        // We need room to commit to stuff
        assert!(parameters.mn > (assignment.n * 4));
        assert!(parameters.mn > assignment.q);

        let mut rx = Vec::with_capacity(3 * assignment.n + 1);
        rx.extend(assignment.c.into_iter().rev());
        rx.extend(assignment.b.into_iter().rev());
        rx.push(C::Scalar::zero());
        rx.extend(assignment.a.into_iter());

        let r = commitment::create_groth_commitment(
            &rx,
            true,
            &parameters.generators,
            parameters.m,
            parameters.n,
        );

        let transcript = hash_groth_commitment(&r);
        let (y, transcript) = get_challenge::<C::Base, C::Scalar>(transcript);

        // Compute k(y) for now
        let mut k_y = C::Scalar::zero();
        for (index, value) in inputs {
            let y = y.pow(index as u64);
            k_y = k_y + (y * value);
        }

        let s = C::one() * k_y;

        Ok(SubsonicProof { r, s })
    }

    fn verify_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        circuit: &CS,
        proof: &Self::Proof,
        parameters: &Self::Parameters,
        inputs: &[C::Scalar],
    ) -> Result<bool, SynthesisError> {
        struct Assignment {
            n: usize,
            q: usize,
            inputs: Vec<usize>,
        }

        impl<'a, F: Field> Backend<F> for &'a mut Assignment {
            type LinearConstraintIndex = usize;

            /// Create a new multiplication gate.
            fn new_multiplication_gate(&mut self) {
                self.n += 1;
            }

            /// Create a new linear constraint, returning a cached index.
            fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex {
                self.q += 1;
                self.q
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

        let mut assignment = Assignment {
            n: 0,
            q: 0,
            inputs: vec![],
        };

        S::synthesize(&mut assignment, circuit)?;

        let transcript = hash_groth_commitment(&proof.r);
        let (y, transcript) = get_challenge::<C::Base, C::Scalar>(transcript);

        // Compute k(y)
        let mut k_y = C::Scalar::zero();
        k_y = k_y + y; // ONE
        for (value, index) in inputs.iter().zip(assignment.inputs.into_iter().skip(1)) {
            let y = y.pow(index as u64);
            k_y = k_y + (y * *value);
        }

        if proof.s != C::one() * k_y {
            return Ok(false);
        }

        Ok(true)
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
            let a =
                AllocatedNum::alloc_input(cs, || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = AllocatedNum::alloc(cs, || self.b.ok_or(SynthesisError::AssignmentMissing))?;

            let result = rescue_gadget(cs, &[a, b])?;

            result.inputify(cs)?;

            Ok(())
        }
    }

    let params = Subsonic::new(3, 8);
    let mycircuit = DinkyCircuit {
        a: Some(Fp::from_u64(10)),
        b: Some(Fp::from_u64(15)),
    };
    let expected = rescue(&[Fp::from_u64(10), Fp::from_u64(15)]);
    assert!(
        circuits::is_satisfied::<_, _, Basic>(&mycircuit, &[Fp::from_u64(10), expected]).unwrap()
    );

    let proof = Subsonic::<Ec1>::new_proof::<_, Basic>(&mycircuit, &params).unwrap();

    assert!(Subsonic::<Ec1>::verify_proof::<_, Basic>(
        &mycircuit,
        &proof,
        &params,
        &[Fp::from_u64(10), expected]
    )
    .unwrap());
}
