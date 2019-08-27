use crate::*;

pub trait ProvingSystem<C: Curve> {
    type Proof;
    type ProofMetadata: Clone;

    fn new_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        old_proof: &Self::ProofMetadata,
    ) -> Result<Self::Proof, SynthesisError>;
    fn verify_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        proof: &Self::Proof,
        inputs: &[C::Scalar],
    ) -> Result<bool, SynthesisError>;
    fn get_proof_metadata<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        proof: &Self::Proof,
    ) -> Result<Self::ProofMetadata, SynthesisError>;
}

#[derive(Clone)]
pub struct Subsonic<C> {
    g: C,
    d: usize,
    n: usize,
    k: usize,
    generators: Vec<C>,
}

impl<C: Curve> Subsonic<C> {
    pub fn new(k: usize) -> Self {
        assert!(k > 3);
        let d = 1 << k;
        let n = d / 4;

        // TODO
        let mut generators = Vec::with_capacity(d);
        let mut cur = C::Scalar::from_u64(1239847893);
        for _ in 0..d {
            generators.push(C::one() * cur);
            cur = cur * &C::Scalar::from_u64(1239847893);
        }

        Subsonic {
            g: C::one(),
            k,
            d,
            n,
            generators,
        }
    }

    pub fn commit(&self, v: &[C::Scalar], right_edge: bool) -> C {
        assert!(self.generators.len() >= v.len());
        if right_edge {
            util::multiexp(&v, &self.generators[(self.generators.len() - v.len())..])
        } else {
            util::multiexp(&v, &self.generators[0..(self.generators.len() - v.len())])
        }
    }
}

pub struct SubsonicProof<C: Curve> {
    pub r_commitment: C,
}

impl<C: Curve> SubsonicProof<C> {
    pub fn dummy() -> Self {
        SubsonicProof {
            r_commitment: C::one(),
        }
    }
}

#[derive(Clone)]
pub struct ProofMetadata<C: Curve> {
    pub s3: C,
    pub y3: C::Scalar,
}

impl<C: Curve> ProofMetadata<C> {
    pub fn dummy() -> Self {
        ProofMetadata {
            s3: C::one(),
            y3: C::Scalar::one(),
        }
    }
}

impl<C: Curve> ProvingSystem<C> for Subsonic<C> {
    type Proof = SubsonicProof<C>;
    type ProofMetadata = ProofMetadata<C>;

    fn new_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        old_proof_data: &Self::ProofMetadata,
    ) -> Result<Self::Proof, SynthesisError> {
        struct Assignment<F: Field> {
            n: usize,
            q: usize,
            a: Vec<F>,
            b: Vec<F>,
            c: Vec<F>,
            inputs: Vec<usize>,
        }

        impl<'a, F: Field> Backend<F> for &'a mut Assignment<F> {
            type LinearConstraintIndex = usize;

            fn get_var(&self, var: Variable) -> Option<F> {
                Some(match var {
                    Variable::A(index) => self.a[index - 1],
                    Variable::B(index) => self.b[index - 1],
                    Variable::C(index) => self.c[index - 1],
                })
            }

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

            fn new_multiplication_gate(&mut self) {
                self.n += 1;
                self.a.push(F::zero());
                self.b.push(F::zero());
                self.c.push(F::zero());
            }

            fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex {
                self.q += 1;
                self.q
            }

            fn insert_coefficient(
                &mut self,
                _var: Variable,
                _coeff: Coeff<F>,
                _y: &Self::LinearConstraintIndex,
            ) {

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
            inputs: vec![],
        };

        // TODO: this will start failing soon
        assert!(is_satisfied::<_, _, S>(circuit, &[]).unwrap());

        S::synthesize(&mut assignment, circuit)?;

        assert!(assignment.n < self.n);
        assert!(assignment.q < self.d);

        assignment.a.resize(self.n, C::Scalar::zero());
        assignment.b.resize(self.n, C::Scalar::zero());
        assignment.c.resize(self.n, C::Scalar::zero());

        // Compute r(X, Y)
        let mut rx = Vec::with_capacity(3 * assignment.n + 1);
        rx.extend(assignment.c.into_iter().rev());
        rx.extend(assignment.b.into_iter().rev());
        rx.push(C::Scalar::zero());
        rx.extend(assignment.a.into_iter());

        // Commit to r(X, Y)
        let r_commitment = self.commit(&rx, true);

        // Obtain the challenge y
        let transcript = C::Base::zero();
        let transcript = append_point::<C>(transcript, &r_commitment);
        let (transcript, y) = get_challenge::<_, C::Scalar>(transcript);

        // Compute s(X, y)
        // TODO

        Ok(SubsonicProof { r_commitment })
    }
    fn verify_proof<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        proof: &Self::Proof,
        inputs: &[C::Scalar],
    ) -> Result<bool, SynthesisError> {
        let transcript = C::Base::zero();
        let transcript = append_point::<C>(transcript, &proof.r_commitment);
        let (transcript, y) = get_challenge::<_, C::Scalar>(transcript);

        Ok(true)
    }
    fn get_proof_metadata<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        proof: &Self::Proof,
    ) -> Result<Self::ProofMetadata, SynthesisError> {
        Ok(ProofMetadata::dummy())
    }
}

fn append_point<C: Curve>(transcript: C::Base, p: &C) -> C::Base
{
    let (x, y) = p.get_xy().unwrap();
    rescue(&[transcript, x, y])
}

fn get_challenge<F1: Field, F2: Field>(
    transcript: F1
) -> (F1, F2)
{
    let new_transcript = rescue(&[transcript]);
    let challenge = transcript.get_lower_128();

    (new_transcript, F2::from_u128(challenge))
}
