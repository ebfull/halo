use super::newcircuits::*;
use super::newproofs::*;
use super::{Curve, CurveAffine, Field};
use std::marker::PhantomData;

pub struct RecursiveProof<E1: CurveAffine, E2: CurveAffine> {
    proof: Proof<E1>,
    local_amortized: Amortized<E1>,
    remote_amortized: Amortized<E2>,
    remote_deferred: Deferred<E2::Scalar>,
}

pub(crate) struct VerificationCircuit<'a, C1: CurveAffine, C2: CurveAffine, CS: Circuit<C1::Scalar>>
{
    pub(crate) _marker: PhantomData<(C1, C2)>,
    pub(crate) params: &'a Params<C2>,
    pub(crate) inner_circuit: &'a CS,
    // pub(crate) base_case: Option<bool>,
    // pub(crate) proof: Option<&'a RecursiveProof<C2, C1>>,
    // pub(crate) new_payload: &'a [u8],
    // pub(crate) forkvalues: Option<&'a [u8]>,
    // pub(crate) old_leftovers: Option<Leftovers<C1>>,
    // pub(crate) new_leftovers: Option<Leftovers<C2>>,
    // pub(crate) deferred: Option<Deferred<C2::Scalar>>,
}

impl<E1, E2> RecursiveProof<E1, E2>
where
    E1: CurveAffine<Base = <E2 as CurveAffine>::Scalar>,
    E2: CurveAffine<Base = <E1 as CurveAffine>::Scalar>,
{
    pub fn create_proof<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        old_proof: Option<&RecursiveProof<E2, E1>>,
        circuit: &CS,
    ) -> Result<Self, SynthesisError> {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            // base_case: None,
            // proof: None,
            inner_circuit: circuit,
            // new_payload: &self.payload,
            // forkvalues: None,
            // old_leftovers: None,
            // new_leftovers: None,
            // deferred: None,
        };

        let circuit2 = VerificationCircuit::<E2, E1, _> {
            _marker: PhantomData,
            params: e1params,
            // base_case: None,
            // proof: None,
            inner_circuit: circuit,
            // new_payload: &self.payload,
            // forkvalues: None,
            // old_leftovers: None,
            // new_leftovers: None,
            // deferred: None,
        };

        let (remote_deferred, remote_amortized, local_amortized) = match old_proof {
            Some(old_proof) => old_proof.verify_inner(e2params)?,
            None => (
                Deferred::new(e2params.k),
                Amortized::new(e2params, &circuit2)?,
                Amortized::new(e1params, &circuit1)?,
            ),
        };

        let proof = create_proof(e1params, &circuit1, &local_amortized)?;

        Ok(RecursiveProof {
            proof,
            local_amortized,
            remote_amortized,
            remote_deferred,
        })
    }

    pub fn verify_inner(
        &self,
        e1params: &Params<E1>,
    ) -> Result<(Deferred<E1::Scalar>, Amortized<E1>, Amortized<E2>), SynthesisError> {
        // The public inputs for the proof consists of
        // 1. The (new) payload.
        // 2. The leftovers that should be used to verify this proof.
        // 3. The leftovers that should be used to construct a proof
        //    for the next proof.
        // 4. The deferred information that has to be manually checked
        //    by the verifier.

        let mut inputs = vec![];
        // inputs.extend(self.local_amortized.public_input_string());
        // inputs.extend(self.remote_amortized.public_input_string());
        // inputs.extend(self.remote_deferred.public_input_string());

        let mut k_commitment = crate::pedersen::pedersen_hash(&inputs, &e1params.generators[2..]);
        k_commitment += e1params.generators[1]; // ONE
        let k_commitment = k_commitment.to_affine();

        let (local_amortized, deferred) = verify_proof_with_commitment(
            e1params,
            &self.proof,
            &self.local_amortized,
            k_commitment,
        )?;

        Ok((deferred, local_amortized, self.remote_amortized.clone()))
    }

    pub fn verify<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        &self,
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        circuit: &CS,
    ) -> Result<(), SynthesisError> {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            // base_case: None,
            // proof: None,
            inner_circuit: circuit,
            // new_payload: &self.payload,
            // forkvalues: None,
            // old_leftovers: None,
            // new_leftovers: None,
            // deferred: None,
        };

        let circuit2 = VerificationCircuit::<E2, E1, _> {
            _marker: PhantomData,
            params: e1params,
            // base_case: None,
            // proof: None,
            inner_circuit: circuit,
            // new_payload: &self.payload,
            // forkvalues: None,
            // old_leftovers: None,
            // new_leftovers: None,
            // deferred: None,
        };

        let (_, local_amortized, remote_amortized) = self.verify_inner(e1params)?;

        local_amortized.verify(e1params, &circuit1)?;
        remote_amortized.verify(e2params, &circuit2)?;

        Ok(())
    }
}

impl<'a, E1: CurveAffine, E2: CurveAffine<Base = E1::Scalar>, Inner: Circuit<E1::Scalar>>
    Circuit<E1::Scalar> for VerificationCircuit<'a, E1, E2, Inner>
{
    fn synthesize<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        Ok(())
    }
}

#[test]
fn recursion_threshold() {
    use crate::curves::*;
    use crate::fields::*;

    let e1params = Params::<EpAffine>::new(19);
    let e2params = Params::<EqAffine>::new(19);

    struct CubingCircuit;

    impl<F: Field> Circuit<F> for CubingCircuit {
        fn synthesize<CS: ConstraintSystem<F>>(&self, _: &mut CS) -> Result<(), SynthesisError> {
            Ok(())
        }
    }

    let circuit = CubingCircuit;

    use std::time::Instant;

    let first_proof = RecursiveProof::create_proof(&e1params, &e2params, None, &circuit).unwrap();
    first_proof.verify(&e1params, &e2params, &circuit).unwrap();
    let second_proof =
        RecursiveProof::create_proof(&e2params, &e1params, Some(&first_proof), &circuit).unwrap();
    second_proof.verify(&e2params, &e1params, &circuit).unwrap();
    let third_proof =
        RecursiveProof::create_proof(&e1params, &e2params, Some(&second_proof), &circuit).unwrap();
    third_proof.verify(&e1params, &e2params, &circuit).unwrap();
    let fourth_proof =
        RecursiveProof::create_proof(&e2params, &e1params, Some(&third_proof), &circuit).unwrap();
    fourth_proof.verify(&e2params, &e1params, &circuit).unwrap();
    let proof_start = Instant::now();
    let fifth_proof =
        RecursiveProof::create_proof(&e1params, &e2params, Some(&fourth_proof), &circuit).unwrap();
    let proof_elapsed = proof_start.elapsed();
    let verify_start = Instant::now();
    fifth_proof.verify(&e1params, &e2params, &circuit).unwrap();
    let verify_elapsed = verify_start.elapsed();
    println!(
        "prover elapsed: {:?}, verifier elapsed: {:?}",
        proof_elapsed, verify_elapsed
    );
}
