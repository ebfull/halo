use super::circuits::*;
use super::gadgets::*;
use super::proofs::*;
use super::synthesis::Basic;
use super::{Curve, Field};
use std::marker::PhantomData;
use std::cell::RefCell;

#[derive(Clone)]
pub struct RecursiveProof<E1: Curve, E2: Curve> {
    proof: Proof<E1>,
    oldproof1: Leftovers<E1>,
    oldproof2: Leftovers<E2>,
    deferred: Deferred<E1>,
    payload: Vec<u8>,
}

#[derive(Clone)]
pub struct RecursiveParameters<E1: Curve, E2: Curve> {
    a: Params<E1>,
    b: Params<E2>,
}

pub trait GetParamsA<E> {
    fn get_a(&self) -> &Params<E>;
}

pub trait GetParamsB<E> {
    fn get_b(&self) -> &Params<E>;
}

impl<E1: Curve, E2: Curve> GetParamsA<E1> for RecursiveParameters<E1, E2> {
    fn get_a(&self) -> &Params<E1> {
        &self.a
    }
}

impl<E1: Curve, E2: Curve> GetParamsB<E2> for RecursiveParameters<E1, E2> {
    fn get_b(&self) -> &Params<E2> {
        &self.b
    }
}

impl<E1: Curve, E2: Curve> RecursiveParameters<E1, E2> {
    pub fn new(k: usize) -> Self {
        RecursiveParameters {
            a: Params::new(k),
            b: Params::new(k),
        }
    }

    pub fn switch(self) -> RecursiveParameters<E2, E1> {
        RecursiveParameters {
            a: self.b,
            b: self.a,
        }
    }
}

struct VerificationCircuit<'a, C1: Curve, C2: Curve, CS: Circuit<C1::Scalar>> {
    _marker: PhantomData<(C1, C2)>,
    params: &'a Params<C2>,
    base_case: Option<bool>,
    inner_circuit: &'a CS,
    proof: Option<&'a RecursiveProof<C2, C1>>,
    new_payload: &'a [u8],
    old_leftovers: Option<Leftovers<C1>>,
    new_leftovers: RefCell<Option<Leftovers<C2>>>,
    deferred: RefCell<Option<Deferred<C1>>>,
}

impl<'a, E1: Curve, E2: Curve<Base = E1::Scalar>, Inner: Circuit<E1::Scalar>> Circuit<E1::Scalar>
    for VerificationCircuit<'a, E1, E2, Inner>
{
    fn synthesize<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // Witness the commitment to r(X, Y)
        // let r_commitment = CurvePoint::<E2>::alloc(cs, || {
        //     let (x, y) = self.proof.r_commitment.get_xy().unwrap();
        //     Ok((x, y))
        // })?;

        // // The transcript starts out with value zero.
        // let transcript = AllocatedNum::alloc(cs, || {
        //     Ok(E1::Scalar::zero())
        // })?;
        // cs.enforce_zero(transcript.lc());

        // // Hash the commitment to r(X, Y)
        // let transcript = append_point(cs, &transcript, &r_commitment)?;

        // // Obtain the challenge y_cur
        // let (transcript, y_cur) = obtain_challenge(cs, &transcript)?;

        // let proof = self.proof.clone().unwrap();
        
        // The public inputs to our circuit include
        // 1. The new payload.
        // 2. Leftovers from the previous proof, which will be used
        // to construct the outer proof.
        // 2. Leftovers resulting from verifying the inner proof
        // 3. New "deferred" computations
        
        // + 256 * (3 + k)
        // + 256 * (3 + k)
        // + 256 * deferred.len()

        let mut payload_bits = vec![];
        for byte in self.new_payload {
            for i in 0..8 {
                let bit = (*byte >> i) & 1 == 1;
                payload_bits.push(cs.alloc_input(|| {
                    Ok(if bit {
                        E1::Scalar::one()
                    } else {
                        E1::Scalar::zero()
                    })
                })?);
            }
        }

        let mut leftovers1 = vec![];
        if let Some(l) = &self.old_leftovers {
            let bytes = l.to_bytes();
            for byte in bytes {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    leftovers1.push(cs.alloc_input(|| {
                        Ok(if bit {
                            E1::Scalar::one()
                        } else {
                            E1::Scalar::zero()
                        })
                    })?);
                }
            }
        } else {
            // 256 * (3 + k)
            let num_bits = 256 * (3 + self.params.k);
            for _ in 0..num_bits {
                leftovers1.push(cs.alloc_input(|| Ok(E1::Scalar::zero()))?);
            }
        }

        //let mut leftovers2 = vec![];

        {
            *self.new_leftovers.borrow_mut() = Some(Leftovers::dummy(self.params));
            *self.deferred.borrow_mut() = Some(Deferred::dummy())
        }
        

        self.inner_circuit.synthesize(cs)
    }
}

impl<E1: Curve<Base = <E2 as Curve>::Scalar>, E2: Curve<Base = <E1 as Curve>::Scalar>>
    RecursiveProof<E1, E2>
{
    pub fn create_proof<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>, P>(
        params: &P,
        old_proof: Option<&RecursiveProof<E2, E1>>,
        circuit: &CS,
        new_payload: &[u8],
    ) -> Result<Self, SynthesisError>
        where P: GetParamsA<E1> + GetParamsB<E2>
    {
        let old_leftovers = match old_proof {
            Some(old_proof) => {
                old_proof.oldproof2.clone()
            },
            None => {
                Leftovers::dummy(params.get_a())
            }
        };

        let new_leftovers = match old_proof {
            Some(old_proof) => {
                // Run the verification procedure on it
                let circuit2 = VerificationCircuit::<E2, E1, _> {
                    _marker: PhantomData,
                    params: params.get_a(),
                    base_case: None,
                    proof: None,
                    inner_circuit: circuit,
                    new_payload: &old_proof.payload,
                    old_leftovers: None,
                    new_leftovers: RefCell::new(None),
                    deferred: RefCell::new(None),
                };

                old_proof.verify(params, &circuit2);

                unimplemented!()
            },
            None => {
                Leftovers::dummy(params.get_a())
            }
        };

        let mut circuit = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: params.get_b(),
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload,
            old_leftovers: Some(old_leftovers.clone()),
            new_leftovers: RefCell::new(None),
            deferred: RefCell::new(None),
        };

        if old_proof.is_some() {
            circuit.base_case = Some(false);
            circuit.proof = old_proof;
        } else {
            circuit.base_case = Some(true);
        }

        // Now make the proof...
        let (proof, _) = Proof::new::<_, Basic>(params.get_a(), &circuit, &old_leftovers)?;

        Ok(RecursiveProof {
            proof,
            oldproof1: old_leftovers,
            oldproof2: circuit.new_leftovers.into_inner().unwrap(),
            deferred: circuit.deferred.into_inner().unwrap(),
            payload: new_payload.to_vec(),
        })
    }

    fn verify_proof_inner<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>, P>(
        &self,
        params: &P,
        circuit: &CS,
        payload: &[u8],
    ) -> Result<(bool, Leftovers<E1>, Leftovers<E2>), SynthesisError>
        where P: GetParamsA<E1> + GetParamsB<E2>
    {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: &params.get_b(),
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: payload,
            old_leftovers: None,
            new_leftovers: RefCell::new(None),
            deferred: RefCell::new(None),
        };

        let circuit2 = VerificationCircuit::<E2, E1, _> {
            _marker: PhantomData,
            params: &params.get_a(),
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: payload,
            old_leftovers: None,
            new_leftovers: RefCell::new(None),
            deferred: RefCell::new(None),
        };

        // The public inputs for the proof consists of
        // 1. The (new) payload.
        // 2. The leftovers that should be used to verify this proof.
        // 3. The leftovers that should be used to construct a proof
        //    for the next proof.
        // 4. The deferred information that has to be manually checked
        //    by the verifier.

        let mut inputs = vec![];
        inputs.extend(self.payload.iter().cloned());
        inputs.extend(self.oldproof1.to_bytes());
        inputs.extend(self.oldproof2.to_bytes());
        inputs.extend(self.deferred.to_bytes());

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

        let (worked, leftovers) =
            self.proof
                .verify::<_, Basic>(&self.oldproof1, &params.get_a(), &circuit1, &bitinputs)?;
        
        let worked = worked & self.oldproof2.verify::<_, Basic>(&params.get_b(), &circuit2)?;

        Ok((worked, leftovers, self.oldproof2.clone()))
    }

    pub fn verify<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>, P>(
        &self,
        params: &P,
        circuit: &CS,
    ) -> Result<bool, SynthesisError>
        where P: GetParamsA<E1> + GetParamsB<E2>
    {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: params.get_b(),
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: RefCell::new(None),
            deferred: RefCell::new(None),
        };

        let circuit2 = VerificationCircuit::<E2, E1, _> {
            _marker: PhantomData,
            params: params.get_a(),
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: RefCell::new(None),
            deferred: RefCell::new(None),
        };

        let (worked, a, b) = self.verify_proof_inner(params, circuit, &self.payload)?;

        Ok(worked &
            a.verify::<_, Basic>(params.get_a(), &circuit1)? &
            b.verify::<_, Basic>(params.get_b(), &circuit2)?)
    }
}

#[derive(Clone)]
struct Deferred<C: Curve> {
    _marker: PhantomData<C>, /*
                             g: C,
                             challenges: Vec<C::Scalar>,
                             s_new: C,
                             y_new: C::Scalar
                             */
}

impl<C: Curve> Deferred<C> {
    fn dummy() -> Self {
        Deferred {
            _marker: PhantomData,
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        vec![]
    }
}
