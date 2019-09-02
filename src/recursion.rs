use super::circuits::*;
use super::gadgets::*;
use super::proofs::*;
use super::synthesis::Basic;
use super::{Curve, Field};
use std::cell::RefCell;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct RecursiveProof<E1: Curve, E2: Curve> {
    proof: Proof<E1>,
    oldproof1: Leftovers<E1>,
    oldproof2: Leftovers<E2>,
    deferred: Deferred<E1>,
    payload: Vec<u8>,
}

impl<E1, E2> RecursiveProof<E1, E2>
where
    E1: Curve<Base = <E2 as Curve>::Scalar>,
    E2: Curve<Base = <E1 as Curve>::Scalar>,
{
    pub fn create_proof<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        old_proof: Option<&RecursiveProof<E2, E1>>,
        circuit: &CS,
        new_payload: &[u8],
    ) -> Result<Self, SynthesisError> {
        let (new_leftovers, old_leftovers) = match old_proof {
            Some(old_proof) => {
                let (_, l1, l2) = old_proof.verify_inner(e2params, e1params, circuit)?;

                (l1, l2)
            },
            None => {
                (Leftovers::dummy(e2params), Leftovers::dummy(e1params))
            }
        };

        let mut circuit = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload,
            old_leftovers: Some(old_leftovers.clone()),
            new_leftovers: Some(new_leftovers.clone()),
            deferred: RefCell::new(None),
        };

        if old_proof.is_some() {
            circuit.base_case = Some(false);
            circuit.proof = old_proof;
        } else {
            circuit.base_case = Some(true);
        }

        // Now make the proof...
        let (proof, _) = Proof::new::<_, Basic>(e1params, &circuit, &old_leftovers)?;

        Ok(RecursiveProof {
            proof,
            oldproof1: old_leftovers,
            oldproof2: new_leftovers,
            deferred: circuit.deferred.into_inner().unwrap(),
            payload: new_payload.to_vec(),
        })
    }

    fn verify_inner<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        &self,
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        circuit: &CS,
    ) -> Result<(bool, Leftovers<E1>, Leftovers<E2>), SynthesisError>
    {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: None,
            deferred: RefCell::new(None),
        };

        let circuit2 = VerificationCircuit::<E2, E1, _> {
            _marker: PhantomData,
            params: e1params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: None,
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
                .verify::<_, Basic>(&self.oldproof1, e1params, &circuit1, &bitinputs)?;

        let worked = worked & self.oldproof2.verify::<_, Basic>(e2params, &circuit2)?;

        Ok((worked, leftovers, self.oldproof2.clone()))
    }

    pub fn verify<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        &self,
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        circuit: &CS,
    ) -> Result<bool, SynthesisError>
    {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: None,
            deferred: RefCell::new(None),
        };

        let circuit2 = VerificationCircuit::<E2, E1, _> {
            _marker: PhantomData,
            params: e1params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: None,
            deferred: RefCell::new(None),
        };

        let (worked, a, b) = self.verify_inner(e1params, e2params, circuit)?;

        Ok(worked &
            a.verify::<_, Basic>(e1params, &circuit1)? &
            b.verify::<_, Basic>(e2params, &circuit2)?)
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
    new_leftovers: Option<Leftovers<C2>>,
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
        for (j, byte) in self.new_payload.into_iter().enumerate() {
            for i in 0..8 {
                let bit = (*byte >> i) & 1 == 1;
                payload_bits.push(cs.alloc_input(
                    || format!("payload bit {}", 8 * j + i),
                    || {
                        Ok(if bit {
                            E1::Scalar::one()
                        } else {
                            E1::Scalar::zero()
                        })
                    },
                )?);
            }
        }

        let mut leftovers1 = vec![];
        if let Some(l) = &self.old_leftovers {
            let bytes = l.to_bytes();
            for (j, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    leftovers1.push(cs.alloc_input(
                        || format!("old leftovers bit {}", 8 * j + i),
                        || {
                            Ok(if bit {
                                E1::Scalar::one()
                            } else {
                                E1::Scalar::zero()
                            })
                        },
                    )?);
                }
            }
        } else {
            // 256 * (3 + k)
            let num_bits = 256 * (3 + self.params.k);
            for i in 0..num_bits {
                leftovers1.push(cs.alloc_input(
                    || format!("old leftovers bit {}", i),
                    || Ok(E1::Scalar::zero()),
                )?);
            }
        }

        let mut leftovers2 = vec![];
        if let Some(l) = &self.new_leftovers {
            let bytes = l.to_bytes();
            for (j, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    leftovers2.push(cs.alloc_input(
                        || format!("new leftovers bit {}", 8 * j + i),
                        || {
                            Ok(if bit {
                                E1::Scalar::one()
                            } else {
                                E1::Scalar::zero()
                            })
                        },
                    )?);
                }
            }
        } else {
            // 256 * (3 + k)
            let num_bits = 256 * (3 + self.params.k);
            for i in 0..num_bits {
                leftovers2.push(cs.alloc_input(
                    || format!("old leftovers bit {}", i),
                    || Ok(E1::Scalar::zero()),
                )?);
            }
        }

        // Compute k(Y) commitment

        // TODO
        {
            *self.deferred.borrow_mut() = Some(Deferred::dummy())
        }

        self.inner_circuit.synthesize(cs)
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
