use super::newcircuits::*;
use super::newgadgets::*;
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
    pub(crate) local_amortized: Option<Amortized<C1>>,
    pub(crate) remote_amortized: Option<Amortized<C2>>,
    pub(crate) remote_deferred: Option<Deferred<C2::Scalar>>,
    pub(crate) proof: Option<&'a RecursiveProof<C2, C1>>,
    pub(crate) base_case: Option<bool>,
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
        let mut dummy_proof = None;

        let mut circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            local_amortized: None,
            remote_amortized: None,
            remote_deferred: None,
            proof: None,
            base_case: None,
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
            local_amortized: None,
            remote_amortized: None,
            remote_deferred: None,
            proof: None,
            base_case: None,
            inner_circuit: circuit,
            // new_payload: &self.payload,
            // forkvalues: None,
            // old_leftovers: None,
            // new_leftovers: None,
            // deferred: None,
        };

        let (remote_deferred, remote_amortized, local_amortized) = match old_proof {
            Some(old_proof) => {
                let tmp = old_proof.verify_inner(e2params)?;

                circuit1.proof = Some(old_proof);
                circuit1.base_case = Some(false);

                tmp
            }
            None => {
                let tmp = (
                    Deferred::new(e2params.k),
                    Amortized::new(e2params, &circuit2)?,
                    Amortized::new(e1params, &circuit1)?,
                );

                let dummy_deferred = Deferred::new(e1params.k);

                dummy_proof = Some(RecursiveProof {
                    proof: Proof::dummy(e2params, &tmp.1, &tmp.0),
                    local_amortized: tmp.1.clone(),
                    remote_amortized: tmp.2.clone(),
                    remote_deferred: dummy_deferred,
                });

                circuit1.proof = Some(&dummy_proof.as_ref().unwrap());
                circuit1.base_case = Some(true);

                tmp
            }
        };

        circuit1.local_amortized = Some(local_amortized.clone());
        circuit1.remote_amortized = Some(remote_amortized.clone());
        circuit1.remote_deferred = Some(remote_deferred.clone());

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
        inputs.extend(self.local_amortized.public_input_string());
        inputs.extend(self.remote_amortized.public_input_string());
        inputs.extend(self.remote_deferred.public_input_string());

        let mut k_commitment = crate::pedersen::pedersen_hash(&inputs, &e1params.generators[2..]);
        k_commitment += e1params.generators[1]; // ONE
        let k_commitment = k_commitment.to_affine();

        let (local_amortized, remote_deferred) = verify_proof_with_commitment(
            e1params,
            &self.proof,
            &self.local_amortized,
            k_commitment,
        )?;

        Ok((
            remote_deferred,
            local_amortized,
            self.remote_amortized.clone(),
        ))
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
            local_amortized: None,
            remote_amortized: None,
            remote_deferred: None,
            proof: None,
            base_case: None,
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
            local_amortized: None,
            remote_amortized: None,
            remote_deferred: None,
            proof: None,
            base_case: None,
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

fn synth<F: Field, I>(window_size: usize, constants: I, assignment: &mut [F])
where
    I: IntoIterator<Item = F>,
{
    assert_eq!(assignment.len(), 1 << window_size);

    for (i, constant) in constants.into_iter().enumerate() {
        let cur = constant - assignment[i];
        assignment[i] = cur;
        for (j, eval) in assignment.iter_mut().enumerate().skip(i + 1) {
            if j & i == i {
                eval.add_assign(&cur);
            }
        }
    }
}

impl<'a, E1: CurveAffine, E2: CurveAffine<Base = E1::Scalar>, Inner: Circuit<E1::Scalar>>
    VerificationCircuit<'a, E1, E2, Inner>
{
    fn inputify<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        input_bits: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        struct InputContext {
            p: Variable,
            q: Variable,
            r: Variable,
            s: Variable,
            t: Variable,
            v: Variable,
            w: Variable,
        }

        let mut check_these = vec![];

        // (1 - 2N) (A + 2B + 1) (ES - E + 1)
        for chunk in input_bits.chunks(4) {
            // p * q = r
            // s * t = v
            // v = public input

            let a = &chunk[0];
            let b = &chunk[1];
            let n = &chunk[2];
            let e = &chunk[3];

            let mut p_value = None;
            let mut q_value = None;
            let mut r_value = None;
            let mut t_value = None;
            let mut v_value = None;

            let (p, q, r) = cs.multiply(|| {
                let a = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let a = if a {
                    E1::Scalar::one()
                } else {
                    E1::Scalar::zero()
                };
                let b = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let b = if b {
                    E1::Scalar::one()
                } else {
                    E1::Scalar::zero()
                };
                let n = n.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let n = if n {
                    E1::Scalar::one()
                } else {
                    E1::Scalar::zero()
                };

                p_value = Some(E1::Scalar::one() - &n - &n);
                q_value = Some(a + &b + &b + &E1::Scalar::one());
                r_value = Some(p_value.unwrap() * &q_value.unwrap());

                Ok((p_value.unwrap(), q_value.unwrap(), r_value.unwrap()))
            })?;

            let (s, t, v) = cs.multiply(|| {
                let e = e.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let e = if e {
                    E1::Scalar::one()
                } else {
                    E1::Scalar::zero()
                };

                t_value = Some(e * &E1::Scalar::ZETA - &e + &E1::Scalar::one());
                v_value = Some(r_value.unwrap() * &t_value.unwrap());

                Ok((r_value.unwrap(), t_value.unwrap(), v_value.unwrap()))
            })?;

            // Allocate the public input. TODO: could be folded into v,
            // need proving system support to do that...
            let w = cs.alloc_input(|| v_value.ok_or(SynthesisError::AssignmentMissing))?;

            check_these.push(InputContext {
                p,
                q,
                r,
                s,
                t,
                v,
                w,
            });
        }

        // All public inputs are assigned; we can now unpack
        for (chunk, context) in input_bits.chunks(4).zip(check_these.into_iter()) {
            let a = &chunk[0];
            let b = &chunk[1];
            let n = &chunk[2];
            let e = &chunk[3];

            // p = 1 - 2N
            // q = A + 2B + 1
            // s = r
            // t = ES - E + 1 = (S - 1)E + 1
            // v = w

            cs.enforce_zero(
                LinearCombination::from(CS::ONE) - n.get_variable() - n.get_variable() - context.p,
            );
            cs.enforce_zero(
                LinearCombination::from(CS::ONE)
                    + b.get_variable()
                    + b.get_variable()
                    + a.get_variable()
                    - context.q,
            );
            cs.enforce_zero(LinearCombination::from(context.s) - context.r);
            cs.enforce_zero(
                LinearCombination::from(CS::ONE)
                    + (
                        Coeff::Full(E1::Scalar::ZETA - &E1::Scalar::one()),
                        e.get_variable(),
                    )
                    - context.t,
            );
            cs.enforce_zero(LinearCombination::from(context.v) - context.w);
        }

        Ok(())
    }

    fn get_challenge_scalar<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        bits: &[AllocatedBit],
    ) -> Result<Num<E1::Scalar>, SynthesisError> {
        assert_eq!(bits.len(), 128);

        let mut acc = Combination::from(Num::constant(
            (E1::Scalar::ZETA + &E1::Scalar::one()).double(),
        ));

        let mut coeffs = [E1::Scalar::zero(); 4];
        synth(
            2,
            vec![
                E1::Scalar::one(),
                -E1::Scalar::one(),
                E1::Scalar::ZETA,
                -E1::Scalar::ZETA,
            ],
            &mut coeffs,
        );

        // let mut real_challenge = E1::Scalar::zero();
        // let mut coeff = E1::Scalar::one();
        // for bit in bits.iter() {
        //     if let Some(val) = bit.get_value() {
        //         if val {
        //             real_challenge = real_challenge + &coeff;
        //         }
        //     }
        //     coeff = coeff.double();
        // }

        for i in (0..64).rev() {
            let should_negate = bits[i * 2 + 1].clone();
            let should_endo = bits[i * 2].clone();
            let combined = AllocatedBit::and(&mut cs, &should_negate, &should_endo)?;

            let lc = Combination::zero()
                + (
                    Coeff::Full(coeffs[0]),
                    Num::from(AllocatedNum::one(&mut cs)),
                )
                + (
                    Coeff::Full(coeffs[1]),
                    Num::from(AllocatedNum::from(should_negate.clone())),
                )
                + (
                    Coeff::Full(coeffs[2]),
                    Num::from(AllocatedNum::from(should_endo.clone())),
                )
                + (
                    Coeff::Full(coeffs[3]),
                    Num::from(AllocatedNum::from(combined.clone())),
                );

            acc = acc.scale(E1::Scalar::from_u64(2));
            acc = acc + lc;
        }

        let tmp = acc.evaluate(&mut cs)?;

        // if let Some(val) = tmp.value() {
        //     let challenge = crate::util::Challenge(real_challenge.get_lower_128());
        //     assert_eq!(
        //         crate::util::get_challenge_scalar::<E1::Scalar>(challenge),
        //         val
        //     );
        //     assert_eq!(challenge.0, 0);
        // }

        Ok(tmp)
    }

    fn get_scalar<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        bits: &[AllocatedBit],
    ) -> Result<Num<E1::Scalar>, SynthesisError> {
        assert_eq!(bits.len(), 256);

        let mut acc = Combination::zero();

        let mut coeff = E1::Scalar::one();
        for bit in bits.iter() {
            acc = acc
                + (
                    Coeff::Full(coeff),
                    Num::from(AllocatedNum::from(bit.clone())),
                );
            coeff = coeff.double();
        }

        acc.evaluate(&mut cs)
    }

    fn check_deferred<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        mut deferred_bits: &[AllocatedBit],
        mut amortized_bits: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        let y_old = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];
        let y_cur = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];
        let x = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];
        let z1 = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];
        let z2 = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];
        let z3 = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];
        let z4 = self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?;
        deferred_bits = &deferred_bits[128..];

        let mut challenges_old_sq = vec![];
        for _ in 0..self.params.k {
            challenges_old_sq.push(self.get_challenge_scalar(&mut cs, &deferred_bits[0..128])?);
            deferred_bits = &deferred_bits[128..];
        }

        let hash1 = self.get_scalar(&mut cs, &deferred_bits[0..256])?;
        deferred_bits = &deferred_bits[256..];
        let hash2 = self.get_scalar(&mut cs, &deferred_bits[0..256])?;
        deferred_bits = &deferred_bits[256..];
        let hash3 = self.get_scalar(&mut cs, &deferred_bits[0..256])?;
        deferred_bits = &deferred_bits[256..];
        let f_opening = self.get_scalar(&mut cs, &deferred_bits[0..256])?;
        deferred_bits = &deferred_bits[256..];
        let b = self.get_scalar(&mut cs, &deferred_bits[0..256])?;
        deferred_bits = &deferred_bits[256..];

        assert_eq!(deferred_bits.len(), 0);

        let y_new = self.get_challenge_scalar(&mut cs, &amortized_bits[0..128])?;
        amortized_bits = &amortized_bits[128..];

        let mut challenges_new_sq = vec![];
        for _ in 0..self.params.k {
            challenges_new_sq.push(self.get_challenge_scalar(&mut cs, &amortized_bits[0..128])?);
            amortized_bits = &amortized_bits[128..];
        }

        assert_eq!(amortized_bits.len(), 8 * 32 * 2 * 2);

        let mut challenges_old = vec![];
        let mut challenges_old_inv = vec![];
        for challenge_old_sq in challenges_old_sq {
            let challenge_old = challenge_old_sq.sqrt(&mut cs)?;
            let challenge_old_inv = challenge_old.invert(&mut cs)?;
            challenges_old.push(challenge_old);
            challenges_old_inv.push(challenge_old_inv);
        }

        let mut challenges_new = vec![];
        let mut challenges_new_inv = vec![];
        for challenge_new_sq in challenges_new_sq {
            let challenge_new = challenge_new_sq.sqrt(&mut cs)?;
            let challenge_new_inv = challenge_new.invert(&mut cs)?;
            challenges_new.push(challenge_new);
            challenges_new_inv.push(challenge_new_inv);
        }

        // Check b
        {
            let expected_b = self
                .compute_b(&mut cs, z3.clone(), &challenges_new, &challenges_new_inv)?
                .evaluate(&mut cs)?;

            {
                let lc1 = expected_b.lc(&mut cs);
                let lc2 = b.lc(&mut cs);

                cs.enforce_zero(lc1 - &lc2);
            }
        }

        // Witness openings

        let k_openings = [
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.k_openings[0])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.k_openings[1])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.k_openings[2])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.k_openings[3])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.k_openings[4])
                    .unwrap())
            })?,
        ];

        let r_openings = [
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.r_openings[0])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.r_openings[1])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.r_openings[2])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.r_openings[3])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.r_openings[4])
                    .unwrap())
            })?,
        ];

        let c_openings = [
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.c_openings[0])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.c_openings[1])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.c_openings[2])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.c_openings[3])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.c_openings[4])
                    .unwrap())
            })?,
        ];

        let t_positive_opening = Num::alloc(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .map(|proof| proof.remote_deferred.t_positive_opening)
                .unwrap())
        })?;

        let t_negative_opening = Num::alloc(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .map(|proof| proof.remote_deferred.t_negative_opening)
                .unwrap())
        })?;

        let p_openings = [
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.p_openings[0])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.p_openings[1])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.p_openings[2])
                    .unwrap())
            })?,
            Num::alloc(&mut cs, || {
                Ok(self
                    .proof
                    .as_ref()
                    .map(|proof| proof.remote_deferred.p_openings[3])
                    .unwrap())
            })?,
        ];

        let q_opening = Num::alloc(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .map(|proof| proof.remote_deferred.q_opening)
                .unwrap())
        })?;

        let g_opening = self
            .compute_b(&mut cs, x.clone(), &challenges_old, &challenges_old_inv)?
            .evaluate(&mut cs)?;

        // TODO: compute hash1/hash2/hash3
        let mut transcript = RescueGadget::new(&mut cs)?;
        let transcript = &mut transcript;

        for opening in k_openings.iter() {
            transcript.absorb(&mut cs, opening.clone())?;
        }

        for opening in r_openings.iter() {
            transcript.absorb(&mut cs, opening.clone())?;
        }

        for opening in c_openings.iter() {
            transcript.absorb(&mut cs, opening.clone())?;
        }

        transcript.absorb(&mut cs, t_positive_opening)?;
        transcript.absorb(&mut cs, t_negative_opening)?;

        let hash1_expected = Num::from(transcript.squeeze(&mut cs)?);

        {
            let lhs = hash1.lc(&mut cs);
            let rhs = hash1_expected.lc(&mut cs);
            cs.enforce_zero(lhs - &rhs);
        }

        let mut transcript = RescueGadget::new(&mut cs)?;
        let transcript = &mut transcript;

        for opening in p_openings.iter() {
            transcript.absorb(&mut cs, opening.clone())?;
        }

        let hash2_expected = Num::from(transcript.squeeze(&mut cs)?);

        {
            let lhs = hash2.lc(&mut cs);
            let rhs = hash2_expected.lc(&mut cs);
            cs.enforce_zero(lhs - &rhs);
        }

        let mut transcript = RescueGadget::new(&mut cs)?;
        let transcript = &mut transcript;

        transcript.absorb(&mut cs, q_opening.clone())?;

        let hash3_expected = Num::from(transcript.squeeze(&mut cs)?);

        {
            let lhs = hash3.lc(&mut cs);
            let rhs = hash3_expected.lc(&mut cs);
            cs.enforce_zero(lhs - &rhs);
        }

        // Check circuit
        let xinv = x.invert(&mut cs)?;
        let yinv = y_cur.invert(&mut cs)?;
        let xyinv = xinv.mul(&mut cs, &yinv)?;
        let xy_cur = x.mul(&mut cs, &y_cur)?;
        let x_invy = x.mul(&mut cs, &yinv)?;

        let nk = self.params.k - 2;

        let mut xinvn = xinv.clone();
        for i in 0..nk {
            xinvn = xinvn.mul(&mut cs, &xinvn)?;
        }
        // let xinvd = xinvn.square().square();
        let mut xinvd = xinvn.clone();
        for i in 0..2 {
            xinvd = xinvd.mul(&mut cs, &xinvd)?;
        }
        // let yn = self.y_cur.pow(&[n as u64, 0, 0, 0]);
        let mut yn = y_cur.clone();
        for i in 0..nk {
            yn = yn.mul(&mut cs, &yn)?;
        }
        // let xn = self.x.pow(&[n as u64, 0, 0, 0]);
        let mut xn = x.clone();
        for i in 0..nk {
            xn = xn.mul(&mut cs, &xn)?;
        }
        // let xyinvn31 = xyinv.pow(&[(3 * n - 1) as u64, 0, 0, 0]);
        let mut xyinvn31 = xyinv.clone();
        for i in 0..nk {
            xyinvn31 = xyinvn31.mul(&mut cs, &xyinvn31)?;
        }
        {
            let tmp = xyinvn31.mul(&mut cs, &xyinvn31)?;
            xyinvn31 = xyinvn31.mul(&mut cs, &tmp)?;
        }
        xyinvn31 = xyinvn31.mul(&mut cs, &xy_cur)?;
        // let xinvn31 = (xinvn.square() * &xinvn) * &self.x;
        let xinvn31 = xinvn.mul(&mut cs, &xinvn)?;
        let xinvn31 = xinvn31.mul(&mut cs, &xinvn)?;
        let xinvn31 = xinvn31.mul(&mut cs, &x)?;

        // println!("circuit xyinvn31: {:?}", xyinvn31);
        // println!("circuit xinvn31: {:?}", xinvn31);

        let rhs = t_positive_opening.mul(&mut cs, &x)?;
        let tmp = t_negative_opening.mul(&mut cs, &xinvd)?;
        let rhs = Combination::from(rhs) + tmp;

        let lhs = c_openings[3].mul(&mut cs, &xinvn)?;
        let lhs = lhs.mul(&mut cs, &yn)?;

        // Computes x + x^2 + x^3 + ... + x^n
        fn compute_thing<F: Field, CS: ConstraintSystem<F>>(
            mut cs: CS,
            x: Num<F>,
            k: usize,
        ) -> Result<Combination<F>, SynthesisError> {
            let mut acc = Combination::from(x);
            let mut cur = x.clone();
            for _ in 0..k {
                let tmp = acc.mul(&mut cs, &Combination::from(cur))?;
                cur = cur.mul(&mut cs, &cur)?;

                acc = acc + tmp;
            }
            Ok(acc)
        }

        let thing = compute_thing(&mut cs, xy_cur, nk)?;
        let thing = thing + compute_thing(&mut cs, x_invy, nk)?;
        let thing = thing.mul(&mut cs, &Combination::from(xn))?;
        /*
        let lhs = lhs - &thing;
        let lhs = lhs + &(self.rxy_opening * &xyinvn31);
        let lhs = lhs * &(self.rx_opening * &xinvn31);
        let ky = self.ky_opening * &yn;
        let lhs = lhs - &ky;
        */

        let tmp = r_openings[1].mul(&mut cs, &xyinvn31)?;
        let lhs = Combination::from(lhs);
        let lhs = lhs + tmp;
        let lhs = lhs - thing;
        let tmp = r_openings[0].mul(&mut cs, &xinvn31)?;
        let lhs = lhs.mul(&mut cs, &Combination::from(tmp))?;
        let ky = k_openings[3].mul(&mut cs, &yn)?;
        let lhs = Combination::from(lhs) + (Coeff::NegativeOne, ky);

        let lhs = lhs.lc(&mut cs);
        let rhs = rhs.lc(&mut cs);
        cs.enforce_zero(lhs - &rhs);

        let p_opening = Combination::from(c_openings[2]);
        let p_opening = Combination::from(p_opening.mul(&mut cs, &Combination::from(z1.clone()))?)
            + (Coeff::One, c_openings[3]);
        let p_opening = Combination::from(p_opening.mul(&mut cs, &Combination::from(z1.clone()))?)
            + (Coeff::One, t_positive_opening);
        let p_opening = Combination::from(p_opening.mul(&mut cs, &Combination::from(z1.clone()))?)
            + (Coeff::One, t_negative_opening);
        let p_opening = Combination::from(p_opening.mul(&mut cs, &Combination::from(z1.clone()))?)
            + (Coeff::One, c_openings[4]);
        let p_opening = Combination::from(p_opening.mul(&mut cs, &Combination::from(z1.clone()))?)
            + (Coeff::One, g_opening);
        let p_opening = Num::from(p_opening.evaluate(&mut cs)?);

        let p_openings = [
            p_opening,
            p_openings[0].clone(),
            p_openings[1].clone(),
            p_openings[2].clone(),
            p_openings[3].clone(),
        ];

        let mut t = Combination::zero();
        for (j, p) in [&x, &xy_cur, &y_old, &y_cur, &y_new].iter().enumerate() {
            let mut basis_num = AllocatedNum::one(&mut cs);
            let mut basis_den = AllocatedNum::one(&mut cs);

            for (m, q) in [&x, &xy_cur, &y_old, &y_cur, &y_new].iter().enumerate() {
                if j != m {
                    basis_num = Combination::from(basis_num).mul(
                        &mut cs,
                        &(Combination::from(z3) + (Coeff::NegativeOne, (*q).clone())),
                    )?;
                    basis_den = Combination::from(basis_den).mul(
                        &mut cs,
                        &(Combination::from((*p).clone()) + (Coeff::NegativeOne, (*q).clone())),
                    )?;
                }
            }

            let value = r_openings[j].mul(&mut cs, &z2)?;
            let value = Combination::from(value) + (Coeff::One, p_openings[j]);
            let value = value.mul(&mut cs, &Combination::from(z2))?;
            let value = Combination::from(value) + (Coeff::One, k_openings[j]);
            let value = value.mul(&mut cs, &Combination::from(z2))?;
            let value = Combination::from(value) + (Coeff::One, c_openings[j]);

            let basis_den = basis_den.invert(&mut cs)?;
            let basis = basis_num.mul(&mut cs, &basis_den)?;
            let product = value.mul(&mut cs, &Combination::from(basis))?;
            t = t + (Coeff::One, product);
        }
        let t = t.evaluate(&mut cs)?;

        let denom =
            Combination::zero() + (Coeff::One, z3.clone()) + (Coeff::NegativeOne, x.clone());
        let denom = Combination::from(denom.mul(
            &mut cs,
            &(Combination::zero()
                + (Coeff::One, z3.clone())
                + (Coeff::NegativeOne, xy_cur.clone())),
        )?);
        let denom = Combination::from(denom.mul(
            &mut cs,
            &(Combination::zero() + (Coeff::One, z3.clone()) + (Coeff::NegativeOne, y_old.clone())),
        )?);
        let denom = Combination::from(denom.mul(
            &mut cs,
            &(Combination::zero() + (Coeff::One, z3.clone()) + (Coeff::NegativeOne, y_cur.clone())),
        )?);
        let denom = Combination::from(denom.mul(
            &mut cs,
            &(Combination::zero() + (Coeff::One, z3.clone()) + (Coeff::NegativeOne, y_new.clone())),
        )?);
        let denom = Combination::from(denom.evaluate(&mut cs)?.invert(&mut cs)?);

        let f_opening_expected = q_opening.mul(&mut cs, &z4.clone())?;
        let f_opening_expected = Combination::from(f_opening_expected)
            + ((Combination::from(q_opening) + (Coeff::NegativeOne, t)).mul(&mut cs, &denom)?);

        let lhs = f_opening.lc(&mut cs);
        let rhs = f_opening_expected.lc(&mut cs);
        cs.enforce_zero(lhs - &rhs);

        Ok(())
    }

    fn compute_b<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        mut x: Num<E1::Scalar>,
        challenges: &[Num<E1::Scalar>],
        challenges_inv: &[Num<E1::Scalar>],
    ) -> Result<Combination<E1::Scalar>, SynthesisError> {
        let mut prod = Combination::zero() + (Coeff::One, Num::from(AllocatedNum::one(&mut cs)));
        for (challenge, challenge_inv) in challenges.iter().rev().zip(challenges_inv.iter().rev()) {
            let tmp = Combination::from(challenge.clone());
            let tmp = tmp.mul(&mut cs, &Combination::from(x.clone()))?;
            let tmp = Combination::from(tmp) + (Coeff::One, challenge_inv.clone());
            prod = Combination::from(tmp.mul(&mut cs, &prod)?);
            x = Num::from(Combination::from(x).square(&mut cs)?);
        }
        Ok(prod)
        /*
        assert!(!challenges.is_empty());
        assert_eq!(challenges.len(), challenges_inv.len());
        if challenges.len() == 1 {
            let challenge_inv = challenges_inv.last().unwrap().clone();
            let challenge = challenges.last().unwrap().clone();

            let tmp = Combination::from(challenge);
            let tmp = tmp.mul(&mut cs, &Combination::from(x.clone()))?;
            let tmp = Combination::from(tmp) + (Coeff::One, challenge_inv);

            Ok(tmp)
        } else {
            let challenge_inv = challenges_inv.last().unwrap().clone();
            let challenge = challenges.last().unwrap().clone();

            let tmp = Combination::from(challenge);
            let tmp = tmp.mul(&mut cs, &Combination::from(x.clone()))?;
            let tmp = Combination::from(tmp) + (Coeff::One, challenge_inv);

            let x2 = Num::from(Combination::from(x.clone()).square(&mut cs)?);

            let sub = self.compute_b(
                &mut cs,
                &x2,
                &challenges[0..(challenges.len() - 1)],
                &challenges_inv[0..(challenges.len() - 1)],
            )?;

            Ok(Combination::from(tmp.mul(&mut cs, &sub)?))
        }
        */
    }

    fn compute_k<'b, I, CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        mut bits: I,
    ) -> Result<(Num<E1::Scalar>, Num<E1::Scalar>), SynthesisError>
    where
        I: Iterator<Item = &'b AllocatedBit>,
    {
        let acc_point = self.params.generators[1].get_xy().unwrap();

        let mut x_coordinate_iter = self.params.pedersen_windows.iter();
        let mut y_coordinate_iter = self.params.pedersen_windows.iter();

        let mut x1 = Num::constant(acc_point.0);
        let mut y1 = Num::constant(acc_point.1);

        loop {
            if let Some(a) = bits.next() {
                let b = bits.next().unwrap();
                let c = bits.next().unwrap();
                let d = bits.next().unwrap();

                let x_coordinates = x_coordinate_iter.next().unwrap();
                let y_coordinates = y_coordinate_iter.next().unwrap();

                let mut x_coeffs = [E1::Scalar::zero(); 4];
                let mut y_coeffs = [E1::Scalar::zero(); 4];
                synth(2, x_coordinates.iter().map(|a| a.0), &mut x_coeffs);
                synth(2, y_coordinates.iter().map(|a| a.1), &mut y_coeffs);

                let ab = AllocatedBit::and(&mut cs, a, b)?;

                let x_lc = Combination::zero()
                    + (
                        Coeff::Full(x_coeffs[0]),
                        Num::from(AllocatedNum::one(&mut cs)),
                    )
                    + (
                        Coeff::Full(x_coeffs[1]),
                        Num::from(AllocatedNum::from(a.clone())),
                    )
                    + (
                        Coeff::Full(x_coeffs[2]),
                        Num::from(AllocatedNum::from(b.clone())),
                    )
                    + (
                        Coeff::Full(x_coeffs[3]),
                        Num::from(AllocatedNum::from(ab.clone())),
                    );

                let y_lc = Combination::zero()
                    + (
                        Coeff::Full(y_coeffs[0]),
                        Num::from(AllocatedNum::one(&mut cs)),
                    )
                    + (
                        Coeff::Full(y_coeffs[1]),
                        Num::from(AllocatedNum::from(a.clone())),
                    )
                    + (
                        Coeff::Full(y_coeffs[2]),
                        Num::from(AllocatedNum::from(b.clone())),
                    )
                    + (Coeff::Full(y_coeffs[3]), Num::from(AllocatedNum::from(ab)));

                let x2 = x_lc.conditional_multiply(&mut cs, &d, E1::Scalar::ZETA)?;
                let y2 = y_lc.conditional_multiply(&mut cs, &c, -E1::Scalar::one())?;

                let y1_neg = (Coeff::NegativeOne, y1);
                let lambda =
                    (y2 + y1_neg.clone()).div(&mut cs, &(x2.clone() + (Coeff::NegativeOne, x1)))?;
                let lambda2 = Combination::from(Num::from(lambda)).square(&mut cs)?;
                let x3 = Combination::from(lambda2)
                    + (Coeff::NegativeOne, x1)
                    + x2.scale(-E1::Scalar::one());
                let x3 = x3.evaluate(&mut cs)?;
                let y3 = (Combination::from(Combination::from(lambda).mul(
                    &mut cs,
                    &(Combination::zero() + (Coeff::One, x1) + (Coeff::NegativeOne, x3)),
                )?) + (y1_neg))
                    .evaluate(&mut cs)?;
                x1 = x3;
                y1 = y3;
            } else {
                break;
            }
        }

        Ok((x1, y1))
    }

    fn num_equal_unless_base_case<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        base_case: &AllocatedBit,
        lhs: &Combination<E1::Scalar>,
        rhs: &Combination<E1::Scalar>,
    ) -> Result<(), SynthesisError> {
        let not_basecase = base_case.get_value().map(|v| (!v).into());

        // lhs - rhs * (1 - base_case) = 0
        // if base_case is true, then 1 - base_case will be zero
        // if base_case is false, then lhs - rhs must be zero, and therefore they are equal
        let (a, b, c) = cs.multiply(|| {
            let lhs = lhs.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let rhs = rhs.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let not_basecase = not_basecase.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((lhs - &rhs, not_basecase, Field::zero()))
        })?;
        let lhs_lc = lhs.lc(&mut cs);
        let rhs_lc = rhs.lc(&mut cs);
        cs.enforce_zero(LinearCombination::from(a) - &lhs_lc + &rhs_lc);
        cs.enforce_zero(LinearCombination::from(b) - CS::ONE + base_case.get_variable());
        cs.enforce_zero(LinearCombination::from(c));

        Ok(())
    }

    fn equal_unless_base_case<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        base_case: &AllocatedBit,
        mut lhs: &[AllocatedBit],
        mut rhs: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        assert_eq!(lhs.len(), rhs.len());

        let mut i = 0;
        while lhs.len() > 0 {
            i += 1;
            let mut coeff = E1::Scalar::one();
            let mut lhs_lc = Combination::zero();
            let mut rhs_lc = Combination::zero();

            let mut truncate_by = 0;
            for (i, (lhs, rhs)) in lhs.iter().zip(rhs.iter()).take(250).enumerate() {
                lhs_lc = lhs_lc
                    + (
                        Coeff::Full(coeff),
                        Num::from(AllocatedNum::from(lhs.clone())),
                    );
                rhs_lc = rhs_lc
                    + (
                        Coeff::Full(coeff),
                        Num::from(AllocatedNum::from(rhs.clone())),
                    );

                coeff = coeff + &coeff;
                truncate_by = i + 1;
            }

            self.num_equal_unless_base_case(&mut cs, base_case, &lhs_lc, &rhs_lc)?;

            lhs = &lhs[truncate_by..];
            rhs = &rhs[truncate_by..];
        }

        Ok(())
    }

    fn check_proof<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        base_case: &AllocatedBit,
        k_commitment: (Num<E1::Scalar>, Num<E1::Scalar>),
        mut old_amortized: &[AllocatedBit],
        mut new_amortized: &[AllocatedBit],
        mut deferred: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        // Parse old amortized

        let y_old = &old_amortized[0..128];
        old_amortized = &old_amortized[128..];

        let mut old_challenges = vec![];
        for _ in 0..self.params.k {
            old_challenges.push(&old_amortized[0..128]);
            old_amortized = &old_amortized[128..];
        }

        let g_old_x = self.get_scalar(&mut cs, &old_amortized[0..256])?;
        old_amortized = &old_amortized[256..];
        let g_old_y = self.get_scalar(&mut cs, &old_amortized[0..256])?;
        old_amortized = &old_amortized[256..];

        let g_old_commitment = (g_old_x, g_old_y);
        self.check_on_curve(&mut cs, &g_old_commitment.0, &g_old_commitment.1)?;

        let s_old_x = self.get_scalar(&mut cs, &old_amortized[0..256])?;
        old_amortized = &old_amortized[256..];
        let s_old_y = self.get_scalar(&mut cs, &old_amortized[0..256])?;
        old_amortized = &old_amortized[256..];

        let s_old_commitment = (s_old_x, s_old_y);
        self.check_on_curve(&mut cs, &s_old_commitment.0, &s_old_commitment.1)?;

        assert_eq!(old_amortized.len(), 0);

        // Parse new amortized

        let y_new_expected = &new_amortized[0..128];
        new_amortized = &new_amortized[128..];

        let mut new_challenges_expected = vec![];
        for _ in 0..self.params.k {
            new_challenges_expected.push(&new_amortized[0..128]);
            new_amortized = &new_amortized[128..];
        }

        let g_new_x = self.get_scalar(&mut cs, &new_amortized[0..256])?;
        new_amortized = &new_amortized[256..];
        let g_new_y = self.get_scalar(&mut cs, &new_amortized[0..256])?;
        new_amortized = &new_amortized[256..];

        let g_new_commitment = (g_new_x, g_new_y);
        self.check_on_curve(&mut cs, &g_new_commitment.0, &g_new_commitment.1)?;

        let s_new_x = self.get_scalar(&mut cs, &new_amortized[0..256])?;
        new_amortized = &new_amortized[256..];
        let s_new_y = self.get_scalar(&mut cs, &new_amortized[0..256])?;
        new_amortized = &new_amortized[256..];

        let s_new_commitment = (s_new_x, s_new_y);
        self.check_on_curve(&mut cs, &s_new_commitment.0, &s_new_commitment.1)?;

        assert_eq!(new_amortized.len(), 0);

        // Parse deferred

        let y_old_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let y_cur_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let x_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let z1_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let z2_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let z3_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let z4_expected = &deferred[0..128];
        deferred = &deferred[128..];

        let mut old_challenges_expected = vec![];
        for _ in 0..self.params.k {
            old_challenges_expected.push(&deferred[0..128]);
            deferred = &deferred[128..];
        }

        let hash1 = self.get_scalar(&mut cs, &deferred[0..256])?;
        deferred = &deferred[256..];

        let hash2 = self.get_scalar(&mut cs, &deferred[0..256])?;
        deferred = &deferred[256..];

        let hash3 = self.get_scalar(&mut cs, &deferred[0..256])?;
        deferred = &deferred[256..];

        let f_opening = &deferred[0..256];
        deferred = &deferred[256..];

        let b = &deferred[0..256];
        deferred = &deferred[256..];

        assert_eq!(deferred.len(), 0);

        // Start the transcript...
        let mut transcript = RescueGadget::new(&mut cs)?;
        let transcript = &mut transcript;

        self.append_point(&mut cs, transcript, &k_commitment)?;

        let r_commitment = self.witness_point(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .unwrap()
                .proof
                .r_commitment
                .get_xy()
                .unwrap())
        })?;
        self.append_point(&mut cs, transcript, &r_commitment)?;

        let y_cur = self.obtain_challenge(&mut cs, transcript)?;

        let s_cur_commitment = self.witness_point(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .unwrap()
                .proof
                .s_cur_commitment
                .get_xy()
                .unwrap())
        })?;
        self.append_point(&mut cs, transcript, &s_cur_commitment)?;

        let t_positive_commitment = self.witness_point(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .unwrap()
                .proof
                .t_positive_commitment
                .get_xy()
                .unwrap())
        })?;
        self.append_point(&mut cs, transcript, &t_positive_commitment)?;

        let t_negative_commitment = self.witness_point(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .unwrap()
                .proof
                .t_negative_commitment
                .get_xy()
                .unwrap())
        })?;
        self.append_point(&mut cs, transcript, &t_negative_commitment)?;

        let x = self.obtain_challenge(&mut cs, transcript)?;

        let c_commitment = self.witness_point(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .unwrap()
                .proof
                .c_commitment
                .get_xy()
                .unwrap())
        })?;
        self.append_point(&mut cs, transcript, &c_commitment)?;

        let y_new = self.obtain_challenge(&mut cs, transcript)?;

        self.append_point(&mut cs, transcript, &s_new_commitment)?;

        transcript.absorb(&mut cs, hash1)?;

        let z1 = self.obtain_challenge(&mut cs, transcript)?;

        transcript.absorb(&mut cs, hash2)?;

        let z2 = self.obtain_challenge(&mut cs, transcript)?;

        let h_commitment = self.witness_point(&mut cs, || {
            Ok(self
                .proof
                .as_ref()
                .unwrap()
                .proof
                .h_commitment
                .get_xy()
                .unwrap())
        })?;
        self.append_point(&mut cs, transcript, &h_commitment)?;

        let z3 = self.obtain_challenge(&mut cs, transcript)?;

        transcript.absorb(&mut cs, hash3)?;

        let z4 = self.obtain_challenge(&mut cs, transcript)?;

        // Check consistency of challenges
        self.equal_unless_base_case(&mut cs, base_case, &y_old, &y_old_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &y_cur, &y_cur_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &x, &x_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &y_new, &y_new_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &z1, &z1_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &z2, &z2_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &z3, &z3_expected)?;
        self.equal_unless_base_case(&mut cs, base_case, &z4, &z4_expected)?;
        for (old, expected) in old_challenges.iter().zip(old_challenges_expected.iter()) {
            self.equal_unless_base_case(&mut cs, base_case, old, expected)?;
        }
        // new_challenges_expected

        Ok(())
    }

    fn obtain_challenge<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        transcript: &mut RescueGadget<E1::Scalar>,
    ) -> Result<Vec<AllocatedBit>, SynthesisError> {
        let num = Num::from(transcript.squeeze(&mut cs)?);
        let mut bits = unpack_fe(&mut cs, &num)?;
        bits.truncate(128);
        Ok(bits)
    }

    fn append_point<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        transcript: &mut RescueGadget<E1::Scalar>,
        p: &(Num<E1::Scalar>, Num<E1::Scalar>),
    ) -> Result<(), SynthesisError> {
        transcript.absorb(&mut cs, p.0.clone())?;
        transcript.absorb(&mut cs, p.1.clone())
    }

    fn witness_point<P, CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        p: P,
    ) -> Result<(Num<E1::Scalar>, Num<E1::Scalar>), SynthesisError>
    where
        P: FnOnce() -> Result<(E1::Scalar, E1::Scalar), SynthesisError>,
    {
        let mut y = None;

        let x = AllocatedNum::alloc(&mut cs, || {
            let p = p()?;
            y = Some(p.1);

            Ok(p.0)
        })?;
        let x = Num::from(x);

        let y = AllocatedNum::alloc(&mut cs, || Ok(y.unwrap()))?;
        let y = Num::from(y);

        self.check_on_curve(&mut cs, &x, &y)?;

        Ok((x, y))
    }

    fn check_on_curve<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        x: &Num<E1::Scalar>,
        y: &Num<E1::Scalar>,
    ) -> Result<(), SynthesisError> {
        // y^2 = x^3 + 5
        let y2 = y.mul(&mut cs, y)?;
        let x2 = x.mul(&mut cs, x)?;
        let x3 = x.mul(&mut cs, &x2)?;

        let lc = Combination::from(y2)
            + (Coeff::NegativeOne, x3)
            + (Coeff::One, Num::constant(-E1::Scalar::from_u64(5)));
        let lc = lc.lc(&mut cs);

        cs.enforce_zero(lc);

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
        // Compute public input bytes
        let mut public_input_bytes = self
            .local_amortized
            .as_ref()
            .map(|l| l.public_input_string())
            .unwrap_or(vec![
                0u8;
                Amortized::<E1>::public_input_string_length(
                    self.params.k
                )
            ]);

        public_input_bytes.extend(
            self.remote_amortized
                .as_ref()
                .map(|l| l.public_input_string())
                .unwrap_or(vec![
                    0u8;
                    Amortized::<E2>::public_input_string_length(
                        self.params.k
                    )
                ]),
        );

        public_input_bytes.extend(
            self.remote_deferred
                .as_ref()
                .map(|l| l.public_input_string())
                .unwrap_or(vec![
                    0u8;
                    Deferred::<E2::Scalar>::public_input_string_length(
                        self.params.k
                    )
                ]),
        );

        // Allocate bits for public inputs
        let mut input_bits = Vec::with_capacity(public_input_bytes.len() * 8);
        for byte in public_input_bytes {
            for i in 0..8 {
                let bit_value = ((byte >> i) & 1) == 1;
                input_bits.push(AllocatedBit::alloc_unchecked(&mut *cs, || Ok(bit_value))?);
            }
        }

        // Pack into inputs
        self.inputify(cs, &input_bits)?;

        // Boolean constrain the bits
        for bit in &input_bits {
            bit.check(&mut *cs)?;
        }

        let input_bits = &input_bits[..];
        let new_proof_local_amortized =
            &input_bits[0..Amortized::<E1>::public_input_string_length(self.params.k) * 8];
        let input_bits = &input_bits[new_proof_local_amortized.len()..];
        let new_proof_remote_amortized =
            &input_bits[0..Amortized::<E1>::public_input_string_length(self.params.k) * 8];
        let input_bits = &input_bits[new_proof_remote_amortized.len()..];
        let new_proof_remote_deferred =
            &input_bits[0..Deferred::<E2::Scalar>::public_input_string_length(self.params.k) * 8];
        let input_bits = &input_bits[new_proof_remote_deferred.len()..];
        assert_eq!(input_bits.len(), 0);

        // Proof inputs consist of:
        // proof's local_amortized
        // proof's remote_amortized, which is equal to our local_amortized
        // proof's remote_deferred

        let inner_proof_local_amortized = {
            let bytes = self
                .proof
                .as_ref()
                .map(|proof| proof.local_amortized.public_input_string())
                .unwrap_or(vec![
                    0u8;
                    Amortized::<E2>::public_input_string_length(
                        self.params.k
                    )
                ]);

            let mut inner_proof_local_amortized = Vec::with_capacity(bytes.len() * 8);
            for byte in bytes {
                for i in 0..8 {
                    let bit_value = ((byte >> i) & 1) == 1;
                    inner_proof_local_amortized
                        .push(AllocatedBit::alloc(&mut *cs, || Ok(bit_value))?);
                }
            }

            inner_proof_local_amortized
        };

        let inner_proof_remote_deferred = {
            let bytes = self
                .proof
                .as_ref()
                .map(|proof| proof.remote_deferred.public_input_string())
                .unwrap_or(vec![
                    0u8;
                    Deferred::<E2::Scalar>::public_input_string_length(
                        self.params.k
                    )
                ]);

            let mut inner_proof_remote_deferred = Vec::with_capacity(bytes.len() * 8);
            for byte in bytes {
                for i in 0..8 {
                    let bit_value = ((byte >> i) & 1) == 1;
                    inner_proof_remote_deferred
                        .push(AllocatedBit::alloc(&mut *cs, || Ok(bit_value))?);
                }
            }

            inner_proof_remote_deferred
        };

        let base_case = AllocatedBit::alloc(&mut *cs, || {
            self.base_case.ok_or(SynthesisError::AssignmentMissing)
        })?;

        self.check_deferred(
            &mut *cs,
            &inner_proof_remote_deferred,
            &new_proof_local_amortized,
        )?;

        // Compute K commitment for inner proof
        let k = self.compute_k(
            &mut *cs,
            inner_proof_local_amortized
                .iter()
                .chain(new_proof_local_amortized.iter())
                .chain(inner_proof_remote_deferred.iter()),
        )?;

        self.check_proof(
            &mut *cs,
            &base_case,
            k,
            &inner_proof_local_amortized,
            &new_proof_remote_amortized,
            &new_proof_remote_deferred,
        )?;

        self.inner_circuit.synthesize(cs)
    }
}

#[test]
fn recursion_threshold() {
    use crate::curves::*;
    use crate::fields::*;

    let e1params = Params::<EpAffine>::new(19);
    let e2params = Params::<EqAffine>::new(19);

    struct CubingCircuit {
        x: Option<u64>,
        num_cubes: usize,
    }

    impl<F: Field> Circuit<F> for CubingCircuit {
        fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            /*
            let initial_x = self.x.map(|x| F::from_u64(x as u64));

            let mut x2value = None;
            let (x, _, x2) = cs.multiply(|| {
                let x = initial_x.ok_or(SynthesisError::AssignmentMissing)?;
                let x2 = x.square();

                x2value = Some(x2);

                Ok((x, x, x2))
            })?;
            let mut x3value = None;
            let (a, b, c) = cs.multiply(|| {
                let x = initial_x.ok_or(SynthesisError::AssignmentMissing)?;
                let x2 = x2value.ok_or(SynthesisError::AssignmentMissing)?;
                //let x3 = -(x * x2);
                let x3 = x * x2;

                x3value = Some(x3);

                Ok((x, x2, x3))
            })?;

            cs.enforce_zero(LinearCombination::from(x) - a);
            cs.enforce_zero(LinearCombination::from(x2) - b);

            let x3 = cs.alloc(|| x3value.ok_or(SynthesisError::AssignmentMissing))?;

            cs.enforce_zero(LinearCombination::from(x3) - c);

            for _ in 0..self.num_cubes {
                let mut x2value = None;
                let (x, _, x2) = cs.multiply(|| {
                    let x = initial_x.ok_or(SynthesisError::AssignmentMissing)?;
                    let x2 = x.square();

                    x2value = Some(x2);

                    Ok((x, x, x2))
                })?;
                let mut x3value = None;
                let (a, b, c) = cs.multiply(|| {
                    let x = initial_x.ok_or(SynthesisError::AssignmentMissing)?;
                    let x2 = x2value.ok_or(SynthesisError::AssignmentMissing)?;
                    //let x3 = -(x * x2);
                    let x3 = x * x2;

                    x3value = Some(x3);

                    Ok((x, x2, x3))
                })?;

                cs.enforce_zero(LinearCombination::from(x) - a);
                cs.enforce_zero(LinearCombination::from(x2) - b);
                cs.enforce_zero(LinearCombination::from(x3) - c);
            }
            */

            Ok(())
        }
    }

    let circuit = CubingCircuit {
        x: Some(10),
        num_cubes: 65000,
    };

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
