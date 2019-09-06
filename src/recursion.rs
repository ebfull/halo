use super::circuits::*;
use super::gadgets::*;
use super::proofs::*;
use super::synthesis::Basic;
use super::{Curve, Field};
use std::marker::PhantomData;

#[derive(Clone)]
pub struct RecursiveProof<E1: Curve, E2: Curve> {
    proof: Proof<E1>,
    oldproof1: Leftovers<E1>,
    oldproof2: Leftovers<E2>,
    deferred: Deferred<E2::Scalar>,
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
        let (newdeferred, new_leftovers, old_leftovers) = match old_proof {
            Some(old_proof) => {
                let (_, newdeferred, l1, l2) =
                    old_proof.verify_inner(e2params, e1params, circuit)?;

                (newdeferred, l1, l2)
            }
            None => (
                Deferred::dummy(e2params.k),
                Leftovers::dummy(e2params),
                Leftovers::dummy(e1params),
            ),
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
            deferred: Some(newdeferred.clone()),
        };

        if old_proof.is_some() {
            circuit.base_case = Some(false);
            circuit.proof = old_proof;
        } else {
            circuit.base_case = Some(true);
        }

        {
            let mut inputs = vec![];
            inputs.extend(new_payload.iter().cloned());
            inputs.extend(old_leftovers.to_bytes());
            inputs.extend(new_leftovers.to_bytes());
            inputs.extend(newdeferred.to_bytes());

            let mut realinputs = vec![];
            for byte in inputs {
                for i in 0..8 {
                    let bit = ((byte >> i) & 1) == 1;
                    if bit {
                        realinputs.push(Field::one());
                    } else {
                        realinputs.push(Field::zero());
                    }
                }
            }

            assert!(is_satisfied::<_, _, Basic>(&circuit, &realinputs)?);
        }

        // Now make the proof...
        let (proof, _) = Proof::new::<_, Basic>(e1params, &circuit, &old_leftovers)?;

        Ok(RecursiveProof {
            proof,
            oldproof1: old_leftovers,
            oldproof2: new_leftovers,
            deferred: newdeferred,
            payload: new_payload.to_vec(),
        })
    }

    fn verify_inner<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        &self,
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        circuit: &CS,
    ) -> Result<(bool, Deferred<E1::Scalar>, Leftovers<E1>, Leftovers<E2>), SynthesisError> {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: None,
            deferred: None,
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
            deferred: None,
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

        let mut k_commitment = e1params.generators[1];
        let mut iter_gens = e1params.generators[2..].iter();
        let mut bitinputs = vec![];
        for byte in inputs {
            for i in 0..8 {
                let b = ((byte >> i) & 1) == 1;
                if b {
                    bitinputs.push(E1::Scalar::one());
                    k_commitment = k_commitment + iter_gens.next().unwrap();
                } else {
                    iter_gens.next();
                    bitinputs.push(E1::Scalar::zero());
                }
            }
        }

        let (worked, leftovers, deferred) = self.proof.verify::<_, Basic>(
            &self.oldproof1,
            e1params,
            &circuit1,
            &bitinputs,
            Some(k_commitment),
        )?;

        let worked = worked & self.oldproof2.verify::<_, Basic>(e2params, &circuit2)?;

        Ok((worked, deferred, leftovers, self.oldproof2.clone()))
    }

    pub fn verify<CS: Circuit<E1::Scalar> + Circuit<E2::Scalar>>(
        &self,
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        circuit: &CS,
    ) -> Result<bool, SynthesisError> {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            old_leftovers: None,
            new_leftovers: None,
            deferred: None,
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
            deferred: None,
        };

        let (worked, deferred, a, b) = self.verify_inner(e1params, e2params, circuit)?;

        Ok(worked
            & self.deferred.verify(e2params.k)
            & deferred.verify(e1params.k)
            & a.verify::<_, Basic>(e1params, &circuit1)?
            & b.verify::<_, Basic>(e2params, &circuit2)?)
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
    deferred: Option<Deferred<C2::Scalar>>,
}

impl<'a, E1: Curve, E2: Curve<Base = E1::Scalar>, Inner: Circuit<E1::Scalar>>
    VerificationCircuit<'a, E1, E2, Inner>
{
    fn verify_deferred<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        mut deferred: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        // Unpack all of the deferred data
        /*
        x: F,
        y_old: F,
        y_cur: F,
        y_new: F,
        ky_opening: F,
        tx_positive_opening: F,
        tx_negative_opening: F,
        sx_cur_opening: F,
        rx_opening: F,
        rxy_opening: F,
        challenges_old: Vec<F>,
        gx_old_opening: F,
        challenges_new: Vec<F>,
        b_x: F,
        b_xy: F,
        b_y_old: F,
        b_y_cur: F,
        b_y_new: F,
        */

        let x = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let y_old = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let y_cur = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let y_new = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let ky_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let tx_positive_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let tx_negative_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let sx_cur_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let rx_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let rxy_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let mut challenges_old = vec![];
        for _ in 0..self.params.k {
            challenges_old.push(self.obtain_scalar_from_bits(cs, &deferred[0..256])?);
            deferred = &deferred[256..];
        }
        let gx_old_opening = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let mut challenges_new = vec![];
        for _ in 0..self.params.k {
            challenges_new.push(self.obtain_scalar_from_bits(cs, &deferred[0..256])?);
            deferred = &deferred[256..];
        }
        let b_x = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_xy = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_y_old = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_y_cur = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_y_new = self.obtain_scalar_from_bits(cs, &deferred[0..256])?;
        deferred = &deferred[256..];

        assert_eq!(deferred.len(), 0);

        // Check that the inner proof's circuit check was satisfied for it, since
        // we can do scalar arithmetic more efficiently in our base field! :)

        let xinv = x.invert(cs)?;
        let yinv = y_cur.invert(cs)?;
        let xyinv = xinv.mul(cs, &yinv)?;
        let xy = x.mul(cs, &y_cur)?;
        let x_invy = x.mul(cs, &yinv)?;

        let nk = self.params.k - 2;

        // let xinvn = xinv.pow(&[n as u64, 0, 0, 0]);
        let mut xinvn = xinv.clone();
        for _ in 0..nk {
            xinvn = xinvn.mul(cs, &xinvn)?;
        }
        // let xinvd = xinvn.square().square();
        let mut xinvd = xinvn.clone();
        for _ in 0..2 {
            xinvd = xinvd.mul(cs, &xinvd)?;
        }
        // let yn = self.y_cur.pow(&[n as u64, 0, 0, 0]);
        let mut yn = y_cur.clone();
        for _ in 0..nk {
            yn = yn.mul(cs, &yn)?;
        }
        // let xn = self.x.pow(&[n as u64, 0, 0, 0]);
        let mut xn = x.clone();
        for _ in 0..nk {
            xn = xn.mul(cs, &xn)?;
        }
        // let xyinvn31 = xyinv.pow(&[(3 * n - 1) as u64, 0, 0, 0]);
        let mut xyinvn31 = xyinv.clone();
        for _ in 0..nk {
            xyinvn31 = xyinvn31.mul(cs, &xyinvn31)?;
        }
        {
            let tmp = xyinvn31.mul(cs, &xyinvn31)?;
            xyinvn31 = xyinvn31.mul(cs, &tmp)?;
        }
        xyinvn31 = xyinvn31.mul(cs, &xy)?;
        // let xinvn31 = (xinvn.square() * &xinvn) * &self.x;
        let xinvn31 = xinvn.mul(cs, &xinvn)?;
        let xinvn31 = xinvn31.mul(cs, &xinvn)?;
        let xinvn31 = xinvn31.mul(cs, &x)?;

        // println!("circuit xyinvn31: {:?}", xyinvn31);
        // println!("circuit xinvn31: {:?}", xinvn31);

        let rhs = tx_positive_opening.mul(cs, &x)?;
        let tmp = tx_negative_opening.mul(cs, &xinvd)?;
        let rhs = Combination::from(rhs) + tmp;

        let lhs = sx_cur_opening.mul(cs, &xinvn)?;
        let lhs = lhs.mul(cs, &yn)?;

        // Computes x + x^2 + x^3 + ... + x^n
        fn compute_thing<F: Field, CS: ConstraintSystem<F>>(
            cs: &mut CS,
            x: AllocatedNum<F>,
            k: usize,
        ) -> Result<Combination<F>, SynthesisError> {
            let mut acc = Combination::from(x);
            let mut cur = x.clone();
            for _ in 0..k {
                let tmp = acc.mul(cs, &Combination::from(cur))?;
                cur = cur.mul(cs, &cur)?;

                acc = acc + tmp;
            }
            Ok(acc)
        }

        let thing = compute_thing(cs, xy, nk)?;
        let thing = thing + compute_thing(cs, x_invy, nk)?;
        let thing = thing.mul(cs, &Combination::from(xn))?;
        /*
        let lhs = lhs - &thing;
        let lhs = lhs + &(self.rxy_opening * &xyinvn31);
        let lhs = lhs * &(self.rx_opening * &xinvn31);
        let ky = self.ky_opening * &yn;
        let lhs = lhs - &ky;
        */

        let tmp = rxy_opening.mul(cs, &xyinvn31)?;
        let lhs = Combination::from(lhs);
        let lhs = lhs + tmp;
        let lhs = lhs - thing;
        let tmp = rx_opening.mul(cs, &xinvn31)?;
        let lhs = lhs.mul(cs, &Combination::from(tmp))?;
        let ky = ky_opening.mul(cs, &yn)?;
        let lhs = Combination::from(lhs) - ky;

        let lhs = lhs.lc(cs);
        let rhs = rhs.lc(cs);
        cs.enforce_zero(lhs - &rhs);

        // Check gx_old_opening
        {
            let mut challenges_old_inv = challenges_old.clone();
            for c in &mut challenges_old_inv {
                *c = c.invert(cs)?;
            }
            let expected_gx_old_opening =
                self.compute_b(cs, x, &challenges_old, &challenges_old_inv)?;

            let lc = expected_gx_old_opening.lc(cs);
            cs.enforce_zero(lc - gx_old_opening.get_variable());
        }

        // Check the other `b` entries
        let mut challenges_new_inv = challenges_new.clone();
        for c in &mut challenges_new_inv {
            *c = c.invert(cs)?;
        }
        let expected_b_x = self.compute_b(cs, x, &challenges_new, &challenges_new_inv)?;
        let expected_b_xy = self.compute_b(cs, xy, &challenges_new, &challenges_new_inv)?;
        let expected_b_y_old = self.compute_b(cs, y_old, &challenges_new, &challenges_new_inv)?;
        let expected_b_y_cur = self.compute_b(cs, y_cur, &challenges_new, &challenges_new_inv)?;
        let expected_b_y_new = self.compute_b(cs, y_new, &challenges_new, &challenges_new_inv)?;

        let lc = expected_b_x.lc(cs);
        cs.enforce_zero(lc - b_x.get_variable());

        let lc = expected_b_xy.lc(cs);
        cs.enforce_zero(lc - b_xy.get_variable());

        let lc = expected_b_y_old.lc(cs);
        cs.enforce_zero(lc - b_y_old.get_variable());

        let lc = expected_b_y_cur.lc(cs);
        cs.enforce_zero(lc - b_y_cur.get_variable());

        let lc = expected_b_y_new.lc(cs);
        cs.enforce_zero(lc - b_y_new.get_variable());

        Ok(())
    }

    fn compute_b<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        x: AllocatedNum<E1::Scalar>,
        challenges: &[AllocatedNum<E1::Scalar>],
        challenges_inv: &[AllocatedNum<E1::Scalar>],
    ) -> Result<Combination<E1::Scalar>, SynthesisError> {
        assert!(challenges.len() >= 1);
        assert_eq!(challenges.len(), challenges_inv.len());
        Ok(if challenges.len() == 1 {
            // return *challenges_inv.last().unwrap() + *challenges.last().unwrap() * x;
            let tmp = x.mul(cs, challenges.last().unwrap())?;
            Combination::from(*challenges_inv.last().unwrap()) + tmp
        } else {
            // return (*challenges_inv.last().unwrap() + *challenges.last().unwrap() * x)
            //     * compute_b(
            //         x.square(),
            //         &challenges[0..(challenges.len() - 1)],
            //         &challenges_inv[0..(challenges.len() - 1)],
            //     );

            let tmp = x.mul(cs, challenges.last().unwrap())?;
            let tmp = Combination::from(*challenges_inv.last().unwrap()) + tmp;
            let x2 = x.mul(cs, &x)?;

            Combination::from(
                self.compute_b(
                    cs,
                    x2,
                    &challenges[0..(challenges.len() - 1)],
                    &challenges_inv[0..(challenges.len() - 1)],
                )?
                .mul(cs, &tmp)?,
            )
        })
    }

    fn obtain_scalar_from_bits<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        bits: &[AllocatedBit],
    ) -> Result<AllocatedNum<E1::Scalar>, SynthesisError> {
        assert_eq!(bits.len(), 256);

        let mut value = Some(E1::Scalar::zero());
        let mut cur = E1::Scalar::one();
        let mut lc = LinearCombination::zero();
        for bit in bits {
            if let Some(bit) = bit.get_value() {
                if bit {
                    value = value.map(|value| value + &cur);
                }
            }
            lc = lc + (Coeff::Full(cur), bit.get_variable());
            cur = cur + &cur;
        }

        let newnum = AllocatedNum::alloc(cs, || value.ok_or(SynthesisError::AssignmentMissing))?;

        cs.enforce_zero(lc - newnum.get_variable());

        Ok(newnum)
    }

    fn verify_proof<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        k_commitment: &CurvePoint<E2>,
    ) -> Result<(), SynthesisError> {
        let mut transcript = RescueGadget::new(cs)?;
        let transcript = &mut transcript;

        self.commit_point(cs, transcript, &k_commitment)?;

        let r_commitment = CurvePoint::witness(cs, || {
            Ok(self
                .proof
                .map(|proof| proof.proof.r_commitment)
                .unwrap_or(E2::zero()))
        })?;
        self.commit_point(cs, transcript, &r_commitment)?;

        let y_cur = self.get_challenge(cs, transcript)?;

        let s_cur_commitment = CurvePoint::witness_test(cs, || {
            Ok(self
                .proof
                .map(|proof| proof.proof.s_cur_commitment)
                .unwrap_or(E2::zero()))
        })?;
        //self.commit_point(cs, transcript, &s_cur_commitment)?;
        /*
        let t_positive_commitment = CurvePoint::witness(cs, || {
            Ok(self.proof.map(|proof| proof.proof.t_positive_commitment).unwrap_or(E2::zero()))
        })?;
        self.commit_point(cs, transcript, &t_positive_commitment)?;
        let t_negative_commitment = CurvePoint::witness(cs, || {
            Ok(self.proof.map(|proof| proof.proof.t_negative_commitment).unwrap_or(E2::zero()))
        })?;
        self.commit_point(cs, transcript, &t_negative_commitment)?;

        let x = self.get_challenge(cs, transcript)?;

        let c_commitment = CurvePoint::witness(cs, || {
            Ok(self.proof.map(|proof| proof.proof.c_commitment).unwrap_or(E2::zero()))
        })?;
        self.commit_point(cs, transcript, &c_commitment)?;

        let y_new = self.get_challenge(cs, transcript)?;

        let s_new_commitment = CurvePoint::witness(cs, || {
            Ok(self.proof.map(|proof| proof.proof.s_new_commitment).unwrap_or(E2::zero()))
        })?;
        self.commit_point(cs, transcript, &s_new_commitment)?;

        println!("y_new in the circuit: {:?}", y_new);
        */

        Ok(())
    }

    fn commit_point<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        transcript: &mut RescueGadget<E1::Scalar>,
        point: &CurvePoint<E2>,
    ) -> Result<(), SynthesisError> {
        let (x, y) = point.get_xy(cs)?;
        transcript.absorb(cs, x)?;
        transcript.absorb(cs, y)?;

        Ok(())
    }

    fn get_challenge<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        transcript: &mut RescueGadget<E1::Scalar>,
    ) -> Result<Vec<AllocatedBit>, SynthesisError> {
        let num = transcript.squeeze(cs)?;
        let mut bits = unpack_fe(cs, &num)?;
        bits.truncate(128);

        Ok(bits)
    }
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
                payload_bits.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(bit))?);
            }
        }

        let mut leftovers1 = vec![];
        if let Some(l) = &self.old_leftovers {
            let bytes = l.to_bytes();
            for (j, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    leftovers1.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(bit))?);
                }
            }
        } else {
            // 256 * (3 + k)
            let num_bits = 256 * (3 + self.params.k);
            for i in 0..num_bits {
                leftovers1.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(false))?);
            }
        }

        let mut leftovers2 = vec![];
        if let Some(l) = &self.new_leftovers {
            let bytes = l.to_bytes();
            for (j, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    leftovers2.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(bit))?);
                }
            }
        } else {
            // 256 * (3 + k)
            let num_bits = 256 * (3 + self.params.k);
            for i in 0..num_bits {
                leftovers2.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(false))?);
            }
        }

        let mut deferred = vec![];
        if let Some(l) = &self.deferred {
            let bytes = l.to_bytes();
            for (j, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    deferred.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(bit))?);
                }
            }
        } else {
            // 256 * (16 + 2k)
            let num_bits = 256 * (16 + 2 * self.params.k);
            for i in 0..num_bits {
                deferred.push(AllocatedBit::alloc_input_unchecked(cs, || Ok(false))?);
            }
        }

        // Check that all the inputs are booleans now that we've allocated
        // all of our public inputs.
        for b in &payload_bits {
            b.check(cs)?;
        }
        for b in &leftovers1 {
            b.check(cs)?;
        }
        for b in &leftovers2 {
            b.check(cs)?;
        }
        for b in &deferred {
            b.check(cs)?;
        }

        // Is this the base case?
        let base_case = AllocatedBit::alloc(cs, || {
            self.base_case.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Compute k(Y) commitment
        let mut k_commitment = CurvePoint::<E2>::constant(
            self.params.generators_xy[1].0,
            self.params.generators_xy[1].1,
        );

        // Attach payload for old proof
        let mut bits_for_k_commitment = vec![];
        if let Some(proof) = &self.proof {
            for byte in &proof.payload {
                for i in 0..8 {
                    let bit = ((*byte >> i) & 1) == 1;
                    bits_for_k_commitment.push(AllocatedBit::alloc(cs, || Ok(bit))?);
                }
            }
        } else {
            for _ in 0..(8 * self.new_payload.len()) {
                // TODO: witness the base case payload?
                bits_for_k_commitment.push(AllocatedBit::alloc(cs, || Ok(false))?);
            }
        }

        let mut old_leftovers1 = vec![];
        if let Some(l) = &self.proof {
            let l = &l.oldproof1;
            let bytes = l.to_bytes();
            for (_, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    old_leftovers1.push(AllocatedBit::alloc(cs, || Ok(bit))?);
                }
            }
        } else {
            // 256 * (3 + k)
            let num_bits = 256 * (3 + self.params.k);
            for _ in 0..num_bits {
                old_leftovers1.push(AllocatedBit::alloc(cs, || Ok(false))?);
            }
        }

        let mut old_deferred = vec![];
        if let Some(l) = &self.proof {
            let l = &l.deferred;
            let bytes = l.to_bytes();
            for (_, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    old_deferred.push(AllocatedBit::alloc(cs, || Ok(bit))?);
                }
            }
        } else {
            let dummy_deferred = Deferred::<E2::Scalar>::dummy(self.params.k);
            let bytes = dummy_deferred.to_bytes();
            for (_, byte) in bytes.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (byte >> i) & 1 == 1;
                    old_deferred.push(AllocatedBit::alloc(cs, || Ok(bit))?);
                }
            }
        }

        bits_for_k_commitment.extend(old_leftovers1.clone());
        bits_for_k_commitment.extend(leftovers1);
        bits_for_k_commitment.extend(old_deferred.clone());

        for (bit, gen) in bits_for_k_commitment
            .into_iter()
            .zip(self.params.generators_xy[2..].iter())
        {
            let gen = CurvePoint::constant(gen.0, gen.1);
            k_commitment = k_commitment.add_conditionally(cs, &gen, &Boolean::from(bit.clone()))?;
        }

        println!("k inside circuit: {:?}", k_commitment);

        // Verify the deferred computations from the inner proof

        self.verify_deferred(cs, &old_deferred)?;
        self.verify_proof(cs, &k_commitment)?;

        self.inner_circuit.synthesize(cs)
    }
}
