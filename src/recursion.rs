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
    pub fn create_proof<CS: RecursiveCircuit<E1::Scalar> + RecursiveCircuit<E2::Scalar>>(
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        old_proof: Option<&RecursiveProof<E2, E1>>,
        circuit: &CS,
        new_payload: &[u8],
    ) -> Result<Self, SynthesisError> {
        let (newdeferred, new_leftovers, old_leftovers, forkvalues) = match old_proof {
            Some(old_proof) => {
                let (_, newdeferred, l1, l2, forkvalues) =
                    old_proof.verify_inner(e2params, e1params, circuit)?;

                (newdeferred, l1, l2, forkvalues)
            }
            None => (
                Deferred::dummy(e2params.k),
                Leftovers::dummy(e2params),
                Leftovers::dummy(e1params),
                vec![0; e2params.k],
            ),
        };

        let mut circuit = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload,
            forkvalues: Some(&forkvalues[..]),
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

    pub(crate) fn verify_inner<CS: RecursiveCircuit<E1::Scalar> + RecursiveCircuit<E2::Scalar>>(
        &self,
        e1params: &Params<E1>,
        e2params: &Params<E2>,
        circuit: &CS,
    ) -> Result<
        (
            bool,
            Deferred<E1::Scalar>,
            Leftovers<E1>,
            Leftovers<E2>,
            Vec<u8>,
        ),
        SynthesisError,
    > {
        let circuit1 = VerificationCircuit::<E1, E2, _> {
            _marker: PhantomData,
            params: e2params,
            base_case: None,
            proof: None,
            inner_circuit: circuit,
            new_payload: &self.payload,
            forkvalues: None,
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
            forkvalues: None,
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

        let (worked, leftovers, deferred, forkvalues) = self.proof.verify::<_, Basic>(
            &self.oldproof1,
            e1params,
            &circuit1,
            &bitinputs,
            Some(k_commitment),
        )?;

        let worked = worked & self.oldproof2.verify::<_, Basic>(e2params, &circuit2)?;

        Ok((
            worked,
            deferred,
            leftovers,
            self.oldproof2.clone(),
            forkvalues,
        ))
    }

    pub fn verify<CS: RecursiveCircuit<E1::Scalar> + RecursiveCircuit<E2::Scalar>>(
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
            forkvalues: None,
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
            forkvalues: None,
            old_leftovers: None,
            new_leftovers: None,
            deferred: None,
        };

        let (worked, deferred, a, b, _) = self.verify_inner(e1params, e2params, circuit)?;

        Ok(worked
            & self.deferred.verify(e2params.k)
            & deferred.verify(e1params.k)
            & a.verify::<_, Basic>(e1params, &circuit1)?
            & b.verify::<_, Basic>(e2params, &circuit2)?)
    }
}

pub(crate) struct VerificationCircuit<'a, C1: Curve, C2: Curve, CS: RecursiveCircuit<C1::Scalar>> {
    pub(crate) _marker: PhantomData<(C1, C2)>,
    pub(crate) params: &'a Params<C2>,
    pub(crate) base_case: Option<bool>,
    pub(crate) inner_circuit: &'a CS,
    pub(crate) proof: Option<&'a RecursiveProof<C2, C1>>,
    pub(crate) new_payload: &'a [u8],
    pub(crate) forkvalues: Option<&'a [u8]>,
    pub(crate) old_leftovers: Option<Leftovers<C1>>,
    pub(crate) new_leftovers: Option<Leftovers<C2>>,
    pub(crate) deferred: Option<Deferred<C2::Scalar>>,
}

impl<'a, E1: Curve, E2: Curve<Base = E1::Scalar>, Inner: RecursiveCircuit<E1::Scalar>>
    VerificationCircuit<'a, E1, E2, Inner>
{
    fn verify_deferred<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        mut deferred: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        // Unpack all of the deferred data
        let x = self.obtain_scalar_from_bits(cs.namespace(|| "pack x"), &deferred[0..128])?;
        deferred = &deferred[128..];
        let y_old =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack y_old"), &deferred[0..128])?;
        deferred = &deferred[128..];
        let y_cur =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack y_cur"), &deferred[0..128])?;
        deferred = &deferred[128..];
        let y_new =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack y_new"), &deferred[0..128])?;
        deferred = &deferred[128..];
        let ky_opening =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack ky_opening"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let tx_positive_opening = self.obtain_scalar_from_bits(
            cs.namespace(|| "pack tx_positive_opening"),
            &deferred[0..256],
        )?;
        deferred = &deferred[256..];
        let tx_negative_opening = self.obtain_scalar_from_bits(
            cs.namespace(|| "pack tx_negative_opening"),
            &deferred[0..256],
        )?;
        deferred = &deferred[256..];
        let sx_cur_opening = self
            .obtain_scalar_from_bits(cs.namespace(|| "pack sx_cur_opening"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let rx_opening =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack rx_opening"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let rxy_opening =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack rxy_opening"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let mut challenges_sq_old = vec![];
        for i in 0..self.params.k {
            challenges_sq_old.push(self.get_challenge_scalar(
                cs.namespace(|| format!("pack old challenge {}", i)),
                &deferred[0..128],
            )?);
            deferred = &deferred[128..];
        }
        let gx_old_opening = self
            .obtain_scalar_from_bits(cs.namespace(|| "pack gx_old_opening"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let mut challenges_sq_new = vec![];
        for i in 0..self.params.k {
            challenges_sq_new.push(self.get_challenge_scalar(
                cs.namespace(|| format!("pack new challenge {}", i)),
                &deferred[0..128],
            )?);
            deferred = &deferred[128..];
        }
        let b_x = self.obtain_scalar_from_bits(cs.namespace(|| "pack b_x"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_xy = self.obtain_scalar_from_bits(cs.namespace(|| "pack b_xy"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_y_old =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack b_y_old"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_y_cur =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack b_y_cur"), &deferred[0..256])?;
        deferred = &deferred[256..];
        let b_y_new =
            self.obtain_scalar_from_bits(cs.namespace(|| "pack b_y_new"), &deferred[0..256])?;
        deferred = &deferred[256..];

        assert_eq!(deferred.len(), 0);

        // Check that the inner proof's circuit check was satisfied for it, since
        // we can do scalar arithmetic more efficiently in our base field! :)

        let xinv = x.invert(cs.namespace(|| "xinv"))?;
        let yinv = y_cur.invert(cs.namespace(|| "yinv"))?;
        let xyinv = xinv.mul(cs.namespace(|| "xyinv"), &yinv)?;
        let xy = x.mul(cs.namespace(|| "xy"), &y_cur)?;
        let x_invy = x.mul(cs.namespace(|| "x_invy"), &yinv)?;

        let nk = self.params.k - 2;

        // let xinvn = xinv.pow(&[n as u64, 0, 0, 0]);
        let mut xinvn = xinv.clone();
        for i in 0..nk {
            xinvn = xinvn.mul(
                cs.namespace(|| format!("xinv^{}", 2u32.pow(i as u32 + 1))),
                &xinvn,
            )?;
        }
        // let xinvd = xinvn.square().square();
        let mut xinvd = xinvn.clone();
        for i in 0..2 {
            xinvd = xinvd.mul(
                cs.namespace(|| format!("(xinv^n)^{}", 2u32.pow(i as u32 + 1))),
                &xinvd,
            )?;
        }
        // let yn = self.y_cur.pow(&[n as u64, 0, 0, 0]);
        let mut yn = y_cur.clone();
        for i in 0..nk {
            yn = yn.mul(
                cs.namespace(|| format!("y^{}", 2u32.pow(i as u32 + 1))),
                &yn,
            )?;
        }
        // let xn = self.x.pow(&[n as u64, 0, 0, 0]);
        let mut xn = x.clone();
        for i in 0..nk {
            xn = xn.mul(
                cs.namespace(|| format!("x^{}", 2u32.pow(i as u32 + 1))),
                &xn,
            )?;
        }
        // let xyinvn31 = xyinv.pow(&[(3 * n - 1) as u64, 0, 0, 0]);
        let mut xyinvn31 = xyinv.clone();
        for i in 0..nk {
            xyinvn31 = xyinvn31.mul(
                cs.namespace(|| format!("xyinv^{}", 2u32.pow(i as u32 + 1))),
                &xyinvn31,
            )?;
        }
        {
            let tmp = xyinvn31.mul(cs.namespace(|| "xyinv^2n"), &xyinvn31)?;
            xyinvn31 = xyinvn31.mul(cs.namespace(|| "xyinv^3n"), &tmp)?;
        }
        xyinvn31 = xyinvn31.mul(cs.namespace(|| "xyinv^(3n-1)"), &xy)?;
        // let xinvn31 = (xinvn.square() * &xinvn) * &self.x;
        let xinvn31 = xinvn.mul(cs.namespace(|| "xinv^2n"), &xinvn)?;
        let xinvn31 = xinvn31.mul(cs.namespace(|| "xinv^3n"), &xinvn)?;
        let xinvn31 = xinvn31.mul(cs.namespace(|| "xinv^(3n-1)"), &x)?;

        // println!("circuit xyinvn31: {:?}", xyinvn31);
        // println!("circuit xinvn31: {:?}", xinvn31);

        let rhs = tx_positive_opening.mul(cs.namespace(|| "tx+opening * x"), &x)?;
        let tmp = tx_negative_opening.mul(cs.namespace(|| "tx-opening * xinvd"), &xinvd)?;
        let rhs = Combination::from(rhs) + tmp;

        let lhs = sx_cur_opening.mul(cs.namespace(|| "sx_cur_opening * xinvn"), &xinvn)?;
        let lhs = lhs.mul(cs.namespace(|| "sx_cur_opening * xinvn * yn"), &yn)?;

        // Computes x + x^2 + x^3 + ... + x^n
        fn compute_thing<F: Field, CS: ConstraintSystem<F>>(
            mut cs: CS,
            x: AllocatedNum<F>,
            k: usize,
        ) -> Result<Combination<F>, SynthesisError> {
            let mut acc = Combination::from(x);
            let mut cur = x.clone();
            for _ in 0..k {
                let tmp = acc.mul(
                    cs.namespace(|| format!("extend polynomial")),
                    &Combination::from(cur),
                )?;
                cur = cur.mul(cs.namespace(|| "square cur"), &cur)?;

                acc = acc + tmp;
            }
            Ok(acc)
        }

        let thing = compute_thing(cs.namespace(|| "poly(xy, nk)"), xy, nk)?;
        let thing = thing + compute_thing(cs.namespace(|| "poly(x_invy, nk)"), x_invy, nk)?;
        let thing = thing.mul(
            cs.namespace(|| "(poly(xy, nk) + poly(x_invy, nk)) * xn"),
            &Combination::from(xn),
        )?;
        /*
        let lhs = lhs - &thing;
        let lhs = lhs + &(self.rxy_opening * &xyinvn31);
        let lhs = lhs * &(self.rx_opening * &xinvn31);
        let ky = self.ky_opening * &yn;
        let lhs = lhs - &ky;
        */

        let tmp = rxy_opening.mul(cs.namespace(|| "rxy_opening * xyinvn31"), &xyinvn31)?;
        let lhs = Combination::from(lhs);
        let lhs = lhs + tmp;
        let lhs = lhs - thing;
        let tmp = rx_opening.mul(cs.namespace(|| "rx_opening * xinvn31"), &xinvn31)?;
        let lhs = lhs.mul(
            cs.namespace(|| "lhs * (rx_opening * xinvn31)"),
            &Combination::from(tmp),
        )?;
        let ky = ky_opening.mul(cs.namespace(|| "ky_opening * yn"), &yn)?;
        let lhs = Combination::from(lhs) - ky;

        let lhs = lhs.lc(&mut cs);
        let rhs = rhs.lc(&mut cs);
        cs.enforce_zero(lhs - &rhs);

        // Check gx_old_opening
        {
            let mut challenges_old = challenges_sq_old.clone();
            for (i, c) in challenges_old.iter_mut().enumerate() {
                *c = c.sqrt(cs.namespace(|| format!("sqrt old challenge_sq {}", i)))?;
            }
            let mut challenges_old_inv = challenges_old.clone();
            for (i, c) in challenges_old_inv.iter_mut().enumerate() {
                *c = c.invert(cs.namespace(|| format!("invert old challenge {}", i)))?;
            }
            let expected_gx_old_opening = self.compute_b(
                cs.namespace(|| "b_old(x)"),
                x,
                &challenges_old,
                &challenges_old_inv,
            )?;

            let lc = expected_gx_old_opening.lc(&mut cs);
            cs.enforce_zero(lc - gx_old_opening.get_variable());
        }

        // Check the other `b` entries
        let mut challenges_new = challenges_sq_new.clone();
        for (i, c) in challenges_new.iter_mut().enumerate() {
            *c = c.sqrt(cs.namespace(|| format!("sqrt new challenge_sq {}", i)))?;
        }
        let mut challenges_new_inv = challenges_new.clone();
        for (i, c) in challenges_new_inv.iter_mut().enumerate() {
            *c = c.invert(cs.namespace(|| format!("invert new challenge {}", i)))?;
        }
        let expected_b_x = self.compute_b(
            cs.namespace(|| "b_new(x)"),
            x,
            &challenges_new,
            &challenges_new_inv,
        )?;
        let expected_b_xy = self.compute_b(
            cs.namespace(|| "b_new(xy)"),
            xy,
            &challenges_new,
            &challenges_new_inv,
        )?;
        let expected_b_y_old = self.compute_b(
            cs.namespace(|| "b_new(y_old)"),
            y_old,
            &challenges_new,
            &challenges_new_inv,
        )?;
        let expected_b_y_cur = self.compute_b(
            cs.namespace(|| "b_new(y_cur)"),
            y_cur,
            &challenges_new,
            &challenges_new_inv,
        )?;
        let expected_b_y_new = self.compute_b(
            cs.namespace(|| "b_new(y_new)"),
            y_new,
            &challenges_new,
            &challenges_new_inv,
        )?;

        let lc = expected_b_x.lc(&mut cs);
        cs.enforce_zero(lc - b_x.get_variable());

        let lc = expected_b_xy.lc(&mut cs);
        cs.enforce_zero(lc - b_xy.get_variable());

        let lc = expected_b_y_old.lc(&mut cs);
        cs.enforce_zero(lc - b_y_old.get_variable());

        let lc = expected_b_y_cur.lc(&mut cs);
        cs.enforce_zero(lc - b_y_cur.get_variable());

        let lc = expected_b_y_new.lc(&mut cs);
        cs.enforce_zero(lc - b_y_new.get_variable());

        Ok(())
    }

    fn compute_b<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        x: AllocatedNum<E1::Scalar>,
        challenges: &[AllocatedNum<E1::Scalar>],
        challenges_inv: &[AllocatedNum<E1::Scalar>],
    ) -> Result<Combination<E1::Scalar>, SynthesisError> {
        assert!(challenges.len() >= 1);
        assert_eq!(challenges.len(), challenges_inv.len());
        Ok(if challenges.len() == 1 {
            // return *challenges_inv.last().unwrap() + *challenges.last().unwrap() * x;
            let tmp = x.mul(
                cs.namespace(|| "x * challenges[-1]"),
                challenges.last().unwrap(),
            )?;
            Combination::from(*challenges_inv.last().unwrap()) + tmp
        } else {
            // return (*challenges_inv.last().unwrap() + *challenges.last().unwrap() * x)
            //     * compute_b(
            //         x.square(),
            //         &challenges[0..(challenges.len() - 1)],
            //         &challenges_inv[0..(challenges.len() - 1)],
            //     );

            let tmp = x.mul(
                cs.namespace(|| "x * challenges[-1]"),
                challenges.last().unwrap(),
            )?;
            let tmp = Combination::from(*challenges_inv.last().unwrap()) + tmp;
            let x2 = x.mul(cs.namespace(|| "x^2"), &x)?;

            Combination::from(
                self.compute_b(
                    cs.namespace(|| format!("b layer {}", challenges.len() - 1)),
                    x2,
                    &challenges[0..(challenges.len() - 1)],
                    &challenges_inv[0..(challenges.len() - 1)],
                )?
                .mul(cs, &tmp)?,
            )
        })
    }

    fn num_equal_unless_base_case<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        base_case: AllocatedBit,
        lhs: &Num<E1::Scalar>,
        rhs: &Num<E1::Scalar>,
    ) -> Result<(), SynthesisError> {
        let not_basecase = base_case.get_value().map(|v| (!v).into());

        // lhs - rhs * (1 - base_case) = 0
        // if base_case is true, then 1 - base_case will be zero
        // if base_case is false, then lhs - rhs must be zero, and therefore they are equal
        let (a, b, c) = cs.multiply(
            || "num_equal_unless_base_case",
            || {
                let lhs = lhs.value().ok_or(SynthesisError::AssignmentMissing)?;
                let rhs = rhs.value().ok_or(SynthesisError::AssignmentMissing)?;
                let not_basecase = not_basecase.ok_or(SynthesisError::AssignmentMissing)?;

                Ok((lhs - &rhs, not_basecase, Field::zero()))
            },
        )?;
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
        base_case: AllocatedBit,
        lhs: &[AllocatedBit],
        rhs: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        assert_eq!(lhs.len(), rhs.len());

        let not_basecase = base_case.get_value().map(|v| (!v).into());

        for (lhs, rhs) in lhs.iter().zip(rhs.iter()) {
            // lhs - rhs * (1 - base_case) = 0
            // if base_case is true, then 1 - base_case will be zero
            // if base_case is false, then lhs - rhs must be zero, and therefore they are equal
            let (a, b, c) = cs.multiply(
                || "equal_unless_base_case",
                || {
                    let lhs = lhs.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    let rhs = rhs.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    let not_basecase = not_basecase.ok_or(SynthesisError::AssignmentMissing)?;

                    let lhs: E1::Scalar = lhs.into();
                    let rhs: E1::Scalar = rhs.into();

                    Ok((lhs - &rhs, not_basecase, Field::zero()))
                },
            )?;
            cs.enforce_zero(LinearCombination::from(a) - lhs.get_variable() + rhs.get_variable());
            cs.enforce_zero(LinearCombination::from(b) - CS::ONE + base_case.get_variable());
            cs.enforce_zero(LinearCombination::from(c))
        }

        Ok(())
    }

    fn obtain_scalar_from_bits<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        bits: &[AllocatedBit],
    ) -> Result<AllocatedNum<E1::Scalar>, SynthesisError> {
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

        let newnum = AllocatedNum::alloc(cs.namespace(|| "scalar"), || {
            value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        cs.enforce_zero(lc - newnum.get_variable());

        Ok(newnum)
    }

    fn witness_bits_from_fe<F: Field, CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        value: F,
    ) -> Result<Vec<AllocatedBit>, SynthesisError> {
        let mut tmp = Vec::with_capacity(256);
        let bytes = value.to_bytes();

        for byte in &bytes[0..] {
            for i in 0..8 {
                let bit = ((*byte >> i) & 1) == 1;
                tmp.push(bit);
            }
        }

        let mut res = Vec::with_capacity(256);

        for (i, b) in tmp.into_iter().enumerate() {
            res.push(AllocatedBit::alloc(
                cs.namespace(|| format!("bit {}", i)),
                || Ok(b),
            )?);
        }

        Ok(res)
    }

    fn verify_proof<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        base_case: AllocatedBit,
        k_commitment: &CurvePoint<E2>,
        old_leftovers: &[AllocatedBit],
        new_deferred: &[AllocatedBit],
        new_leftovers: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        let mut transcript = RescueGadget::new(cs.namespace(|| "init Rescue"))?;
        let transcript = &mut transcript;

        // Commitments

        self.commit_point(
            cs.namespace(|| "commit k_commitment"),
            transcript,
            &k_commitment,
        )?;

        let r_commitment = CurvePoint::witness(cs.namespace(|| "witness r_commitment"), || {
            Ok(self
                .proof
                .map(|proof| proof.proof.r_commitment)
                .unwrap_or(E2::zero()))
        })?;
        self.commit_point(
            cs.namespace(|| "commit r_commitment"),
            transcript,
            &r_commitment,
        )?;

        let y_cur = self.get_challenge(cs.namespace(|| "y_cur challenge"), transcript)?;

        let s_cur_commitment =
            CurvePoint::witness(cs.namespace(|| "witness s_cur_commitment"), || {
                Ok(self
                    .proof
                    .map(|proof| proof.proof.s_cur_commitment)
                    .unwrap_or(E2::zero()))
            })?;
        self.commit_point(
            cs.namespace(|| "commit s_cur_commitment"),
            transcript,
            &s_cur_commitment,
        )?;

        let t_positive_commitment =
            CurvePoint::witness(cs.namespace(|| "witness t_positive_commitment"), || {
                Ok(self
                    .proof
                    .map(|proof| proof.proof.t_positive_commitment)
                    .unwrap_or(E2::zero()))
            })?;
        self.commit_point(
            cs.namespace(|| "commit t_positive_commitment"),
            transcript,
            &t_positive_commitment,
        )?;

        let t_negative_commitment =
            CurvePoint::witness(cs.namespace(|| "witness t_negative_commitment"), || {
                Ok(self
                    .proof
                    .map(|proof| proof.proof.t_negative_commitment)
                    .unwrap_or(E2::zero()))
            })?;
        self.commit_point(
            cs.namespace(|| "commit t_negative_commitment"),
            transcript,
            &t_negative_commitment,
        )?;

        let x = self.get_challenge(cs.namespace(|| "x challenge"), transcript)?;

        let c_commitment = CurvePoint::witness(cs.namespace(|| "witness c_commitment"), || {
            Ok(self
                .proof
                .map(|proof| proof.proof.c_commitment)
                .unwrap_or(E2::zero()))
        })?;
        self.commit_point(
            cs.namespace(|| "commit c_commitment"),
            transcript,
            &c_commitment,
        )?;

        let y_new = self.get_challenge(cs.namespace(|| "y_new challenge"), transcript)?;

        let s_new_commitment =
            CurvePoint::witness(cs.namespace(|| "witness s_new_commitment"), || {
                Ok(self
                    .proof
                    .map(|proof| proof.proof.s_new_commitment)
                    .unwrap_or(E2::zero()))
            })?;
        self.commit_point(
            cs.namespace(|| "commit s_new_commitment"),
            transcript,
            &s_new_commitment,
        )?;

        // // Openings

        let g = {
            let (x, y) = E2::one().get_xy().unwrap();
            CurvePoint::<E2>::constant(x, y)
        };

        let ky_opening_pt = g.multiply(
            cs.namespace(|| "ky_opening_pt"),
            &new_deferred[128 * 4..128 * 4 + 256],
        )?;
        self.commit_point(
            cs.namespace(|| "commit ky_opening_pt"),
            transcript,
            &ky_opening_pt,
        )?;

        let rx_opening_pt = g.multiply(
            cs.namespace(|| "rx_opening_pt"),
            &new_deferred[128 * 4 + 256 * 4..128 * 4 + 256 * 4 + 256],
        )?;
        self.commit_point(
            cs.namespace(|| "commit rx_opening_pt"),
            transcript,
            &rx_opening_pt,
        )?;

        let rxy_opening_pt = g.multiply(
            cs.namespace(|| "rxy_opening_pt"),
            &new_deferred[128 * 4 + 256 * 5..128 * 4 + 256 * 5 + 256],
        )?;
        self.commit_point(
            cs.namespace(|| "commit rxy_opening_pt"),
            transcript,
            &rxy_opening_pt,
        )?;

        let sx_old_opening_pt =
            CurvePoint::witness(cs.namespace(|| "witness sx_old_opening_pt"), || {
                Ok(self
                    .proof
                    .map(|proof| E2::one() * &proof.proof.sx_old_opening)
                    .unwrap_or(E2::zero()))
            })?;
        self.commit_point(
            cs.namespace(|| "commit sx_old_opening_pt"),
            transcript,
            &sx_old_opening_pt,
        )?;

        let sx_cur_opening_pt = g.multiply(
            cs.namespace(|| "sx_cur_opening_pt"),
            &new_deferred[128 * 4 + 256 * 3..128 * 4 + 256 * 3 + 256],
        )?;
        self.commit_point(
            cs.namespace(|| "commit sx_cur_opening_pt"),
            transcript,
            &sx_cur_opening_pt,
        )?;

        let tx_positive_opening_pt = g.multiply(
            cs.namespace(|| "tx_positive_opening_pt"),
            &new_deferred[128 * 4 + 256 * 1..128 * 4 + 256 * 1 + 256],
        )?;
        self.commit_point(
            cs.namespace(|| "commit tx_positive_opening_pt"),
            transcript,
            &tx_positive_opening_pt,
        )?;

        let tx_negative_opening_pt = g.multiply(
            cs.namespace(|| "tx_negative_opening_pt"),
            &new_deferred[128 * 4 + 256 * 2..128 * 4 + 256 * 2 + 256],
        )?;
        self.commit_point(
            cs.namespace(|| "commit tx_negative_opening_pt"),
            transcript,
            &tx_negative_opening_pt,
        )?;

        let sx_new_opening_pt =
            CurvePoint::witness(cs.namespace(|| "witness sx_new_opening_pt"), || {
                Ok(self
                    .proof
                    .map(|proof| E2::one() * &proof.proof.sx_new_opening)
                    .unwrap_or(E2::zero()))
            })?;
        self.commit_point(
            cs.namespace(|| "commit sx_new_opening_pt"),
            transcript,
            &sx_new_opening_pt,
        )?;

        let gx_old_opening_pt = g.multiply(
            cs.namespace(|| "gx_old_opening_pt"),
            &new_deferred[256 * 6 + (4 + self.params.k) * 128..256 * 7 + (4 + self.params.k) * 128],
        )?;
        self.commit_point(
            cs.namespace(|| "commit gx_old_opening_pt"),
            transcript,
            &gx_old_opening_pt,
        )?;

        let z = self.get_challenge(cs.namespace(|| "z challenge"), transcript)?;

        // old_leftovers
        let s_old_commitment =
            CurvePoint::witness(cs.namespace(|| "witness s_old_commitment"), || {
                Ok(self
                    .proof
                    .map(|proof| proof.oldproof1.s_new_commitment)
                    .unwrap_or(E2::zero()))
            })?;
        {
            let mut cs = cs.namespace(|| format!("s_old_commitment"));
            let (x, y) = s_old_commitment.get_xy();
            let x = unpack_fe(cs.namespace(|| "unpack x"), &x)?;
            let y = unpack_fe(cs.namespace(|| "unpack y"), &y)?;
            self.equal_unless_base_case(
                cs.namespace(|| "x"),
                base_case.clone(),
                &x,
                &old_leftovers[0..256],
            )?;
            self.equal_unless_base_case(
                cs.namespace(|| "y"),
                base_case.clone(),
                &y,
                &old_leftovers[256..512],
            )?;
        }

        let g_old = CurvePoint::witness(cs.namespace(|| "witness g_old"), || {
            Ok(self
                .proof
                .map(|proof| proof.oldproof1.g_new)
                .unwrap_or(E2::zero()))
        })?;
        {
            let mut cs = cs.namespace(|| format!("g_old"));
            let (x, y) = g_old.get_xy();
            let x = unpack_fe(cs.namespace(|| "unpack x"), &x)?;
            let y = unpack_fe(cs.namespace(|| "unpack y"), &y)?;
            self.equal_unless_base_case(
                cs.namespace(|| "x"),
                base_case.clone(),
                &x,
                &old_leftovers[256 * 2 + 128..256 * 3 + 128],
            )?;
            self.equal_unless_base_case(
                cs.namespace(|| "y"),
                base_case.clone(),
                &y,
                &old_leftovers[256 * 3 + 128..256 * 4 + 128],
            )?;
        }

        let p_commitment = {
            let mut cs = cs.namespace(|| "p_commitment");
            /*
            let p_commitment = self.r_commitment;
            let p_commitment = p_commitment * &z + leftovers.s_new_commitment;
            let p_commitment = p_commitment * &z + self.s_cur_commitment;
            let p_commitment = p_commitment * &z + self.t_positive_commitment;
            let p_commitment = p_commitment * &z + self.t_negative_commitment;
            let p_commitment = p_commitment * &z + self.s_new_commitment;
            let p_commitment = p_commitment * &z + leftovers.g_new;
            */
            let p_commitment = r_commitment.clone();
            let p_commitment = p_commitment.multiply_fast(cs.namespace(|| "mul z 1"), &z)?;
            let p_commitment =
                p_commitment.add(cs.namespace(|| "add s_old_commitment"), &s_old_commitment)?;
            let p_commitment = p_commitment.multiply_fast(cs.namespace(|| "mul z 2"), &z)?;
            let p_commitment =
                p_commitment.add(cs.namespace(|| "add s_cur_commitment"), &s_cur_commitment)?;
            let p_commitment = p_commitment.multiply_fast(cs.namespace(|| "mul z 3"), &z)?;
            let p_commitment = p_commitment.add(
                cs.namespace(|| "add t_positive_commitment"),
                &t_positive_commitment,
            )?;
            let p_commitment = p_commitment.multiply_fast(cs.namespace(|| "mul z 4"), &z)?;
            let p_commitment = p_commitment.add(
                cs.namespace(|| "add t_negative_commitment"),
                &t_negative_commitment,
            )?;
            let p_commitment = p_commitment.multiply_fast(cs.namespace(|| "mul z 5"), &z)?;
            let p_commitment =
                p_commitment.add(cs.namespace(|| "add s_new_commitment"), &s_new_commitment)?;
            let p_commitment = p_commitment.multiply_fast(cs.namespace(|| "mul z 6"), &z)?;
            p_commitment.add(cs.namespace(|| "add g_old"), &g_old)?
        };

        let p_opening = {
            let mut cs = cs.namespace(|| "p_commitment");
            /*
            let p_opening = self.rx_opening;
            let p_opening = p_opening * &z + &self.sx_old_opening;
            let p_opening = p_opening * &z + &self.sx_cur_opening;
            let p_opening = p_opening * &z + &self.tx_positive_opening;
            let p_opening = p_opening * &z + &self.tx_negative_opening;
            let p_opening = p_opening * &z + &self.sx_new_opening;
            let p_opening = p_opening * &z + &gx_old_opening;
            */
            let p_opening = rx_opening_pt;
            let p_opening = p_opening.multiply_fast(cs.namespace(|| "mul z 1"), &z)?;
            let p_opening =
                p_opening.add(cs.namespace(|| "add sx_old_opening_pt"), &sx_old_opening_pt)?;
            let p_opening = p_opening.multiply_fast(cs.namespace(|| "mul z 2"), &z)?;
            let p_opening =
                p_opening.add(cs.namespace(|| "add sx_cur_opening_pt"), &sx_cur_opening_pt)?;
            let p_opening = p_opening.multiply_fast(cs.namespace(|| "mul z 3"), &z)?;
            let p_opening = p_opening.add(
                cs.namespace(|| "add tx_positive_opening_pt"),
                &tx_positive_opening_pt,
            )?;
            let p_opening = p_opening.multiply_fast(cs.namespace(|| "mul z 4"), &z)?;
            let p_opening = p_opening.add(
                cs.namespace(|| "add tx_negative_opening_pt"),
                &tx_negative_opening_pt,
            )?;
            let p_opening = p_opening.multiply_fast(cs.namespace(|| "mul z 5"), &z)?;
            let p_opening =
                p_opening.add(cs.namespace(|| "add sx_new_opening_pt"), &sx_new_opening_pt)?;
            let p_opening = p_opening.multiply_fast(cs.namespace(|| "mul z 6"), &z)?;
            p_opening.add(cs.namespace(|| "add gx_old_opening_pt"), &gx_old_opening_pt)?
        };

        let q_commitment = {
            let mut cs = cs.namespace(|| "q_commitment");
            /*
            let q_commitment = self.c_commitment + (k_commitment * &z);
            let qy_opening = self.sx_cur_opening + &(ky_opening * &z);
            */

            let q_commitment = k_commitment.multiply_fast(cs.namespace(|| "mul z 1"), &z)?;
            q_commitment.add(cs.namespace(|| "add c_commitment"), &c_commitment)?
        };

        let qy_opening = {
            let mut cs = cs.namespace(|| "qy_opening");
            let qy_opening = ky_opening_pt.multiply_fast(cs.namespace(|| "mul z 2"), &z)?;
            qy_opening.add(cs.namespace(|| "add sx_cur_opening_pt"), &sx_cur_opening_pt)?
        };

        // 7 * 256 + (4 + 2k) * 128
        let b = &[
            &new_deferred[256 * 7 + (4 + 2 * self.params.k) * 128
                ..256 * 7 + (4 + 2 * self.params.k) * 128 + 256],
            &new_deferred[256 * 8 + (4 + 2 * self.params.k) * 128
                ..256 * 8 + (4 + 2 * self.params.k) * 128 + 256],
            &new_deferred[256 * 9 + (4 + 2 * self.params.k) * 128
                ..256 * 9 + (4 + 2 * self.params.k) * 128 + 256],
            &new_deferred[256 * 10 + (4 + 2 * self.params.k) * 128
                ..256 * 10 + (4 + 2 * self.params.k) * 128 + 256],
            &new_deferred[256 * 11 + (4 + 2 * self.params.k) * 128
                ..256 * 11 + (4 + 2 * self.params.k) * 128 + 256],
        ];

        let (g_new, challenges_sq_packed_new) = self.verify_inner_product(
            cs.namespace(|| "inner product"),
            &base_case,
            transcript,
            &[
                p_commitment,
                r_commitment,
                c_commitment.clone(),
                q_commitment,
                c_commitment,
            ],
            &[
                p_opening,
                rxy_opening_pt,
                sx_old_opening_pt,
                qy_opening,
                sx_new_opening_pt,
            ],
            b,
        )?;

        // new_leftovers
        {
            let mut cs = cs.namespace(|| format!("s_new_commitment"));
            let (x, y) = s_new_commitment.get_xy();
            let x = unpack_fe(cs.namespace(|| "unpack x"), &x)?;
            let y = unpack_fe(cs.namespace(|| "unpack y"), &y)?;
            self.equal_unless_base_case(
                cs.namespace(|| "x"),
                base_case.clone(),
                &x,
                &new_leftovers[0..256],
            )?;
            self.equal_unless_base_case(
                cs.namespace(|| "y"),
                base_case.clone(),
                &y,
                &new_leftovers[256..512],
            )?;
        }

        {
            self.equal_unless_base_case(
                cs.namespace(|| "y_new in new_leftovers"),
                base_case.clone(),
                &y_new,
                &new_leftovers[512..512 + 128],
            )?;
        }

        {
            let mut cs = cs.namespace(|| format!("g_new"));
            let (x, y) = g_new.get_xy();
            let x = unpack_fe(cs.namespace(|| "unpack x"), &x)?;
            let y = unpack_fe(cs.namespace(|| "unpack y"), &y)?;
            self.equal_unless_base_case(
                cs.namespace(|| "x"),
                base_case.clone(),
                &x,
                &new_leftovers[256 * 2 + 128..256 * 3 + 128],
            )?;
            self.equal_unless_base_case(
                cs.namespace(|| "y"),
                base_case.clone(),
                &y,
                &new_leftovers[256 * 3 + 128..256 * 4 + 128],
            )?;
        }

        for (i, challenge_sq_packed) in challenges_sq_packed_new.into_iter().enumerate() {
            self.equal_unless_base_case(
                cs.namespace(|| format!("challenge {} in new_leftovers", i)),
                base_case.clone(),
                &challenge_sq_packed,
                &new_leftovers[256 * 4 + 128 + 128 * i..256 * 4 + 128 + 128 * i + 128],
            )?;

            // 4 * 128 + 6 * 256 + k * 128 + 256 is the start
            self.equal_unless_base_case(
                cs.namespace(|| format!("challenge {} in new_deferred", i)),
                base_case.clone(),
                &challenge_sq_packed,
                &new_deferred[(4 * 128 + 6 * 256 + self.params.k * 128 + 256) + i * 128
                    ..(4 * 128 + 6 * 256 + self.params.k * 128 + 256) + i * 128 + 128],
            )?;
        }

        // x (deferred)
        {
            self.equal_unless_base_case(
                cs.namespace(|| "challenge x in new_deferred"),
                base_case.clone(),
                &x,
                &new_deferred[0..128],
            )?;
        }

        // y_cur (deferred)
        {
            self.equal_unless_base_case(
                cs.namespace(|| "challenge y_cur in new_deferred"),
                base_case.clone(),
                &y_cur,
                &new_deferred[128 * 2..128 * 2 + 128],
            )?;
        }

        // y_new (deferred)
        {
            self.equal_unless_base_case(
                cs.namespace(|| "challenge y_new in new_deferred"),
                base_case.clone(),
                &y_new,
                &new_deferred[128 * 3..128 * 3 + 128],
            )?;
        }

        Ok(())
    }

    fn verify_inner_product<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        base_case: &AllocatedBit,
        transcript: &mut RescueGadget<E1::Scalar>,
        commitments: &[CurvePoint<E2>],
        openings: &[CurvePoint<E2>],
        b: &[&[AllocatedBit]],
    ) -> Result<(CurvePoint<E2>, Vec<Vec<AllocatedBit>>), SynthesisError> {
        assert_eq!(commitments.len(), openings.len());
        let mut challenges_sq_packed = vec![];

        let mut p = commitments.to_vec();
        let mut v = openings.to_vec();

        for i in 0..self.params.k {
            let mut cs = cs.namespace(|| format!("round {}", i));
            let mut tmp = vec![];

            for j in 0..commitments.len() {
                let L = CurvePoint::witness(cs.namespace(|| format!("witness L_{}", j)), || {
                    Ok(self
                        .proof
                        .map(|proof| proof.proof.inner_product.rounds[i].L[j])
                        .unwrap_or(E2::zero()))
                })?;
                let R = CurvePoint::witness(cs.namespace(|| format!("witness R_{}", j)), || {
                    Ok(self
                        .proof
                        .map(|proof| proof.proof.inner_product.rounds[i].R[j])
                        .unwrap_or(E2::zero()))
                })?;
                let l = CurvePoint::witness(cs.namespace(|| format!("witness l_{}", j)), || {
                    Ok(self
                        .proof
                        .map(|proof| E2::one() * &proof.proof.inner_product.rounds[i].l[j])
                        .unwrap_or(E2::zero()))
                })?;
                let r = CurvePoint::witness(cs.namespace(|| format!("witness r_{}", j)), || {
                    Ok(self
                        .proof
                        .map(|proof| E2::one() * &proof.proof.inner_product.rounds[i].r[j])
                        .unwrap_or(E2::zero()))
                })?;

                self.commit_point(cs.namespace(|| format!("commit L_{}", j)), transcript, &L)?;
                self.commit_point(cs.namespace(|| format!("commit R_{}", j)), transcript, &R)?;
                self.commit_point(cs.namespace(|| format!("commit l_{}", j)), transcript, &l)?;
                self.commit_point(cs.namespace(|| format!("commit r_{}", j)), transcript, &r)?;

                tmp.push((L, R, l, r));
            }

            let forkvalue =
                AllocatedNum::alloc(cs.namespace(|| format!("fork for challenge {}", i)), || {
                    let val = self.forkvalues.ok_or(SynthesisError::AssignmentMissing)?[i];

                    let fe = Field::from_u128(val as u128);

                    Ok(fe)
                })?;

            transcript.absorb(
                cs.namespace(|| format!("transcript absorb fork value {}", i)),
                Num::from(forkvalue),
            )?;

            let challenge_sq_packed = self.get_challenge(
                cs.namespace(|| format!("round challenge {}", i)),
                transcript,
            )?;
            challenges_sq_packed.push(challenge_sq_packed.clone());

            for (j, tmp) in tmp.into_iter().enumerate() {
                let L = tmp.0.multiply_endo(
                    cs.namespace(|| format!("[challenge^2] L_{}", j)),
                    &challenge_sq_packed,
                )?;
                let R = tmp.1.multiply_inv_endo(
                    cs.namespace(|| format!("[challenge^-2] R_{}", j)),
                    &challenge_sq_packed,
                )?;
                let l = tmp.2.multiply_endo(
                    cs.namespace(|| format!("[challenge^2] l_{}", j)),
                    &challenge_sq_packed,
                )?;
                let r = tmp.3.multiply_inv_endo(
                    cs.namespace(|| format!("[challenge^-2] r_{}", j)),
                    &challenge_sq_packed,
                )?;

                p[j] = p[j].add(cs.namespace(|| format!("p_{} + L_{}", j, j)), &L)?;
                p[j] = p[j].add(cs.namespace(|| format!("p_{} + R_{}", j, j)), &R)?;
                v[j] = v[j].add(cs.namespace(|| format!("p_{} + l_{}", j, j)), &l)?;
                v[j] = v[j].add(cs.namespace(|| format!("p_{} + r_{}", j, j)), &r)?;
            }
        }

        let g_new = CurvePoint::witness(cs.namespace(|| "witness G"), || {
            Ok(self
                .proof
                .map(|proof| proof.proof.inner_product.g)
                .unwrap_or(E2::zero()))
        })?;

        let g = {
            let (x, y) = E2::one().get_xy().unwrap();
            CurvePoint::<E2>::constant(x, y)
        };

        for j in 0..commitments.len() {
            let a = self.witness_bits_from_fe(
                cs.namespace(|| format!("witness a_{}", j)),
                self.proof
                    .map(|proof| proof.proof.inner_product.a[j])
                    .unwrap_or(Field::zero()),
            )?;

            let (x1, y1) = p[j].get_xy();
            let (x2, y2) = g_new
                .multiply(cs.namespace(|| format!("[a_{}] g_new", j)), &a)?
                .get_xy();
            {
                let mut cs = cs.namespace(|| format!("p_{} == [a_{}] g_new", j, j));
                self.num_equal_unless_base_case(cs.namespace(|| "x"), base_case.clone(), &x1, &x2)?;
                self.num_equal_unless_base_case(cs.namespace(|| "y"), base_case.clone(), &y1, &y2)?;
            }

            let (x1, y1) = v[j].get_xy();
            let (x2, y2) = g
                .multiply(cs.namespace(|| "[a_{}] g"), &a)?
                .multiply(cs.namespace(|| format!("[a b_{}] g", j)), b[j])?
                .get_xy();
            {
                let mut cs = cs.namespace(|| format!("v_{} == [a_{} b_{}] g", j, j, j));
                self.num_equal_unless_base_case(cs.namespace(|| "x"), base_case.clone(), &x1, &x2)?;
                self.num_equal_unless_base_case(cs.namespace(|| "y"), base_case.clone(), &y1, &y2)?;
            }
        }

        Ok((g_new, challenges_sq_packed))
    }

    fn commit_point<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        transcript: &mut RescueGadget<E1::Scalar>,
        point: &CurvePoint<E2>,
    ) -> Result<(), SynthesisError> {
        let (x, y) = point.get_xy();
        transcript.absorb(cs.namespace(|| "absorb x"), x)?;
        transcript.absorb(cs.namespace(|| "absorb y"), y)?;

        Ok(())
    }

    fn get_challenge_scalar<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: CS,
        bits: &[AllocatedBit]
    ) -> Result<AllocatedNum<E1::Scalar>, SynthesisError>
    {
        assert_eq!(bits.len(), 128);
        // TODO
        AllocatedNum::alloc(cs, || {
            let mut cur = E1::Scalar::zero();
            for b in bits.iter().rev() {
                cur = cur + &cur;
                if let Some(b) = b.get_value() {
                    if b {
                        cur = cur + &E1::Scalar::one();
                    }
                }
            }

            Ok(crate::util::get_challenge_scalar(cur))
        })
    }

    fn get_challenge<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        transcript: &mut RescueGadget<E1::Scalar>,
    ) -> Result<Vec<AllocatedBit>, SynthesisError> {
        let num = transcript.squeeze(cs.namespace(|| "squeeze"))?;
        let mut bits = unpack_fe(cs.namespace(|| "unpack"), &num.into())?;
        bits.truncate(127);
        bits.push(AllocatedBit::one(cs));

        Ok(bits)
    }
}

impl<'a, E1: Curve, E2: Curve<Base = E1::Scalar>, Inner: RecursiveCircuit<E1::Scalar>>
    Circuit<E1::Scalar> for VerificationCircuit<'a, E1, E2, Inner>
{
    fn synthesize<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut payload_bits = vec![];
        {
            let mut cs = cs.namespace(|| "new_payload");
            for (j, byte) in self.new_payload.into_iter().enumerate() {
                for i in 0..8 {
                    let bit = (*byte >> i) & 1 == 1;
                    payload_bits.push(AllocatedBit::alloc_input_unchecked(
                        cs.namespace(|| format!("bit {}", 8 * j + i)),
                        || Ok(bit),
                    )?);
                }
            }
        }

        let mut leftovers1 = vec![];
        {
            let mut cs = cs.namespace(|| "old_leftovers");
            if let Some(l) = &self.old_leftovers {
                let bytes = l.to_bytes();
                for (j, byte) in bytes.into_iter().enumerate() {
                    for i in 0..8 {
                        let bit = (byte >> i) & 1 == 1;
                        leftovers1.push(AllocatedBit::alloc_input_unchecked(
                            cs.namespace(|| format!("bit {}", 8 * j + i)),
                            || Ok(bit),
                        )?);
                    }
                }
            } else {
                // (256 * 2) + 128 + (256 * 2) + (128 * k)
                // = 256 * 4 + 128 * (k + 1)
                let num_bits = 256 * 4 + 128 * (self.params.k + 1);
                for i in 0..num_bits {
                    leftovers1.push(AllocatedBit::alloc_input_unchecked(
                        cs.namespace(|| format!("bit {}", i)),
                        || Ok(false),
                    )?);
                }
            }
        }

        let mut leftovers2 = vec![];
        {
            let mut cs = cs.namespace(|| "new_leftovers");
            if let Some(l) = &self.new_leftovers {
                let bytes = l.to_bytes();
                for (j, byte) in bytes.into_iter().enumerate() {
                    for i in 0..8 {
                        let bit = (byte >> i) & 1 == 1;
                        leftovers2.push(AllocatedBit::alloc_input_unchecked(
                            cs.namespace(|| format!("bit {}", 8 * j + i)),
                            || Ok(bit),
                        )?);
                    }
                }
            } else {
                // (256 * 2) + 128 + (256 * 2) + (128 * k)
                // = 256 * 4 + 128 * (k + 1)
                let num_bits = 256 * 4 + 128 * (self.params.k + 1);
                for i in 0..num_bits {
                    leftovers2.push(AllocatedBit::alloc_input_unchecked(
                        cs.namespace(|| format!("bit {}", i)),
                        || Ok(false),
                    )?);
                }
            }
        }

        let mut deferred = vec![];
        {
            let mut cs = cs.namespace(|| "deferred");
            if let Some(l) = &self.deferred {
                let bytes = l.to_bytes();
                for (j, byte) in bytes.into_iter().enumerate() {
                    for i in 0..8 {
                        let bit = (byte >> i) & 1 == 1;
                        deferred.push(AllocatedBit::alloc_input_unchecked(
                            cs.namespace(|| format!("bit {}", 8 * j + i)),
                            || Ok(bit),
                        )?);
                    }
                }
            } else {
                // 12 * 256 + (4 + 2k) * 128
                let num_bits = 12 * 256 + (4 + 2 * self.params.k) * 128;
                for i in 0..num_bits {
                    deferred.push(AllocatedBit::alloc_input_unchecked(
                        cs.namespace(|| format!("deferred bit {}", i)),
                        || Ok(false),
                    )?);
                }
            }
        }

        // Check that all the inputs are booleans now that we've allocated
        // all of our public inputs.
        {
            let mut cs = cs.namespace(|| "constrain new_payload");
            for (i, b) in payload_bits.iter().enumerate() {
                b.check(cs.namespace(|| format!("bit {}", i)))?;
            }
        }
        {
            let mut cs = cs.namespace(|| "constrain old_leftovers");
            for (i, b) in leftovers1.iter().enumerate() {
                b.check(cs.namespace(|| format!("bit {}", i)))?;
            }
        }
        {
            let mut cs = cs.namespace(|| "constrain new_leftovers");
            for (i, b) in leftovers2.iter().enumerate() {
                b.check(cs.namespace(|| format!("bit {}", i)))?;
            }
        }
        {
            let mut cs = cs.namespace(|| "constrain deferred");
            for (i, b) in deferred.iter().enumerate() {
                b.check(cs.namespace(|| format!("bit {}", i)))?;
            }
        }

        // Is this the base case?
        let base_case = AllocatedBit::alloc(cs.namespace(|| "is base case"), || {
            self.base_case.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Compute k(Y) commitment
        let mut k_commitment = CurvePoint::<E2>::constant(
            self.params.generators_xy[1].0,
            self.params.generators_xy[1].1,
        );

        // Attach payload for old proof
        let mut old_payload = vec![];
        if let Some(proof) = &self.proof {
            let mut cs = cs.namespace(|| "old_payload");
            for (j, byte) in proof.payload.iter().enumerate() {
                for i in 0..8 {
                    let bit = ((*byte >> i) & 1) == 1;
                    old_payload.push(AllocatedBit::alloc(
                        cs.namespace(|| format!("bit {}", 8 * j + i)),
                        || Ok(bit),
                    )?);
                }
            }
        } else {
            let mut cs = cs.namespace(|| "base_payload");
            for (i, bit) in self.inner_circuit.base_payload().into_iter().enumerate() {
                old_payload.push(AllocatedBit::alloc(
                    cs.namespace(|| format!("bit {}", i)),
                    || Ok(bit),
                )?);
            }
        }

        let basecase_val = base_case.get_value().map(|v| v.into());

        {
            let mut cs = cs.namespace(|| "constrain old_payload if base case");
            for (i, (bit, old_payload_bit)) in self
                .inner_circuit
                .base_payload()
                .into_iter()
                .zip(old_payload.iter())
                .enumerate()
            {
                let (a, b, c) = cs.multiply(
                    || format!("(bit_{} - old_payload_bit_{}) * base_case = 0", i, i),
                    || {
                        let old_payload_bit = old_payload_bit
                            .get_value()
                            .ok_or(SynthesisError::AssignmentMissing)?;
                        let basecase_val = basecase_val.ok_or(SynthesisError::AssignmentMissing)?;

                        let lhs: E1::Scalar = bit.into();
                        let rhs: E1::Scalar = old_payload_bit.into();

                        Ok((lhs - &rhs, basecase_val, Field::zero()))
                    },
                )?;
                if bit {
                    cs.enforce_zero(
                        LinearCombination::from(a) - CS::ONE + old_payload_bit.get_variable(),
                    );
                } else {
                    cs.enforce_zero(LinearCombination::from(a) + old_payload_bit.get_variable());
                }
                cs.enforce_zero(LinearCombination::from(b) - base_case.get_variable());
                cs.enforce_zero(LinearCombination::from(c));
            }
        }

        let mut old_leftovers1 = vec![];
        {
            let mut cs = cs.namespace(|| "old_proof");
            if let Some(l) = &self.proof {
                let l = &l.oldproof1;
                let bytes = l.to_bytes();
                for (j, byte) in bytes.into_iter().enumerate() {
                    for i in 0..8 {
                        let bit = (byte >> i) & 1 == 1;
                        old_leftovers1.push(AllocatedBit::alloc(
                            cs.namespace(|| format!("bit {}", 8 * j + i)),
                            || Ok(bit),
                        )?);
                    }
                }
            } else {
                // (256 * 2) + 128 + (256 * 2) + (128 * k)
                // = 256 * 4 + 128 * (k + 1)
                let num_bits = 256 * 4 + 128 * (self.params.k + 1);
                for i in 0..num_bits {
                    old_leftovers1.push(AllocatedBit::alloc(
                        cs.namespace(|| format!("bit {}", i)),
                        || Ok(false),
                    )?);
                }
            }
        }

        let mut old_deferred = vec![];
        {
            let mut cs = cs.namespace(|| "old_deferred");
            if let Some(l) = &self.proof {
                let l = &l.deferred;
                let bytes = l.to_bytes();
                for (j, byte) in bytes.into_iter().enumerate() {
                    for i in 0..8 {
                        let bit = (byte >> i) & 1 == 1;
                        old_deferred.push(AllocatedBit::alloc(
                            cs.namespace(|| format!("bit {}", 8 * j + i)),
                            || Ok(bit),
                        )?);
                    }
                }
            } else {
                let dummy_deferred = Deferred::<E1::Scalar>::dummy(self.params.k);
                let bytes = dummy_deferred.to_bytes();
                for (_, byte) in bytes.into_iter().enumerate() {
                    for i in 0..8 {
                        let bit = (byte >> i) & 1 == 1;
                        old_deferred.push(AllocatedBit::alloc(
                            cs.namespace(|| format!("bit {}", i)),
                            || Ok(bit),
                        )?);
                    }
                }
            }
        }

        assert_eq!(old_deferred.len(), deferred.len());

        let mut bits_for_k_commitment = vec![];
        bits_for_k_commitment.extend(old_payload.clone());
        bits_for_k_commitment.extend(old_leftovers1.clone());
        bits_for_k_commitment.extend(leftovers1);
        bits_for_k_commitment.extend(old_deferred.clone());

        {
            let mut cs = cs.namespace(|| "k_commitment");
            for (i, (bit, gen)) in bits_for_k_commitment
                .into_iter()
                .zip(self.params.generators_xy[2..].iter())
                .enumerate()
            {
                let gen = CurvePoint::constant(gen.0, gen.1);
                k_commitment = k_commitment.add_conditionally_incomplete(
                    cs.namespace(|| format!("bit {}", i)),
                    &gen,
                    &Boolean::from(bit.clone()),
                )?;
            }
        }

        // println!("k inside circuit: {:?}", k_commitment);

        self.verify_deferred(cs.namespace(|| "verify deferred"), &old_deferred)?;
        self.verify_proof(
            cs.namespace(|| "verify proof"),
            base_case.clone(),
            &k_commitment,
            &old_leftovers1,
            &deferred,
            &leftovers2,
        )?;

        // deferred old challenges should be the same
        self.equal_unless_base_case(
            cs.namespace(|| "deferred[challeges] == old_leftovers1[challenges]"),
            base_case.clone(),
            &deferred[256 * 8..256 * 8 + 128 * self.params.k],
            &old_leftovers1[256 * 4 + 128..],
        )?;

        // deferred y_old should be the same
        self.equal_unless_base_case(
            cs.namespace(|| "deferred[y_old] == old_leftovers1[y_old]"),
            base_case.clone(),
            &deferred[128 * 1..128 * 2],
            &old_leftovers1[256 * 2..256 * 2 + 128],
        )?;

        self.inner_circuit.synthesize(
            &mut cs.namespace(|| "inner circuit"),
            &old_payload,
            &payload_bits,
        )
    }
}
