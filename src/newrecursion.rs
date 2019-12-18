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

    fn check_deferred<CS: ConstraintSystem<E1::Scalar>>(
        &self,
        cs: &mut CS,
        deferred_bits: &[AllocatedBit],
    ) -> Result<(), SynthesisError> {
        // TODO

        Ok(())
    }

    fn compute_k<'b, I, CS: ConstraintSystem<E1::Scalar>>(
        &self,
        mut cs: CS,
        mut bits: I,
    ) -> Result<(Num<E1::Scalar>, Num<E1::Scalar>), SynthesisError>
    where
        I: Iterator<Item = &'b AllocatedBit>,
    {
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

        self.check_deferred(&mut *cs, &inner_proof_remote_deferred)?;

        // Compute K commitment for inner proof
        self.compute_k(
            &mut *cs,
            inner_proof_local_amortized
                .iter()
                .chain(new_proof_local_amortized.iter())
                .chain(inner_proof_remote_deferred.iter()),
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
