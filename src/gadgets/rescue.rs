use crate::{
    circuits::{Coeff, ConstraintSystem, IntoLinearCombination, LinearCombination, SynthesisError},
    curves::Curve,
    fields::Field,
    gadgets::{
        boolean::{unpack_fe, AllocatedBit},
        ecc::CurvePoint,
        num::{AllocatedNum, Combination, Num},
    },
    rescue::{generate_mds_matrix, RESCUE_M, RESCUE_ROUNDS, SPONGE_RATE},
};

/// Constrain base^5 = result
///
/// We can do so with three multiplication constraints and seven linear constraints:
///
/// a * b = c
/// a = x
/// b = x
/// c = x^2
///
/// d * e = f
/// d = c
/// e = c
/// f = x^4
///
/// g * h = i
/// g = f
/// h = x
/// i = x^5
fn constrain_pow_5<F, CS, B, R>(cs: &mut CS, base: B, result: R) -> Result<(), SynthesisError>
where
    F: Field,
    CS: ConstraintSystem<F>,
    B: IntoLinearCombination<F>,
    R: IntoLinearCombination<F>,
{
    let base_lc = base.lc(cs);
    let result_lc = result.lc(cs);

    let x = base.get_value();
    let x2 = x.and_then(|x| Some(x.square()));
    let x4 = x2.and_then(|x2| Some(x2.square()));
    let x5 = x4.and_then(|x4| x.and_then(|x| Some(x4 * x)));

    let (a_var, b_var, c_var) = cs.multiply(|| {
        let x = x.ok_or(SynthesisError::AssignmentMissing)?;
        let x2 = x2.ok_or(SynthesisError::AssignmentMissing)?;

        Ok((x, x, x2))
    })?;
    cs.enforce_zero(base_lc.clone() - a_var);
    cs.enforce_zero(base_lc.clone() - b_var);

    let (d_var, e_var, f_var) = cs.multiply(|| {
        let x2 = x2.ok_or(SynthesisError::AssignmentMissing)?;
        let x4 = x4.ok_or(SynthesisError::AssignmentMissing)?;

        Ok((x2, x2, x4))
    })?;
    cs.enforce_zero(LinearCombination::from(c_var) - d_var);
    cs.enforce_zero(LinearCombination::from(c_var) - e_var);

    let (g_var, h_var, i_var) = cs.multiply(|| {
        let x = x.ok_or(SynthesisError::AssignmentMissing)?;
        let x4 = x4.ok_or(SynthesisError::AssignmentMissing)?;
        let x5 = x5.ok_or(SynthesisError::AssignmentMissing)?;

        Ok((x4, x, x5))
    })?;
    cs.enforce_zero(LinearCombination::from(f_var) - g_var);
    cs.enforce_zero(base_lc - h_var);
    cs.enforce_zero(result_lc - i_var);

    Ok(())
}

fn rescue_f<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [AllocatedNum<F>; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> Result<(), SynthesisError> {
    println!("Gadget state before f:");
    for entry in state.iter() {
        if let Some(v) = entry.get_value() {
            println!("  {:?},", v);
        }
    }
    println!();

    let mut cur: Vec<_> = state
        .iter()
        .map(|entry| Combination::from(*entry))
        .collect();

    for r in 0..2 * RESCUE_ROUNDS {
        let mut mid = vec![];
        for entry in cur.into_iter() {
            // Assuming F::RESCUE_ALPHA = 5, we need to constrain either entry^5 or
            // entry^(1/5).
            assert_eq!(F::RESCUE_ALPHA, 5);
            if r % 2 == 0 {
                let result = AllocatedNum::alloc(cs, || {
                    let num = entry.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    Ok(num.pow(&F::RESCUE_INVALPHA))
                })?;

                // entry^(1/5) --> Constrain result^5 = entry
                constrain_pow_5(cs, result, entry)?;

                mid.push(result);
            } else {
                let result = AllocatedNum::alloc(cs, || {
                    let num = entry.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    Ok(num.pow(&[F::RESCUE_ALPHA, 0, 0, 0]))
                })?;

                // entry^5 --> Constrain entry^5 = result
                constrain_pow_5(cs, entry, result)?;

                mid.push(result);
            };
        }

        let mut next = vec![];
        for mds_row in mds_matrix.iter() {
            let mut sum = Combination::from(Num::constant(F::zero()));
            for (coeff, entry) in mds_row.iter().zip(mid.iter()) {
                sum = sum + (Coeff::Full(*coeff), *entry);
            }
            next.push(sum);
        }

        cur = next;
    }

    for i in 0..RESCUE_M {
        let out = AllocatedNum::alloc(cs, || {
            cur[i].get_value().ok_or(SynthesisError::AssignmentMissing)
        })?;
        let cur_lc = cur[i].lc(cs);
        cs.enforce_zero(out.lc() - &cur_lc);
        state[i] = out;
    }

    println!("Gadget state after f:");
    for entry in state.iter() {
        if let Some(v) = entry.get_value() {
            println!("  {:?},", v);
        }
    }
    println!();

    Ok(())
}

fn pad<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &[Option<AllocatedNum<F>>; SPONGE_RATE],
) -> Result<[AllocatedNum<F>; SPONGE_RATE], SynthesisError> {
    let one = AllocatedNum::alloc(cs, || Ok(F::one()))?;
    cs.enforce_zero(one.lc() - CS::ONE);

    let mut padded = vec![];
    for i in 0..SPONGE_RATE {
        if let Some(e) = input[i] {
            padded.push(e);
        } else {
            // No more elements; apply necessary padding
            // TODO: Decide on a padding strategy (currently padding with all-ones)
            padded.push(one);
        }
    }

    // Manually expand so that we return a fixed-length array without having to
    // allocate placeholder variables.
    Ok([
        padded[0], padded[1], padded[2], padded[3], padded[4], padded[5], padded[6], padded[7],
        padded[8], padded[9], padded[10], padded[11],
    ])
}

fn rescue_duplex<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [AllocatedNum<F>; RESCUE_M],
    input: &[Option<AllocatedNum<F>>; SPONGE_RATE],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> Result<[Option<AllocatedNum<F>>; SPONGE_RATE], SynthesisError> {
    for (entry, input) in state.iter_mut().zip(pad(cs, input)?.iter()) {
        let sum = Combination::from(*entry) + *input;
        *entry = AllocatedNum::alloc(cs, || {
            sum.get_value().ok_or(SynthesisError::AssignmentMissing)
        })?;
        let sum_lc = sum.lc(cs);
        cs.enforce_zero(entry.lc() - &sum_lc);
    }

    rescue_f(cs, state, mds_matrix)?;

    let mut output = [None; SPONGE_RATE];
    for i in 0..SPONGE_RATE {
        output[i] = Some(state[i]);
    }
    Ok(output)
}

enum SpongeState<F: Field> {
    Absorbing([Option<AllocatedNum<F>>; SPONGE_RATE]),
    Squeezing([Option<AllocatedNum<F>>; SPONGE_RATE]),
}

impl<F: Field> SpongeState<F> {
    fn absorb(val: AllocatedNum<F>) -> Self {
        let mut input = [None; SPONGE_RATE];
        input[0] = Some(val);
        SpongeState::Absorbing(input)
    }
}

pub struct RescueGadget<F: Field> {
    sponge: SpongeState<F>,
    state: [AllocatedNum<F>; RESCUE_M],
    mds_matrix: [[F; RESCUE_M]; RESCUE_M],
}

impl<F: Field> RescueGadget<F> {
    pub fn new<CS: ConstraintSystem<F>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let zero = AllocatedNum::alloc(cs, || Ok(F::zero()))?;
        cs.enforce_zero(zero.lc());

        Ok(RescueGadget {
            sponge: SpongeState::Absorbing([None; SPONGE_RATE]),
            state: [zero; RESCUE_M],
            mds_matrix: generate_mds_matrix(),
        })
    }

    pub fn absorb<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        val: AllocatedNum<F>,
    ) -> Result<(), SynthesisError> {
        match self.sponge {
            SpongeState::Absorbing(ref mut input) => {
                for entry in input.iter_mut() {
                    if entry.is_none() {
                        *entry = Some(val);
                        return Ok(());
                    }
                }

                // We've already absorbed as many elements as we can
                let _ = rescue_duplex(cs, &mut self.state, input, &self.mds_matrix)?;
                self.sponge = SpongeState::absorb(val);
            }
            SpongeState::Squeezing(_) => {
                // Drop the remaining output elements
                self.sponge = SpongeState::absorb(val);
            }
        }

        Ok(())
    }

    pub fn squeeze<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        loop {
            match self.sponge {
                SpongeState::Absorbing(input) => {
                    self.sponge = SpongeState::Squeezing(rescue_duplex(
                        cs,
                        &mut self.state,
                        &input,
                        &self.mds_matrix,
                    )?);
                }
                SpongeState::Squeezing(ref mut output) => {
                    for entry in output.iter_mut() {
                        if let Some(e) = entry.take() {
                            return Ok(e);
                        }
                    }

                    // We've already squeezed out all available elements
                    self.sponge = SpongeState::Absorbing([None; SPONGE_RATE]);
                }
            }
        }
    }
}

/*
pub fn rescue_gadget<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    inputs: &[AllocatedNum<F>],
) -> Result<AllocatedNum<F>, SynthesisError> {
    let mut cur = Combination::from(Num::constant(F::ALPHA));
    for input in inputs {
        for _ in 0..30 {
            cur = cur + *input;
            cur = Combination::from(cur.square(cs)?);
        }
    }

    cur.square(cs)
}
*/
pub fn rescue<F: Field>(inputs: &[F]) -> F {
    let mut cur = F::ALPHA;
    for input in inputs {
        for _ in 0..30 {
            cur = cur + *input;
            cur = cur.square()
        }
    }

    cur.square()
}
/*
pub fn append_point<C: Curve, CS: ConstraintSystem<C::Base>>(
    cs: &mut CS,
    transcript: &AllocatedNum<C::Base>,
    point: &CurvePoint<C>,
) -> Result<AllocatedNum<C::Base>, SynthesisError> {
    rescue_gadget(cs, &[transcript.clone(), point.x(), point.y()])
}

pub fn obtain_challenge<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    transcript: &AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, Vec<AllocatedBit>), SynthesisError> {
    let new_transcript = rescue_gadget(cs, &[transcript.clone()])?;

    // We don't need to enforce that it's canonical; the adversary
    // only gains like a bit out of this.
    let mut bits = unpack_fe(cs, &transcript)?;
    bits.truncate(128); // only need lower 128 bits

    Ok((new_transcript, bits))
}
*/

#[cfg(test)]
mod test {
    use super::RescueGadget;
    use crate::{
        circuits::{
            is_satisfied, Circuit, ConstraintSystem, IntoLinearCombination, SynthesisError,
        },
        fields::Fp,
        gadgets::AllocatedNum,
        rescue::Rescue,
        Basic,
    };

    #[test]
    fn test_rescue_gadget() {
        struct TestCircuit {
            expected_s: Fp,
            expected_s2: Fp,
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut g = RescueGadget::new(cs)?;

                let (n, n2) = AllocatedNum::alloc_and_square(cs, || Ok(Fp::from(3)))?;
                g.absorb(cs, n)?;
                g.absorb(cs, n2)?;

                let s = g.squeeze(cs)?;
                let s2 = g.squeeze(cs)?;

                if let (Some(s1), Some(s2)) = (s.get_value(), s2.get_value()) {
                    println!("Computed s1: {:?}", s1);
                    println!("Computed s2: {:?}", s2);
                }

                let expected_s = AllocatedNum::alloc_input(cs, || Ok(self.expected_s))?;
                let expected_s2 = AllocatedNum::alloc_input(cs, || Ok(self.expected_s2))?;

                cs.enforce_zero(expected_s.lc() - &s.lc());
                cs.enforce_zero(expected_s2.lc() - &s2.lc());

                Ok(())
            }
        }

        let mut r = Rescue::new();

        r.absorb(Fp::from(3));
        r.absorb(Fp::from(9));

        let expected_s = r.squeeze();
        let expected_s2 = r.squeeze();

        println!("Expected s1: {:?}", expected_s);
        println!("Expected s2: {:?}", expected_s2);
        println!();

        assert_eq!(
            is_satisfied::<_, _, Basic>(
                &TestCircuit {
                    expected_s,
                    expected_s2
                },
                &[expected_s, expected_s2]
            ),
            Ok(true)
        );
    }
}
