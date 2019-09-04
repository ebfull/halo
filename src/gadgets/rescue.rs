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
use std::ops::AddAssign;

fn rescue_f<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [Combination<F>; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> Result<(), SynthesisError> {
    let mut cur: Vec<_> = state.iter().cloned().collect();

    for r in 0..2 * RESCUE_ROUNDS {
        let mut mid = vec![];
        for entry in cur.into_iter() {
            if r % 2 == 0 {
                mid.push(AllocatedNum::rescue_invalpha(cs, entry)?);
            } else {
                mid.push(AllocatedNum::rescue_alpha(cs, entry)?);
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

    for (i, entry) in cur.into_iter().enumerate() {
        state[i] = entry;
    }

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
    state: &mut [Combination<F>; RESCUE_M],
    input: &[Option<AllocatedNum<F>>; SPONGE_RATE],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> Result<(), SynthesisError> {
    for (entry, input) in state.iter_mut().zip(pad(cs, input)?.iter()) {
        entry.add_assign(*input);
    }

    rescue_f(cs, state, mds_matrix)?;

    Ok(())
}

enum SpongeState<F: Field> {
    Absorbing([Option<AllocatedNum<F>>; SPONGE_RATE]),
    Squeezing([bool; SPONGE_RATE]),
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
    state: [Combination<F>; RESCUE_M],
    mds_matrix: [[F; RESCUE_M]; RESCUE_M],
}

impl<F: Field> RescueGadget<F> {
    pub fn new<CS: ConstraintSystem<F>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let state = [
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
            Num::constant(F::zero()).into(),
        ];

        Ok(RescueGadget {
            sponge: SpongeState::Absorbing([None; SPONGE_RATE]),
            state,
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
                rescue_duplex(cs, &mut self.state, input, &self.mds_matrix)?;
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
                    rescue_duplex(cs, &mut self.state, &input, &self.mds_matrix)?;
                    self.sponge = SpongeState::Squeezing([false; SPONGE_RATE]);
                }
                SpongeState::Squeezing(ref mut output) => {
                    for (squeezed, entry) in output.iter_mut().zip(self.state.iter_mut()) {
                        if !*squeezed {
                            *squeezed = true;

                            let out = AllocatedNum::alloc(cs, || {
                                entry.get_value().ok_or(SynthesisError::AssignmentMissing)
                            })?;
                            let entry_lc = entry.lc(cs);
                            cs.enforce_zero(out.lc() - &entry_lc);

                            // As we've constrained this current state combination, we can
                            // substitute for the new variable to shorten subsequent
                            // combinations.
                            *entry = out.into();

                            return Ok(out);
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
