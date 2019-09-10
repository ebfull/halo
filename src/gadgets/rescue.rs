use crate::{
    circuits::{Coeff, ConstraintSystem, SynthesisError},
    fields::Field,
    gadgets::num::{AllocatedNum, Combination, Num},
    rescue::{generate_mds_matrix, RESCUE_M, RESCUE_ROUNDS, SPONGE_RATE},
};
use std::ops::AddAssign;

fn rescue_f<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [Combination<F>; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
    key_schedule: &[[Num<F>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
) -> Result<(), SynthesisError> {
    for (entry, key) in state.iter_mut().zip(key_schedule[0].iter()) {
        *entry += *key;
    }

    for r in 0..2 * RESCUE_ROUNDS {
        let mut mid = vec![];
        for entry in state.iter() {
            if r % 2 == 0 {
                mid.push(entry.rescue_invalpha(cs)?);
            } else {
                mid.push(entry.rescue_alpha(cs)?);
            };
        }

        for (next_entry, (mds_row, key)) in state
            .iter_mut()
            .zip(mds_matrix.iter().zip(key_schedule[r + 1].iter()))
        {
            let mut sum = Combination::from(Num::constant(F::zero()));
            for (coeff, entry) in mds_row.iter().zip(mid.iter()) {
                sum = sum + (Coeff::Full(*coeff), *entry);
            }
            *next_entry = sum + *key;
        }
    }

    Ok(())
}

/// Duplicates [`rescue_f`] in order to extract the key schedule.
fn generate_key_schedule<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    master_key: [Num<F>; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> Result<[[Num<F>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1], SynthesisError> {
    // TODO: Generate correct constants
    let constants = [[Num::constant(F::one()); RESCUE_M]; 2 * RESCUE_ROUNDS + 1];

    let mut key_schedule = vec![];

    let mut state: Vec<_> = master_key
        .iter()
        .zip(constants[0].iter())
        .map(|(e, k)| Combination::from(*e) + *k)
        .collect();
    key_schedule.push(
        state
            .iter()
            .map(|c| c.evaluate(cs))
            .collect::<Result<Vec<_>, _>>()?,
    );

    for r in 0..2 * RESCUE_ROUNDS {
        let mut mid = vec![];
        for entry in state.iter() {
            if r % 2 == 0 {
                mid.push(entry.rescue_invalpha(cs)?);
            } else {
                mid.push(entry.rescue_alpha(cs)?);
            };
        }

        for (next_entry, (mds_row, constant)) in state
            .iter_mut()
            .zip(mds_matrix.iter().zip(constants[r + 1].iter()))
        {
            let mut sum = Combination::from(Num::constant(F::zero()));
            for (coeff, entry) in mds_row.iter().zip(mid.iter()) {
                sum = sum + (Coeff::Full(*coeff), *entry);
            }
            *next_entry = sum + *constant;
        }

        key_schedule.push(
            state
                .iter()
                .map(|c| c.evaluate(cs))
                .collect::<Result<Vec<_>, _>>()?,
        );
    }

    let key_schedule: Vec<_> = key_schedule
        .into_iter()
        .map(|k| {
            [
                k[0], k[1], k[2], k[3], k[4], k[5], k[6], k[7], k[8], k[9], k[10], k[11], k[12],
            ]
        })
        .collect();

    Ok([
        key_schedule[0],
        key_schedule[1],
        key_schedule[2],
        key_schedule[3],
        key_schedule[4],
        key_schedule[5],
        key_schedule[6],
        key_schedule[7],
        key_schedule[8],
        key_schedule[9],
        key_schedule[10],
        key_schedule[11],
        key_schedule[12],
        key_schedule[13],
        key_schedule[14],
        key_schedule[15],
        key_schedule[16],
        key_schedule[17],
        key_schedule[18],
        key_schedule[19],
        key_schedule[20],
    ])
}

fn pad<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &[Option<Num<F>>; SPONGE_RATE],
) -> Result<[Num<F>; SPONGE_RATE], SynthesisError> {
    let one = AllocatedNum::alloc(cs, || Ok(F::one()))?;
    cs.enforce_zero(one.lc() - CS::ONE);

    let mut padded = vec![];
    for i in 0..SPONGE_RATE {
        if let Some(e) = input[i] {
            padded.push(e);
        } else {
            // No more elements; apply necessary padding
            // TODO: Decide on a padding strategy (currently padding with all-ones)
            padded.push(one.into());
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
    input: &[Option<Num<F>>; SPONGE_RATE],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
    key_schedule: &[[Num<F>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
) -> Result<(), SynthesisError> {
    for (entry, input) in state.iter_mut().zip(pad(cs, input)?.iter()) {
        entry.add_assign(*input);
    }

    rescue_f(cs, state, mds_matrix, key_schedule)?;

    Ok(())
}

enum SpongeState<F: Field> {
    Absorbing([Option<Num<F>>; SPONGE_RATE]),
    Squeezing([bool; SPONGE_RATE]),
}

impl<F: Field> SpongeState<F> {
    fn absorb(val: Num<F>) -> Self {
        let mut input = [None; SPONGE_RATE];
        input[0] = Some(val);
        SpongeState::Absorbing(input)
    }
}

pub struct RescueGadget<F: Field> {
    sponge: SpongeState<F>,
    state: [Combination<F>; RESCUE_M],
    mds_matrix: [[F; RESCUE_M]; RESCUE_M],
    key_schedule: [[Num<F>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
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
        let mds_matrix = generate_mds_matrix();

        // To use Rescue as a permutation, fix the master key to zero
        let key_schedule =
            generate_key_schedule(cs, [Num::constant(F::zero()); RESCUE_M], &mds_matrix)?;

        Ok(RescueGadget {
            sponge: SpongeState::Absorbing([None; SPONGE_RATE]),
            state,
            mds_matrix,
            key_schedule,
        })
    }

    pub fn absorb<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        val: Num<F>,
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
                rescue_duplex(
                    cs,
                    &mut self.state,
                    input,
                    &self.mds_matrix,
                    &self.key_schedule,
                )?;
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
                    rescue_duplex(
                        cs,
                        &mut self.state,
                        &input,
                        &self.mds_matrix,
                        &self.key_schedule,
                    )?;
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

#[cfg(test)]
mod test {
    use super::RescueGadget;
    use crate::{
        circuits::{is_satisfied, Circuit, ConstraintSystem, SynthesisError},
        fields::Fp,
        gadgets::AllocatedNum,
        rescue::{Rescue, SPONGE_RATE},
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
                g.absorb(cs, n.into())?;
                g.absorb(cs, n2.into())?;

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

    #[test]
    fn saturate_sponge() {
        struct TestCircuit {
            expected_s: Fp,
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut g = RescueGadget::new(cs)?;

                for i in 0..=2 * SPONGE_RATE {
                    let n = AllocatedNum::alloc(cs, || Ok(Fp::from(i as u64 + 1)))?;
                    g.absorb(cs, n.into())?;
                }

                let s = g.squeeze(cs)?;

                if let Some(s) = s.get_value() {
                    println!("Computed s: {:?}", s);
                }

                let expected_s = AllocatedNum::alloc_input(cs, || Ok(self.expected_s))?;

                cs.enforce_zero(expected_s.lc() - &s.lc());

                Ok(())
            }
        }

        let mut r = Rescue::new();

        for i in 0..=2 * SPONGE_RATE {
            r.absorb(Fp::from(i as u64 + 1));
        }

        let expected_s = r.squeeze();

        println!("Expected s: {:?}", expected_s);
        println!();

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit { expected_s }, &[expected_s]),
            Ok(true)
        );
    }

    #[test]
    fn squeeze_dry() {
        struct TestCircuit {
            expected_s: Fp,
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut g = RescueGadget::new(cs)?;
                let n = AllocatedNum::alloc(cs, || Ok(Fp::from(7)))?;

                for i in 0..=2 * SPONGE_RATE {
                    g.squeeze(cs)?;
                }

                let s = g.squeeze(cs)?;

                if let Some(s) = s.get_value() {
                    println!("Computed s: {:?}", s);
                }

                let expected_s = AllocatedNum::alloc_input(cs, || Ok(self.expected_s))?;

                cs.enforce_zero(expected_s.lc() - &s.lc());

                Ok(())
            }
        }

        let mut r = Rescue::new();
        r.absorb(Fp::from(7));

        for _ in 0..=2 * SPONGE_RATE {
            r.squeeze();
        }

        let expected_s = r.squeeze();

        println!("Expected s: {:?}", expected_s);
        println!();

        assert_eq!(
            is_satisfied::<_, _, Basic>(&TestCircuit { expected_s }, &[expected_s]),
            Ok(true)
        );
    }
}
