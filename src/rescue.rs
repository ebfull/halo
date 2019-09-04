//! Implementation of a duplex sponge construction based on the Rescue algebraic
//! permutation.

use crate::fields::Field;

pub(crate) const RESCUE_ROUNDS: usize = 10;
pub(crate) const RESCUE_M: usize = 13;

// Set sponge capacity to 1
pub(crate) const SPONGE_RATE: usize = RESCUE_M - 1;

pub(crate) fn generate_mds_matrix<F: Field>() -> [[F; RESCUE_M]; RESCUE_M] {
    // TODO: Correct MDS generation; this causes horribly-biased output
    let mut mds_matrix = [[F::zero(); RESCUE_M]; RESCUE_M];
    for i in (0..RESCUE_M).rev() {
        for j in (0..RESCUE_M).rev() {
            mds_matrix[i][j] = F::from_u64(((i + 1) * j) as u64);
        }
    }
    mds_matrix
}

fn mds<F: Field>(
    in_state: &[F; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> [F; RESCUE_M] {
    let mut out_state = [F::zero(); RESCUE_M];
    for i in 0..RESCUE_M {
        for j in 0..RESCUE_M {
            out_state[i] += mds_matrix[i][j] * in_state[j];
        }
    }
    out_state
}

fn rescue_f<F: Field>(state: &mut [F; RESCUE_M], mds_matrix: &[[F; RESCUE_M]; RESCUE_M]) {
    for r in 0..2 * RESCUE_ROUNDS {
        let exp = if r % 2 == 0 {
            F::RESCUE_INVALPHA
        } else {
            [F::RESCUE_ALPHA, 0, 0, 0]
        };
        for entry in state.iter_mut() {
            *entry = entry.pow_vartime(&exp);
        }
        *state = mds(state, mds_matrix);
    }
}

fn pad<F: Field>(input: &[Option<F>; SPONGE_RATE]) -> [F; SPONGE_RATE] {
    let mut padded = [F::one(); SPONGE_RATE];
    for i in 0..SPONGE_RATE {
        if let Some(e) = input[i] {
            padded[i] = e;
        } else {
            // No more elements; apply necessary padding
            // TODO: Decide on a padding strategy (currently padding with all-ones)
        }
    }
    padded
}

fn rescue_duplex<F: Field>(
    state: &mut [F; RESCUE_M],
    input: &[Option<F>; SPONGE_RATE],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
) -> [Option<F>; SPONGE_RATE] {
    let padded = pad(input);
    for i in 0..SPONGE_RATE {
        state[i] += padded[i];
    }

    rescue_f(state, mds_matrix);

    let mut output = [None; SPONGE_RATE];
    for i in 0..SPONGE_RATE {
        output[i] = Some(state[i]);
    }
    output
}

enum SpongeState<F: Field> {
    Absorbing([Option<F>; SPONGE_RATE]),
    Squeezing([Option<F>; SPONGE_RATE]),
}

impl<F: Field> SpongeState<F> {
    fn absorb(val: F) -> Self {
        let mut input = [None; SPONGE_RATE];
        input[0] = Some(val);
        SpongeState::Absorbing(input)
    }
}

pub struct Rescue<F: Field> {
    sponge: SpongeState<F>,
    state: [F; RESCUE_M],
    mds_matrix: [[F; RESCUE_M]; RESCUE_M],
}

impl<F: Field> Default for Rescue<F> {
    fn default() -> Self {
        Rescue::new()
    }
}

impl<F: Field> Rescue<F> {
    pub fn new() -> Self {
        Rescue {
            sponge: SpongeState::Absorbing([None; SPONGE_RATE]),
            state: [F::zero(); RESCUE_M],
            mds_matrix: generate_mds_matrix(),
        }
    }

    pub fn absorb(&mut self, val: F) {
        match self.sponge {
            SpongeState::Absorbing(ref mut input) => {
                for entry in input.iter_mut() {
                    if entry.is_none() {
                        *entry = Some(val);
                        return;
                    }
                }

                // We've already absorbed as many elements as we can
                let _ = rescue_duplex(&mut self.state, input, &self.mds_matrix);
                self.sponge = SpongeState::absorb(val);
            }
            SpongeState::Squeezing(_) => {
                // Drop the remaining output elements
                self.sponge = SpongeState::absorb(val);
            }
        }
    }

    pub fn squeeze(&mut self) -> F {
        loop {
            match self.sponge {
                SpongeState::Absorbing(input) => {
                    self.sponge = SpongeState::Squeezing(rescue_duplex(
                        &mut self.state,
                        &input,
                        &self.mds_matrix,
                    ));
                }
                SpongeState::Squeezing(ref mut output) => {
                    for entry in output.iter_mut() {
                        if let Some(e) = entry.take() {
                            return e;
                        }
                    }

                    // We've already squeezed out all available elements
                    self.sponge = SpongeState::Absorbing([None; SPONGE_RATE]);
                }
            }
        }
    }
}
