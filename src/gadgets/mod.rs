use crate::*;

mod boolean;
mod ecc;
mod num;
pub mod sha256;
mod uint32;
mod uint64;

pub use boolean::*;
pub use ecc::*;
pub use num::*;
pub use uint64::*;

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
