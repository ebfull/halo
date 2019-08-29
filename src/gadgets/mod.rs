use crate::*;

mod boolean;
mod num;
pub mod sha256;
mod uint32;

pub use boolean::*;
pub use num::*;

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
    rescue_gadget(cs, &[transcript.clone(), point.x.clone(), point.y.clone()])
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

pub struct CurvePoint<C: Curve> {
    x: AllocatedNum<C::Base>,
    y: AllocatedNum<C::Base>,
}

impl<C: Curve> CurvePoint<C> {
    pub fn alloc<FF, CS: ConstraintSystem<C::Base>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<Self, SynthesisError>
    where
        FF: FnOnce() -> Result<(C::Base, C::Base), SynthesisError>,
    {
        let mut y_value = None;
        let (x, x2) = AllocatedNum::alloc_and_square(cs, || {
            let (x, y) = value()?;
            y_value = Some(y);
            Ok(x)
        })?;
        let (y, y2) = AllocatedNum::alloc_and_square(cs, || {
            y_value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let x3 = x2.mul(cs, &x)?;
        cs.enforce_zero(
            LinearCombination::from(y2.get_variable())
                - x3.get_variable()
                - (Coeff::from(C::b()), CS::ONE),
        );

        Ok(CurvePoint { x, y })
    }
}
