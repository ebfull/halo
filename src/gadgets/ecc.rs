use super::AllocatedNum;
use crate::{
    circuits::{Coeff, ConstraintSystem, LinearCombination, SynthesisError},
    Curve,
};

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

    pub fn x(&self) -> AllocatedNum<C::Base> {
        self.x
    }

    pub fn y(&self) -> AllocatedNum<C::Base> {
        self.y
    }
}
