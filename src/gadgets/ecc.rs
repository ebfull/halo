use super::AllocatedNum;
use crate::{
    circuits::{Coeff, ConstraintSystem, LinearCombination, SynthesisError},
    Curve,
};
use super::{Num, Boolean};

pub struct CurvePoint<C: Curve> {
    x: Num<C::Base>,
    y: Num<C::Base>
}

impl<C: Curve> CurvePoint<C> {
    pub fn constant(x: C::Base, y: C::Base) -> Self {
        CurvePoint {
            x: Num::constant(x), y: Num::constant(y)
        }
    }

    pub fn add_conditionally<CS: ConstraintSystem<C::Base>>(
        &self,
        cs: &mut CS,
        other: &Self,
        condition: Boolean
    ) -> Result<Self, SynthesisError>
    {
        let p1 = self.x.value().and_then(|x| {
            self.y.value().and_then(|y| {
                Some(C::from_xy(x, y).unwrap())
            })
        });

        let p2 = other.x.value().and_then(|x| {
            other.y.value().and_then(|y| {
                Some(C::from_xy(x, y).unwrap())
            })
        });

        let p3 = p1.and_then(|p1| {
            p2.and_then(|p2| {
                condition.get_value().and_then(|b| {
                    if b {
                        Some((p1 + p2).get_xy().unwrap())
                    } else {
                        self.x.value().and_then(|x| {
                            self.y.value().and_then(|y| {
                                Some((x, y))
                            })
                        })
                    }
                })
            })
        });

        let x3 = AllocatedNum::alloc(cs, || {
            Ok(p3.ok_or(SynthesisError::AssignmentMissing)?.0)
        })?;

        let y3 = AllocatedNum::alloc(cs, || {
            Ok(p3.ok_or(SynthesisError::AssignmentMissing)?.1)
        })?;

        Ok(CurvePoint {
            x: Num::from(x3),
            y: Num::from(y3)
        })
    }
}
