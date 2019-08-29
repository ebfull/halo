use crate::*;
use std::ops::Add;

mod boolean;
pub use boolean::*;

#[derive(Copy, Clone)]
pub struct AllocatedNum<F> {
    value: Option<F>,
    var: Variable,
}

impl<F: Field> AllocatedNum<F> {
    pub fn alloc<FF, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let var = cs.alloc(|| "num", || value)?;

        Ok(AllocatedNum {
            value: value.ok(),
            var,
        })
    }

    pub fn alloc_input<FF, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let var = cs.alloc_input(|| "input variable", || value)?;

        Ok(AllocatedNum {
            value: value.ok(),
            var,
        })
    }

    pub fn inputify<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let var = cs.alloc_input(
            || "input variable",
            || self.value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce_zero(LinearCombination::from(self.var) - var);

        Ok(AllocatedNum {
            value: self.value,
            var,
        })
    }

    pub fn mul<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let product = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a * b)));

        let (l, r, o) = cs.multiply(|| {
            let l = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let r = other.value.ok_or(SynthesisError::AssignmentMissing)?;
            let o = product.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((l, r, o))
        })?;

        cs.enforce_zero(LinearCombination::from(self.var) - l);
        cs.enforce_zero(LinearCombination::from(other.var) - r);

        Ok(AllocatedNum {
            value: product,
            var: o,
        })
    }

    pub fn alloc_and_square<FF, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError>
    where
        FF: FnOnce() -> Result<F, SynthesisError>,
    {
        let value = value();
        let mut value_sq = None;
        let (a, b, c) = cs.multiply(|| {
            let value = value?;
            value_sq = Some(value.square());

            Ok((value, value, value_sq.unwrap()))
        })?;
        cs.enforce_zero(LinearCombination::from(a) - b);

        Ok((
            AllocatedNum {
                value: value.ok(),
                var: a,
            },
            AllocatedNum {
                value: value_sq,
                var: c,
            },
        ))
    }

    pub fn lc(&self) -> LinearCombination<F> {
        LinearCombination::from(self.var)
    }
}

#[derive(Copy, Clone)]
enum Num<F: Field> {
    Constant(Coeff<F>),
    Allocated(Coeff<F>, AllocatedNum<F>),
}

impl<F: Field> From<AllocatedNum<F>> for Num<F> {
    fn from(num: AllocatedNum<F>) -> Self {
        Num::Allocated(Coeff::One, num)
    }
}

impl<F: Field> Num<F> {
    pub fn constant(val: F) -> Self {
        Num::Constant(Coeff::from(val))
    }

    pub fn value(&self) -> Option<F> {
        match *self {
            Num::Constant(v) => Some(v.value()),
            Num::Allocated(coeff, var) => var.value.map(|v| (coeff * v).value()),
        }
    }
}

#[derive(Clone)]
struct Combination<F: Field> {
    value: Option<F>,
    terms: Vec<Num<F>>,
}

impl<F: Field> From<AllocatedNum<F>> for Combination<F> {
    fn from(num: AllocatedNum<F>) -> Self {
        Combination {
            value: num.value,
            terms: vec![num.into()],
        }
    }
}

impl<F: Field> From<Num<F>> for Combination<F> {
    fn from(num: Num<F>) -> Self {
        Combination {
            value: num.value(),
            terms: vec![num],
        }
    }
}

impl<F: Field> Add<AllocatedNum<F>> for Combination<F> {
    type Output = Combination<F>;

    fn add(mut self, other: AllocatedNum<F>) -> Combination<F> {
        let new_value = self
            .value
            .and_then(|a| other.value.and_then(|b| Some(a + b)));

        self.terms.push(other.into());

        Combination {
            value: new_value,
            terms: self.terms,
        }
    }
}

impl<F: Field> Combination<F> {
    pub fn lc<CS: ConstraintSystem<F>>(&self, _cs: &mut CS) -> LinearCombination<F> {
        let mut acc = LinearCombination::zero();

        for term in &self.terms {
            let tmp = match term {
                Num::Constant(v) => (Coeff::from(*v), CS::ONE),
                Num::Allocated(coeff, num) => (Coeff::from(*coeff), num.var),
            };

            acc = acc + tmp;
        }

        acc
    }

    pub fn square<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let mut value = None;
        let (l, r, o) = cs.multiply(|| {
            let l = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let c = l.square();
            value = Some(c);

            Ok((l, l, c))
        })?;

        let lc = self.lc(cs);
        cs.enforce_zero(lc.clone() - l);
        cs.enforce_zero(lc - r);

        Ok(AllocatedNum { value, var: o })
    }
}

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
        cs.enforce_zero(LinearCombination::from(y2.var) - x3.var - (Coeff::from(C::b()), CS::ONE));

        Ok(CurvePoint { x, y })
    }
}
