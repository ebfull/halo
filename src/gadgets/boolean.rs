use crate::*;

#[derive(Debug)]
pub struct AllocatedBit {
    value: Option<bool>,
    var: Variable
}

impl AllocatedBit {
    pub fn alloc<F: Field, CS: ConstraintSystem<F>, FF>(
        cs: &mut CS,
        value: FF
    ) -> Result<Self, SynthesisError>
        where FF: FnOnce() -> Result<bool, SynthesisError>
    {
        let mut final_value = None;
        let (a, b, c) = cs.multiply(|| {
            let v = value()?;
            final_value = Some(v);
            let fe = if v {
                F::one()
            } else {
                F::zero()
            };

            Ok((fe, fe, fe))
        })?;

        cs.enforce_zero(LinearCombination::from(a) - b);
        cs.enforce_zero(LinearCombination::from(b) - c);

        Ok(AllocatedBit {
            value: final_value,
            var: a
        })
    }
}

pub fn unpack_fe<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    num: &AllocatedNum<F>
) -> Result<Vec<AllocatedBit>, SynthesisError>
{
    let values = match num.value {
        Some(value) => {
            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);
            let bytes = value.to_bytes();

            for byte in &bytes[0..] {
                for i in 0..8 {
                    let bit = ((*byte >> i) & 1) == 1;
                    tmp.push(Some(bit));
                }
            }

            tmp
        },
        None => {
            vec![None; F::NUM_BITS as usize]
        }
    };

    let mut bools = vec![];
    for value in values {
        bools.push(AllocatedBit::alloc(cs, || {
            value.ok_or(SynthesisError::AssignmentMissing)
        })?);
    }

    // Check that it's equal.
    let mut lc = LinearCombination::zero();
    let mut cur = F::one();
    for b in &bools {
        lc = lc + (Coeff::from(cur), b.var);
        cur = cur + cur;
    }
    cs.enforce_zero(lc - num.var);

    Ok(bools)
}
