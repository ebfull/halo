use super::boolean::{AllocatedBit, Boolean};
use crate::{fields::Field, Coeff, ConstraintSystem, LinearCombination, SynthesisError};

/// Represents an interpretation of 64 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone)]
pub struct UInt64 {
    // Least significant bit first
    bits: Vec<Boolean>,
    value: Option<u64>,
}

impl UInt64 {
    /// Construct a constant `UInt64` from a `u64`
    pub fn constant(value: u64) -> Self {
        let mut bits = Vec::with_capacity(64);

        let mut tmp = value;
        for _ in 0..64 {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        UInt64 {
            bits,
            value: Some(value),
        }
    }

    /// Allocate a `UInt64` in the constraint system
    pub fn alloc<F, CS>(mut cs: CS, value: Option<u64>) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(64);

                for _ in 0..64 {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            }
            None => vec![None; 64],
        };

        let bits = values
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("allocated bit {}", i)),
                    || v.ok_or(SynthesisError::AssignmentMissing),
                )?))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(UInt64 { bits, value })
    }

    /// Turns this `UInt64` into its little-endian byte order representation.
    pub fn into_bits(self) -> Vec<Boolean> {
        self.bits
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt64`.
    pub fn from_bits(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 64);

        let new_bits = bits.to_vec();

        let mut value = Some(0u64);
        for b in new_bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match *b {
                Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                }
                Boolean::Is(ref b) => match b.get_value() {
                    Some(true) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(false) => {}
                    None => value = None,
                },
                Boolean::Not(ref b) => match b.get_value() {
                    Some(false) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(true) => {}
                    None => value = None,
                },
            }
        }

        UInt64 {
            value,
            bits: new_bits,
        }
    }

    pub fn lc<F, CS>(&self) -> LinearCombination<F>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let mut lc = LinearCombination::zero();
        let mut coeff = Coeff::One;
        for bit in &self.bits {
            lc = lc + &bit.lc(CS::ONE, coeff);
            coeff = coeff.double();
        }
        lc
    }

    /// Returns (self * other) + addend1 + addend2.
    ///
    /// Doesn't overflow 128 bits, because the maximum assignable value is
    /// (2^64 - 1)^2 + 2*(2^64 - 1) = 2^128 - 1
    pub fn mul_acc2<F, CS>(
        &self,
        mut cs: CS,
        other: &Self,
        addend1: &Self,
        addend2: &Self,
    ) -> Result<(Self, Self), SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let product = self.value.and_then(|a| {
            other
                .value
                .and_then(|b| Some(u128::from(a) * u128::from(b)))
        });

        let result_value = product.and_then(|p| {
            addend1.value.and_then(|c1| {
                addend2
                    .value
                    .and_then(|c2| Some(p + u128::from(c1) + u128::from(c2)))
            })
        });

        let result_bits = {
            let values = match result_value {
                Some(mut val) => {
                    let mut v = Vec::with_capacity(128);

                    for _ in 0..128 {
                        v.push(Some(val & 1 == 1));
                        val >>= 1;
                    }

                    v
                }
                None => vec![None; 128],
            };

            values
                .into_iter()
                .enumerate()
                .map(|(i, v)| {
                    Ok(Boolean::from(AllocatedBit::alloc(
                        cs.namespace(|| format!("allocated bit {}", i)),
                        || v.ok_or(SynthesisError::AssignmentMissing),
                    )?))
                })
                .collect::<Result<Vec<_>, SynthesisError>>()?
        };

        let res_low = UInt64::from_bits(&result_bits[0..64]);
        let res_high = UInt64::from_bits(&result_bits[64..128]);

        let (l, r, o) = cs.multiply(|| {
            let l = self
                .value
                .map(F::from_u64)
                .ok_or(SynthesisError::AssignmentMissing)?;
            let r = other
                .value
                .map(F::from_u64)
                .ok_or(SynthesisError::AssignmentMissing)?;
            let o = product
                .map(F::from_u128)
                .ok_or(SynthesisError::AssignmentMissing)?;

            Ok((l, r, o))
        })?;

        // 2^64
        let high_coeff = Coeff::from(
            F::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ])
            .unwrap(),
        );

        cs.enforce_zero(self.lc::<F, CS>() - l);
        cs.enforce_zero(other.lc::<F, CS>() - r);
        cs.enforce_zero(
            res_low.lc::<F, CS>() + (high_coeff, &res_high.lc::<F, CS>())
                - o
                - &addend1.lc::<F, CS>()
                - &addend2.lc::<F, CS>(),
        );

        Ok((res_low, res_high))
    }
}

#[cfg(test)]
mod test {
    use super::UInt64;
    use crate::{
        circuits::Circuit, fields::Fp, gadgets::boolean::Boolean, is_satisfied, Basic,
        ConstraintSystem, SynthesisError,
    };
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_uint64_from_bits() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let v = (0..64)
                .map(|_| Boolean::constant(rng.next_u32() % 2 != 0))
                .collect::<Vec<_>>();

            let b = UInt64::from_bits(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match *bit {
                    Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    }
                    _ => unreachable!(),
                }
            }

            let expected_to_be_same = b.into_bits();

            for x in v.iter().zip(expected_to_be_same.iter()) {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_uint64_mulacc2() {
        struct TestCircuit {
            a: u64,
            b: u64,
            c: u64,
            d: u64,
        };

        impl TestCircuit {
            fn new(rng: &mut XorShiftRng) -> Self {
                TestCircuit {
                    a: rng.next_u64(),
                    b: rng.next_u64(),
                    c: rng.next_u64(),
                    d: rng.next_u64(),
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut expected = (u128::from(self.a) * u128::from(self.b))
                    + u128::from(self.c)
                    + u128::from(self.d);

                let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(self.a))?;
                let b_bit = UInt64::constant(self.b);
                let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(self.c))?;
                let d_bit = UInt64::constant(self.d);

                let (r_low, r_high) =
                    a_bit.mul_acc2(cs.namespace(|| "mul_acc2"), &b_bit, &c_bit, &d_bit)?;

                assert!(r_low.value.map(u128::from) == Some(expected & (((1 as u128) << 64) - 1)));
                assert!(r_high.value.map(u128::from) == Some(expected >> 64));

                for b in r_low.bits.iter().chain(r_high.bits.iter()) {
                    match *b {
                        Boolean::Is(ref b) => {
                            assert!(b.get_value().unwrap() == (expected & 1 == 1));
                        }
                        Boolean::Not(ref b) => {
                            assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                        }
                        Boolean::Constant(b) => {
                            assert!(b == (expected & 1 == 1));
                        }
                    }

                    expected >>= 1;
                }

                Ok(())
            }
        }

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            assert_eq!(
                is_satisfied::<_, _, Basic>(&TestCircuit::new(&mut rng), &[]),
                Ok(true)
            );
        }
    }
}
