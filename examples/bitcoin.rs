#[macro_use]
extern crate hex_literal;

#[macro_use]
extern crate uint;

use halo::{
    is_satisfied, sha256::sha256, unpack_fe, AllocatedBit, AllocatedNum, Basic, Boolean, Circuit,
    Coeff, ConstraintSystem, Field, Fp, LinearCombination, SynthesisError, UInt64,
};
use sha2::{Digest, Sha256};
use std::iter;

construct_uint! {
    pub struct U256(4);
}

fn bytes_to_bits<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    data: Option<&[u8]>,
    len: usize,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = vec![];

    for byte_i in 0..len {
        for bit_i in (0..8).rev() {
            let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

            bits.push(
                AllocatedBit::alloc(cs, || {
                    data.map(|bytes| (bytes[byte_i] >> bit_i) & 1u8 == 1u8)
                        .ok_or(SynthesisError::AssignmentMissing)
                })?
                .into(),
            );
        }
    }

    Ok(bits)
}

fn input_bytes_to_bits<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    data: Option<&[u8]>,
    len: usize,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = vec![];

    for byte_i in 0..len {
        for bit_i in (0..8).rev() {
            let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

            let value = data.map(|bytes| (bytes[byte_i] >> bit_i) & 1u8 == 1u8);
            let alloc_bit =
                AllocatedBit::alloc(cs, || value.ok_or(SynthesisError::AssignmentMissing))?;
            let input_bit = AllocatedNum::alloc_input(cs, || {
                value
                    .map(|value| if value { F::one() } else { F::zero() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce_zero(input_bit.lc() - alloc_bit.get_variable());

            bits.push(alloc_bit.into());
        }
    }

    Ok(bits)
}

fn add_input_bits_for_bytes<F: Field>(input: &mut Vec<F>, data: &[u8]) {
    for byte in data.iter() {
        for bit_i in (0..8).rev() {
            let value = (byte >> bit_i) & 1u8 == 1u8;
            input.push(if value { F::one() } else { F::zero() });
        }
    }
}

fn enforce_equality<F: Field, CS: ConstraintSystem<F>>(cs: &mut CS, a: &[Boolean], b: &[Boolean]) {
    assert_eq!(a.len(), b.len());

    let mut a_lc = LinearCombination::zero();
    let mut b_lc = LinearCombination::zero();
    let mut coeff = Coeff::One;
    for (a_bit, b_bit) in a.into_iter().zip(b.into_iter()) {
        a_lc = a_lc + &a_bit.lc(CS::ONE, coeff);
        b_lc = b_lc + &b_bit.lc(CS::ONE, coeff);
        coeff = coeff.double();
    }
    cs.enforce_zero(a_lc - &b_lc);
}

fn lc_from_bits<F: Field, CS: ConstraintSystem<F>>(bits: &[Boolean]) -> LinearCombination<F> {
    let mut lc = LinearCombination::zero();
    let mut coeff = Coeff::One;
    for bit in bits {
        lc = lc + &bit.lc(CS::ONE, coeff);
        coeff = coeff.double();
    }
    lc
}

struct CompactBits {
    mantissa: Option<[u8; 3]>,
    size: Option<usize>,
    mantissa_bits: Vec<Boolean>,
    mantissa_sign_bit: Boolean,
    size_bits: Vec<Boolean>,
}

impl CompactBits {
    fn from_header(bytes: Option<&[u8; 80]>, bits: &[Boolean]) -> Self {
        const NBITS_START: usize = 4 + 32 + 32 + 4;

        let (mantissa, size) = match bytes {
            Some(bytes) => {
                let mut mantissa = [0; 3];
                mantissa.copy_from_slice(&bytes[NBITS_START..NBITS_START + 3]);
                mantissa[2] &= 0xfe; // TODO or 0x7f?
                let size = bytes[NBITS_START + 3] as usize;

                // Assert that the size is at least 4, so the mantissa doesn't collide with the
                // lowest byte, and we can just set the lowest bit to get (target + 1)
                assert!(size >= 4);

                (Some(mantissa), Some(size))
            }
            None => (None, None),
        };

        let mantissa_bits = bits[8 * NBITS_START..(8 * NBITS_START) + 23]
            .iter()
            .cloned()
            .collect();
        let mantissa_sign_bit = bits[(8 * NBITS_START) + 23].clone();
        let size_bits = bits[(8 * NBITS_START) + 24..(8 * NBITS_START) + 32]
            .iter()
            .cloned()
            .collect();

        CompactBits {
            mantissa,
            size,
            mantissa_bits,
            mantissa_sign_bit,
            size_bits,
        }
    }

    fn unpack<F: Field, CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(Vec<Boolean>, Option<U256>), SynthesisError> {
        // Enforce that the mantissa sign bit is zero. A negative target is invalid under
        // the Bitcoin consensus rules.
        cs.enforce_zero(self.mantissa_sign_bit.lc(CS::ONE, Coeff::One));

        // Construct the target from the size and mantissa, and witness it
        let target_val = match (self.mantissa, self.size) {
            (Some(mantissa), Some(size)) => {
                let mut bytes = [0; 32];
                bytes[size - 3] = mantissa[0];
                bytes[size - 2] = mantissa[1];
                bytes[size - 1] = mantissa[2];
                Some(bytes)
            }
            _ => None,
        };
        let target = bytes_to_bits(
            cs.namespace(|| "target"),
            target_val.as_ref().map(|b| &b[..]),
            32,
        )?;

        // We enforce that target is correctly derived from nBits:
        //   mantissa * 256^(size - 3) = target
        //
        // with the following constraints:
        //   a * b = c
        //   a = mantissa
        //   c = target
        //
        //   d * e = f
        //   d = b
        //   e = 256^3
        //   f = 256^size

        let base_val = F::from_u64(256);
        let base = AllocatedNum::alloc(cs, || Ok(base_val))?;
        cs.enforce_zero(base.lc() - (Coeff::Full(base_val), CS::ONE));

        // Enforce that the top three bits of size are zero, so that 256^size does not
        // overflow a field element. This allows a maximum size of 31, which is larger
        // than the largest possible size that will occur in the nBits field in Bitcoin.
        assert!(F::CAPACITY >= ((8 * 31) + 1));
        cs.enforce_zero(self.size_bits[0].lc(CS::ONE, Coeff::One));
        cs.enforce_zero(self.size_bits[1].lc(CS::ONE, Coeff::One));
        cs.enforce_zero(self.size_bits[2].lc(CS::ONE, Coeff::One));

        let mut pow_size = AllocatedNum::alloc(cs, || Ok(F::one()))?;
        for bit in self.size_bits.iter().skip(3) {
            // Square, then conditionally multiply by 256
            //
            // sq = cur^2
            // sq_m256 = sq * 256
            // next = (1 - x)*sq + x*sq_m256
            // next = sq - x*sq + x*sq_m256
            // next - sq = x * (sq_m256 - sq)
            //
            // a * b = c
            // a = x
            // b = sq_m256 - sq
            // c = next - sq

            let sq = pow_size.mul(cs, &pow_size)?;
            let sq_m256 = sq.mul(cs, &base)?;
            pow_size = AllocatedNum::alloc(cs, || {
                match (bit.get_value(), sq.get_value(), sq_m256.get_value()) {
                    (Some(b), Some(sq), Some(sq_m256)) => Ok(if b { sq_m256 } else { sq }),
                    _ => Err(SynthesisError::AssignmentMissing),
                }
            })?;

            let (a_var, b_var, c_var) = cs.multiply(|| {
                match (
                    bit.get_value(),
                    sq.get_value(),
                    sq_m256.get_value(),
                    pow_size.get_value(),
                ) {
                    (Some(b), Some(sq), Some(sq_m256), Some(next)) => {
                        let a_val = if b { F::one() } else { F::zero() };
                        let b_val = sq_m256 - sq;
                        let c_val = next - sq;

                        Ok((a_val, b_val, c_val))
                    }
                    _ => Err(SynthesisError::AssignmentMissing),
                }
            })?;

            cs.enforce_zero(bit.lc(CS::ONE, Coeff::One) - a_var);
            cs.enforce_zero(sq_m256.lc() - &sq.lc() - b_var);
            cs.enforce_zero(pow_size.lc() - &sq.lc() - c_var);
        }

        let b_val = self
            .size
            .map(|size| base_val.pow(&[size as u64 - 3, 0, 0, 0]));
        let (a_var, b_var, c_var) = cs.multiply(|| {
            let mantissa = self.mantissa.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = b_val.ok_or(SynthesisError::AssignmentMissing)?;
            let target = target_val.ok_or(SynthesisError::AssignmentMissing)?;

            let mantissa_val = {
                let mut bytes = [0; 8];
                bytes[0..3].copy_from_slice(&mantissa);
                F::from_u64(u64::from_le_bytes(bytes))
            };

            // Build target value with double-and-add
            let mut target_val = F::zero();
            for byte in target.iter().rev() {
                for i in 0..8 {
                    target_val = target_val + target_val;
                    if (byte >> i) & 1u8 == 1u8 {
                        target_val = target_val + F::one();
                    }
                }
            }

            Ok((mantissa_val, b_val, target_val))
        })?;

        // 256^3
        let base_pow3 = F::from_u64(0x01000000);
        let (d_var, e_var, f_var) = cs.multiply(|| {
            let b_val = b_val.ok_or(SynthesisError::AssignmentMissing)?;
            let size = self.size.ok_or(SynthesisError::AssignmentMissing)?;

            Ok((b_val, base_pow3, base_val.pow(&[size as u64, 0, 0, 0])))
        })?;

        let mantissa_lc = lc_from_bits::<F, CS>(&self.mantissa_bits);
        let target_lc = lc_from_bits::<F, CS>(&target);
        cs.enforce_zero(mantissa_lc - a_var);
        cs.enforce_zero(target_lc - c_var);
        cs.enforce_zero(LinearCombination::from(b_var) - d_var);
        cs.enforce_zero(LinearCombination::from(e_var) - (Coeff::Full(base_pow3), CS::ONE));
        cs.enforce_zero(pow_size.lc() - f_var);

        Ok((
            target,
            target_val.map(|bytes| U256::from_little_endian(&bytes)),
        ))
    }
}

struct BitcoinHeaderCircuit<F: Field> {
    header: Option<[u8; 80]>,
    remainder: Option<F>,
    prev_height: Option<F>,
    prev_hash: Option<[u8; 32]>,
    prev_chain_work: Option<F>,
}

impl<F: Field> BitcoinHeaderCircuit<F> {
    fn from_witnesses(header: [u8; 80], remainder: F, prev: (F, [u8; 32], F)) -> Self {
        BitcoinHeaderCircuit {
            header: Some(header),
            remainder: Some(remainder),
            prev_height: Some(prev.0),
            prev_hash: Some(prev.1),
            prev_chain_work: Some(prev.2),
        }
    }

    fn for_verification() -> Self {
        BitcoinHeaderCircuit {
            header: None,
            remainder: None,
            prev_height: None,
            prev_hash: None,
            prev_chain_work: None,
        }
    }
}

impl<F: Field> Circuit<F> for BitcoinHeaderCircuit<F> {
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Witness the previous height
        let prev_height = AllocatedNum::alloc(cs, || {
            self.prev_height.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Expose the current block height as an input
        let height = AllocatedNum::alloc_input(cs, || {
            self.prev_height
                .map(|h| h + F::one())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce_zero(height.lc() - &prev_height.lc() - CS::ONE);

        // Witness the header
        let header_bits = bytes_to_bits(
            cs.namespace(|| "header"),
            self.header.as_ref().map(|b| &b[..]),
            80,
        )?;

        // Witness the previous hash
        let prev_bits = bytes_to_bits(
            cs.namespace(|| "prev"),
            self.prev_hash.as_ref().map(|b| &b[..]),
            32,
        )?;

        // Enforce that header contains the previous hash
        enforce_equality(cs, &header_bits[32..32 + 256], &prev_bits);

        // Compute SHA256d(header)
        let result = {
            let mid = sha256(cs, &header_bits)?;
            sha256(cs, &mid)?
        };

        // Expose the hash as an input
        let hash_value = self
            .header
            .map(|header| Sha256::digest(&Sha256::digest(&header)));
        let hash_bits = input_bytes_to_bits(
            cs.namespace(|| "hash"),
            hash_value.as_ref().map(|b| &b[..]),
            32,
        )?;
        assert_eq!(result.len(), hash_bits.len());
        enforce_equality(cs, &result, &hash_bits);

        // Unpack nBits as the block target
        let (target, target_val) =
            CompactBits::from_header(self.header.as_ref(), &header_bits).unpack(cs)?;

        // TODO: Range check hash <= target

        // Next, we want to enforce that the witnessed work is correct for this block.
        // We need to compute block_work = 2^256 / (target+1), but there are two problems:
        //
        // - We can't represent 2^256 as it's too large for a field element.
        // - This is integer division, so we can't simply witness block_work and constrain
        //   the multiplication.
        //
        // Our strategy is to use 64-bit limbs and full-width u256 x u256 -> u512
        // multiplication to ensure that (target + 1) * block_work does not wrap, and then
        // constrain (target + 1) * block_work + remainder = 2^256 with remainder <= target.

        // Construct (target + 1) by setting the lowest bit of target to 1
        let target_p1_bits: Vec<_> = iter::once(Boolean::Constant(true))
            .chain(target.iter().skip(1).cloned())
            .collect();

        // Load (target + 1) into four 64-bit limbs
        let target_p1_limbs = [
            UInt64::from_bits(&target_p1_bits[0..64]),
            UInt64::from_bits(&target_p1_bits[64..128]),
            UInt64::from_bits(&target_p1_bits[128..192]),
            UInt64::from_bits(&target_p1_bits[192..256]),
        ];

        // Witness the work for this block
        let block_work_val = target_val
            .ok_or(SynthesisError::AssignmentMissing)
            .and_then(|target| {
                let work = (!target / (target + 1)) + 1;

                let mut bytes = [0; 32];
                work.to_little_endian(&mut bytes);

                let fe = F::from_bytes(&bytes);
                if fe.is_some().into() {
                    Ok(fe.unwrap())
                } else {
                    Err(SynthesisError::Unsatisfiable)
                }
            });
        let block_work = AllocatedNum::alloc(cs, || block_work_val)?;

        // Load block_work into four 64-bit limbs
        let work_bits: Vec<_> = unpack_fe(cs, &block_work)?
            .into_iter()
            .map(Boolean::from)
            .collect();
        let work_limbs = [
            UInt64::from_bits(&work_bits[0..64]),
            UInt64::from_bits(&work_bits[64..128]),
            UInt64::from_bits(&work_bits[128..192]),
            UInt64::from_bits(&work_bits[192..256]),
        ];

        // Witness the remainder for this block
        let remainder = AllocatedNum::alloc(cs, || {
            self.remainder.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // TODO: Range check remainder <= target

        // Prepare the 64-bit output limbs, loading remainder into the lower four limbs
        // (so that it is added via UInt64::mul_acc2).
        let remainder_bits: Vec<_> = unpack_fe(cs, &remainder)?
            .into_iter()
            .map(Boolean::from)
            .collect();
        let mut w = [
            UInt64::from_bits(&remainder_bits[0..64]),
            UInt64::from_bits(&remainder_bits[64..128]),
            UInt64::from_bits(&remainder_bits[128..192]),
            UInt64::from_bits(&remainder_bits[192..256]),
            UInt64::constant(0),
            UInt64::constant(0),
            UInt64::constant(0),
            UInt64::constant(0),
        ];

        // u256 x u256 -> u512
        for j in 0..4 {
            let mut k = UInt64::constant(0);
            for i in 0..4 {
                let (t_low, t_high) =
                    target_p1_limbs[i].mul_acc2(cs, &work_limbs[j], &w[i + j], &k)?;
                w[i + j] = t_low;
                k = t_high;
            }
            w[j + 4] = k;
        }

        // Enforce that the result equals 2^256
        cs.enforce_zero(w[0].lc::<_, CS>());
        cs.enforce_zero(w[1].lc::<_, CS>());
        cs.enforce_zero(w[2].lc::<_, CS>());
        cs.enforce_zero(w[3].lc::<_, CS>());
        cs.enforce_zero(w[4].lc::<_, CS>() - CS::ONE);
        cs.enforce_zero(w[5].lc::<_, CS>());
        cs.enforce_zero(w[6].lc::<_, CS>());
        cs.enforce_zero(w[7].lc::<_, CS>());

        // Witness the previous block's chain work
        let prev_chain_work = AllocatedNum::alloc(cs, || {
            self.prev_chain_work
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Compute this block's chain work and expose it as an input
        let chain_work_value = prev_chain_work
            .get_value()
            .and_then(|a| block_work.get_value().and_then(|b| Some(a + b)));
        let chain_work = AllocatedNum::alloc_input(cs, || {
            chain_work_value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce_zero(chain_work.lc() - &prev_chain_work.lc() - &block_work.lc());

        Ok(())
    }
}

fn main() {
    let headers = vec![
        hex!("0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"),
        hex!("010000006fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000982051fd1e4ba744bbbe680e1fee14677ba1a3c3540bf7b1cdb606e857233e0e61bc6649ffff001d01e36299"),
        hex!("010000004860eb18bf1b1620e37e9490fc8a427514416fd75159ab86688e9a8300000000d5fdcc541e25de1c7a5addedf24858b8bb665c9f36ef744ee42c316022c90f9bb0bc6649ffff001d08d2bd61"),
        hex!("01000000bddd99ccfda39da1b108ce1a5d70038d0a967bacb68b6b63065f626a0000000044f672226090d85db9a9f2fbfe5f0f9609b387af7be5b7fbb7a1767c831c9e995dbe6649ffff001d05e0ed6d"),
        hex!("010000004944469562ae1c2c74d9a535e00b6f3e40ffbad4f2fda3895501b582000000007a06ea98cd40ba2e3288262b28638cec5337c1456aaf5eedc8e9e5a20f062bdf8cc16649ffff001d2bfee0a9"),
        hex!("0100000085144a84488ea88d221c8bd6c059da090e88f8a2c99690ee55dbba4e00000000e11c48fecdd9e72510ca84f023370c9a38bf91ac5cae88019bee94d24528526344c36649ffff001d1d03e477"),
        hex!("01000000fc33f596f822a0a1951ffdbf2a897b095636ad871707bf5d3162729b00000000379dfb96a5ea8c81700ea4ac6b97ae9a9312b2d4301a29580e924ee6761a2520adc46649ffff001d189c4c97"),
        hex!("010000008d778fdc15a2d3fb76b7122a3b5582bea4f21f5a0c693537e7a03130000000003f674005103b42f984169c7d008370967e91920a6a5d64fd51282f75bc73a68af1c66649ffff001d39a59c86"),
        hex!("010000004494c8cf4154bdcc0720cd4a59d9c9b285e4b146d45f061d2b6c967100000000e3855ed886605b6d4a99d5fa2ef2e9b0b164e63df3c4136bebf2d0dac0f1f7a667c86649ffff001d1c4b5666"),
        hex!("01000000c60ddef1b7618ca2348a46e868afc26e3efc68226c78aa47f8488c4000000000c997a5e56e104102fa209c6a852dd90660a20b2d9c352423edce25857fcd37047fca6649ffff001d28404f53"),
        hex!("010000000508085c47cc849eb80ea905cc7800a3be674ffc57263cf210c59d8d00000000112ba175a1e04b14ba9e7ea5f76ab640affeef5ec98173ac9799a852fa39add320cd6649ffff001d1e2de565"),
    ];

    let hashes = vec![
        hex!("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"),
        hex!("00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048"),
        hex!("000000006a625f06636b8bb6ac7b960a8d03705d1ace08b1a19da3fdcc99ddbd"),
        hex!("0000000082b5015589a3fdf2d4baff403e6f0be035a5d9742c1cae6295464449"),
        hex!("000000004ebadb55ee9096c9a2f8880e09da59c0d68b1c228da88e48844a1485"),
        hex!("000000009b7262315dbf071787ad3656097b892abffd1f95a1a022f896f533fc"),
        hex!("000000003031a0e73735690c5a1ff2a4be82553b2a12b776fbd3a215dc8f778d"),
        hex!("0000000071966c2b1d065fd446b1e485b2c9d9594acd2007ccbd5441cfc89444"),
        hex!("00000000408c48f847aa786c2268fc3e6ec2af68e8468a34a28c61b7f1de0dc6"),
        hex!("000000008d9dc510f23c2657fc4f67bea30078cc05a90eb89e84cc475c080805"),
        hex!("000000002c05cc2e78923c34df87fd108b22221ac6076c18f3ade378a4d915e9"),
    ];

    let chain_work = vec![
        hex!("0000000000000000000000000000000000000000000000000000000100010001"),
        hex!("0000000000000000000000000000000000000000000000000000000200020002"),
        hex!("0000000000000000000000000000000000000000000000000000000300030003"),
        hex!("0000000000000000000000000000000000000000000000000000000400040004"),
        hex!("0000000000000000000000000000000000000000000000000000000500050005"),
        hex!("0000000000000000000000000000000000000000000000000000000600060006"),
        hex!("0000000000000000000000000000000000000000000000000000000700070007"),
        hex!("0000000000000000000000000000000000000000000000000000000800080008"),
        hex!("0000000000000000000000000000000000000000000000000000000900090009"),
        hex!("0000000000000000000000000000000000000000000000000000000a000a000a"),
        hex!("0000000000000000000000000000000000000000000000000000000b000b000b"),
    ];

    // Remainder is fixed for a given block target
    let remainder = {
        let mut r = hex!("000000000000fffffffffffffffffffffffffffffffffffffffffffefffeffff");
        r.reverse();
        Fp::from_bytes(&r).unwrap()
    };

    let mut prev = (
        -Fp::one(),
        hex!("0000000000000000000000000000000000000000000000000000000000000000"),
        Fp::zero(),
    );

    for (i, ((header, mut hash), mut chain_work)) in headers
        .into_iter()
        .zip(hashes.into_iter())
        .zip(chain_work.into_iter())
        .enumerate()
    {
        hash.reverse();
        chain_work.reverse();

        let height = Fp::from(i as u64);
        let chain_work = Fp::from_bytes(&chain_work).unwrap();

        let mut input = vec![height];
        add_input_bits_for_bytes(&mut input, &hash);
        input.push(chain_work);

        assert_eq!(
            is_satisfied::<_, _, Basic>(
                &BitcoinHeaderCircuit::from_witnesses(header, remainder, prev),
                &input,
            ),
            Ok(true)
        );

        prev = (height, hash, chain_work);
    }
    println!("Valid!");
}
