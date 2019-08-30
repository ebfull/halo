#[macro_use]
extern crate hex_literal;

use subsonic::{
    is_satisfied, sha256::sha256, AllocatedBit, Basic, Boolean, Circuit, Coeff, ConstraintSystem,
    Fp, LinearCombination, SynthesisError,
};

fn bytes_to_bits<CS: ConstraintSystem<Fp>>(
    cs: &mut CS,
    data: &[u8],
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = vec![];

    for (byte_i, byte) in data.iter().enumerate() {
        for bit_i in (0..8).rev() {
            let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

            bits.push(AllocatedBit::alloc(cs, || Ok((byte >> bit_i) & 1u8 == 1u8))?.into());
        }
    }

    Ok(bits)
}

fn enforce_equality<CS: ConstraintSystem<Fp>>(cs: &mut CS, a: &[Boolean], b: &[Boolean]) {
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

struct BitcoinHeaderCircuit {
    header: [u8; 80],
    hash: [u8; 32],
    prev: [u8; 32],
}

impl BitcoinHeaderCircuit {
    fn new(header: [u8; 80], hash: [u8; 32], prev: [u8; 32]) -> Self {
        BitcoinHeaderCircuit { header, hash, prev }
    }
}

impl Circuit<Fp> for BitcoinHeaderCircuit {
    fn synthesize<CS: ConstraintSystem<Fp>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Witness the header
        let header_bits = bytes_to_bits(cs.namespace(|| "header"), &self.header)?;

        // Witness the previous hash
        let prev_bits = bytes_to_bits(cs.namespace(|| "prev"), &self.prev)?;

        // Enforce that header contains the previous hash
        enforce_equality(cs, &header_bits[32..32 + 256], &prev_bits);

        // Compute SHA256d(header)
        let result = {
            let mid = sha256(cs, &header_bits)?;
            sha256(cs, &mid)?
        };

        // Witness the expected hash
        let hash_bits = bytes_to_bits(cs.namespace(|| "hash"), &self.hash)?;
        assert_eq!(result.len(), hash_bits.len());

        // Enforce equality between the computed and expected hash
        enforce_equality(cs, &result, &hash_bits);

        Ok(())
    }
}

fn main() {
    let genesis_header = hex!("0100000000000000000000000000000000000000000000000000000000000000000000003BA3EDFD7A7B12B27AC72C3E67768F617FC81BC3888A51323A9FB8AA4B1E5E4A29AB5F49FFFF001D1DAC2B7C");

    let mut genesis_hash = hex!("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    genesis_hash.reverse();

    let mut prev_hash = hex!("0000000000000000000000000000000000000000000000000000000000000000");
    prev_hash.reverse();

    assert_eq!(
        is_satisfied::<_, _, Basic>(
            &BitcoinHeaderCircuit::new(genesis_header, genesis_hash, prev_hash),
            &[]
        ),
        Ok(true)
    );
    println!("Valid!");
}
