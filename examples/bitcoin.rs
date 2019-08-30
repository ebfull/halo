#[macro_use]
extern crate hex_literal;

use subsonic::{
    is_satisfied, sha256::sha256, AllocatedBit, AllocatedNum, Basic, Boolean, Circuit, Coeff,
    ConstraintSystem, Fp, LinearCombination, SynthesisError,
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

fn input_bytes_to_bits<CS: ConstraintSystem<Fp>>(
    cs: &mut CS,
    data: &[u8],
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = vec![];

    for (byte_i, byte) in data.iter().enumerate() {
        for bit_i in (0..8).rev() {
            let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

            let value = (byte >> bit_i) & 1u8 == 1u8;
            let alloc_bit = AllocatedBit::alloc(cs, || Ok(value))?;
            let input_bit =
                AllocatedNum::alloc_input(cs, || Ok(if value { Fp::one() } else { Fp::zero() }))?;
            cs.enforce_zero(input_bit.lc() - alloc_bit.get_variable());

            bits.push(alloc_bit.into());
        }
    }

    Ok(bits)
}

fn add_input_bits_for_bytes(input: &mut Vec<Fp>, data: &[u8]) {
    for byte in data.iter() {
        for bit_i in (0..8).rev() {
            let value = (byte >> bit_i) & 1u8 == 1u8;
            input.push(if value { Fp::one() } else { Fp::zero() });
        }
    }
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
    height: Fp,
    header: [u8; 80],
    hash: [u8; 32],
    prev_height: Fp,
    prev_hash: [u8; 32],
}

impl BitcoinHeaderCircuit {
    fn new(height: Fp, header: [u8; 80], hash: [u8; 32], prev: (Fp, [u8; 32])) -> Self {
        BitcoinHeaderCircuit {
            height,
            header,
            hash,
            prev_height: prev.0,
            prev_hash: prev.1,
        }
    }
}

impl Circuit<Fp> for BitcoinHeaderCircuit {
    fn synthesize<CS: ConstraintSystem<Fp>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Witness the previous height
        let prev_height = AllocatedNum::alloc(cs, || Ok(self.prev_height))?;

        // Bring the block height in as an input
        let height = AllocatedNum::alloc_input(cs, || Ok(self.height))?;

        // Enforce that the heights are sequential
        cs.enforce_zero(height.lc() - &prev_height.lc() - CS::ONE);

        // Witness the header
        let header_bits = bytes_to_bits(cs.namespace(|| "header"), &self.header)?;

        // Witness the previous hash
        let prev_bits = bytes_to_bits(cs.namespace(|| "prev"), &self.prev_hash)?;

        // Enforce that header contains the previous hash
        enforce_equality(cs, &header_bits[32..32 + 256], &prev_bits);

        // Compute SHA256d(header)
        let result = {
            let mid = sha256(cs, &header_bits)?;
            sha256(cs, &mid)?
        };

        // Bring the expected hash in as an input
        let hash_bits = input_bytes_to_bits(cs.namespace(|| "hash"), &self.hash)?;
        assert_eq!(result.len(), hash_bits.len());

        // Enforce equality between the computed and expected hash
        enforce_equality(cs, &result, &hash_bits);

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

    let mut prev = (
        -Fp::one(),
        hex!("0000000000000000000000000000000000000000000000000000000000000000"),
    );

    for (i, (header, mut hash)) in headers.into_iter().zip(hashes.into_iter()).enumerate() {
        hash.reverse();

        let height = Fp::from(i as u64);

        let mut input = vec![height];
        add_input_bits_for_bytes(&mut input, &hash);

        assert_eq!(
            is_satisfied::<_, _, Basic>(
                &BitcoinHeaderCircuit::new(height, header, hash, prev),
                &input,
            ),
            Ok(true)
        );

        prev = (height, hash);
    }
    println!("Valid!");
}
