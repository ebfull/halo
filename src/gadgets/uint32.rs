use crate::{fields::Field, Coeff, ConstraintSystem, LinearCombination, SynthesisError};

use super::boolean::{AllocatedBit, Boolean};

/// Represents an interpretation of 32 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone)]
pub struct UInt32 {
    // Least significant bit first
    bits: Vec<Boolean>,
    value: Option<u32>,
}

impl UInt32 {
    /// Construct a constant `UInt32` from a `u32`
    pub fn constant(value: u32) -> Self {
        let mut bits = Vec::with_capacity(32);

        let mut tmp = value;
        for _ in 0..32 {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        UInt32 {
            bits,
            value: Some(value),
        }
    }

    /// Allocate a `UInt32` in the constraint system
    pub fn alloc<F, CS>(cs: &mut CS, value: Option<u32>) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(32);

                for _ in 0..32 {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            }
            None => vec![None; 32],
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

        Ok(UInt32 { bits, value })
    }

    pub fn into_bits_be(self) -> Vec<Boolean> {
        let mut ret = self.bits;
        ret.reverse();
        ret
    }

    pub fn from_bits_be(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 32);

        let mut value = Some(0u32);
        for b in bits {
            value.as_mut().map(|v| *v <<= 1);

            match b.get_value() {
                Some(true) => {
                    value.as_mut().map(|v| *v |= 1);
                }
                Some(false) => {}
                None => {
                    value = None;
                }
            }
        }

        UInt32 {
            value,
            bits: bits.iter().rev().cloned().collect(),
        }
    }

    /// Turns this `UInt32` into its little-endian byte order representation.
    pub fn into_bits(self) -> Vec<Boolean> {
        self.bits
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt32`.
    pub fn from_bits(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 32);

        let new_bits = bits.to_vec();

        let mut value = Some(0u32);
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

        UInt32 {
            value,
            bits: new_bits,
        }
    }

    pub fn rotr(&self, by: usize) -> Self {
        let by = by % 32;

        let new_bits = self
            .bits
            .iter()
            .skip(by)
            .chain(self.bits.iter())
            .take(32)
            .cloned()
            .collect();

        UInt32 {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32)),
        }
    }

    pub fn shr(&self, by: usize) -> Self {
        let by = by % 32;

        let fill = Boolean::constant(false);

        let new_bits = self
            .bits
            .iter() // The bits are least significant first
            .skip(by) // Skip the bits that will be lost during the shift
            .chain(Some(&fill).into_iter().cycle()) // Rest will be zeros
            .take(32) // Only 32 bits needed!
            .cloned()
            .collect();

        UInt32 {
            bits: new_bits,
            value: self.value.map(|v| v >> by as u32),
        }
    }

    fn triop<F, CS, FF, U>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &Self,
        tri_fn: FF,
        circuit_fn: U,
    ) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
        FF: Fn(u32, u32, u32) -> u32,
        U: Fn(&mut CS, usize, &Boolean, &Boolean, &Boolean) -> Result<Boolean, SynthesisError>,
    {
        let new_value = match (a.value, b.value, c.value) {
            (Some(a), Some(b), Some(c)) => Some(tri_fn(a, b, c)),
            _ => None,
        };

        let bits = a
            .bits
            .iter()
            .zip(b.bits.iter())
            .zip(c.bits.iter())
            .enumerate()
            .map(|(i, ((a, b), c))| circuit_fn(cs, i, a, b, c))
            .collect::<Result<_, _>>()?;

        Ok(UInt32 {
            bits,
            value: new_value,
        })
    }

    /// Compute the `maj` value (a and b) xor (a and c) xor (b and c)
    /// during SHA256.
    pub fn sha256_maj<F, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        Self::triop(
            cs,
            a,
            b,
            c,
            |a, b, c| (a & b) ^ (a & c) ^ (b & c),
            |cs, i, a, b, c| Boolean::sha256_maj(cs.namespace(|| format!("maj {}", i)), a, b, c),
        )
    }

    /// Compute the `ch` value `(a and b) xor ((not a) and c)`
    /// during SHA256.
    pub fn sha256_ch<F, CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        Self::triop(
            cs,
            a,
            b,
            c,
            |a, b, c| (a & b) ^ ((!a) & c),
            |cs, i, a, b, c| Boolean::sha256_ch(cs.namespace(|| format!("ch {}", i)), a, b, c),
        )
    }

    /// XOR this `UInt32` with another `UInt32`
    pub fn xor<F, CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a ^ b),
            _ => None,
        };

        let bits = self
            .bits
            .iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| Boolean::xor(cs.namespace(|| format!("xor of bit {}", i)), a, b))
            .collect::<Result<_, _>>()?;

        Ok(UInt32 {
            bits,
            value: new_value,
        })
    }

    /// Perform modular addition of several `UInt32` objects.
    pub fn addmany<F, CS>(cs: &mut CS, operands: &[Self]) -> Result<Self, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
    {
        // Make some arbitrary bounds for ourselves to avoid overflows
        // in the scalar field
        assert!(F::NUM_BITS >= 64);
        assert!(operands.len() >= 2); // Weird trivial cases that should never happen
        assert!(operands.len() <= 10);

        // Compute the maximum value of the sum so we allocate enough bits for
        // the result
        let mut max_value = (operands.len() as u64) * (u64::from(u32::max_value()));

        // Keep track of the resulting value
        let mut result_value = Some(0u64);

        // This is a linear combination that we will enforce to equal the
        // output
        let mut lc = LinearCombination::zero();

        let mut all_constants = true;

        // Iterate over the operands
        for op in operands {
            // Accumulate the value
            match op.value {
                Some(val) => {
                    result_value.as_mut().map(|v| *v += u64::from(val));
                }
                None => {
                    // If any of our operands have unknown value, we won't
                    // know the value of the result
                    result_value = None;
                }
            }

            // Iterate over each bit of the operand and add the operand to
            // the linear combination
            let mut coeff = Coeff::One;
            for bit in &op.bits {
                lc = lc + &bit.lc(CS::ONE, coeff);

                all_constants &= bit.is_constant();

                coeff = coeff.double();
            }
        }

        // The value of the actual result is modulo 2^32
        let modular_value = result_value.map(|v| v as u32);

        if all_constants && modular_value.is_some() {
            // We can just return a constant, rather than
            // unpacking the result into allocated bits.

            return Ok(UInt32::constant(modular_value.unwrap()));
        }

        // Storage area for the resulting bits
        let mut result_bits = vec![];

        // Linear combination representing the output,
        // for comparison with the sum of the operands
        let mut result_lc = LinearCombination::zero();

        // Allocate each bit of the result
        let mut coeff = Coeff::One;
        let mut i = 0;
        while max_value != 0 {
            // Allocate the bit
            let b = AllocatedBit::alloc(cs.namespace(|| format!("result bit {}", i)), || {
                result_value
                    .map(|v| (v >> i) & 1 == 1)
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;

            // Add this bit to the result combination
            result_lc = result_lc + (coeff, b.get_variable());

            result_bits.push(b.into());

            max_value >>= 1;
            i += 1;
            coeff = coeff.double();
        }

        // Enforce equality between the sum and result
        cs.enforce_zero(lc - &result_lc);

        // Discard carry bits that we don't care about
        result_bits.truncate(32);

        Ok(UInt32 {
            bits: result_bits,
            value: modular_value,
        })
    }
}

#[cfg(test)]
mod test {
    use super::UInt32;
    use crate::{
        circuits::Circuit, fields::Fp, gadgets::boolean::Boolean, is_satisfied, Basic,
        ConstraintSystem, SynthesisError,
    };
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_uint32_from_bits_be() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let v = (0..32)
                .map(|_| Boolean::constant(rng.next_u32() % 2 != 0))
                .collect::<Vec<_>>();

            let b = UInt32::from_bits_be(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match *bit {
                    Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    }
                    _ => unreachable!(),
                }
            }

            let expected_to_be_same = b.into_bits_be();

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
    fn test_uint32_from_bits() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let v = (0..32)
                .map(|_| Boolean::constant(rng.next_u32() % 2 != 0))
                .collect::<Vec<_>>();

            let b = UInt32::from_bits(&v);

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
    fn test_uint32_xor() {
        struct TestCircuit {
            a: u32,
            b: u32,
            c: u32,
        };

        impl TestCircuit {
            fn new(rng: &mut XorShiftRng) -> Self {
                TestCircuit {
                    a: rng.next_u32(),
                    b: rng.next_u32(),
                    c: rng.next_u32(),
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut expected = self.a ^ self.b ^ self.c;

                let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(self.a))?;
                let b_bit = UInt32::constant(self.b);
                let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(self.c))?;

                let r = a_bit.xor(cs.namespace(|| "first xor"), &b_bit)?;
                let r = r.xor(cs.namespace(|| "second xor"), &c_bit)?;

                assert!(r.value == Some(expected));

                for b in r.bits.iter() {
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

    #[test]
    fn test_uint32_addmany_constants() {
        struct TestCircuit {
            a: u32,
            b: u32,
            c: u32,
        };

        impl TestCircuit {
            fn new(rng: &mut XorShiftRng) -> Self {
                TestCircuit {
                    a: rng.next_u32(),
                    b: rng.next_u32(),
                    c: rng.next_u32(),
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a_bit = UInt32::constant(self.a);
                let b_bit = UInt32::constant(self.b);
                let c_bit = UInt32::constant(self.c);

                let mut expected = self.a.wrapping_add(self.b).wrapping_add(self.c);

                let r = UInt32::addmany(cs.namespace(|| "addition"), &[a_bit, b_bit, c_bit])?;

                assert!(r.value == Some(expected));

                for b in r.bits.iter() {
                    match *b {
                        Boolean::Is(_) => panic!(),
                        Boolean::Not(_) => panic!(),
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

    #[test]
    fn test_uint32_addmany() {
        struct TestCircuit {
            a: u32,
            b: u32,
            c: u32,
            d: u32,
        };

        impl TestCircuit {
            fn new(rng: &mut XorShiftRng) -> Self {
                TestCircuit {
                    a: rng.next_u32(),
                    b: rng.next_u32(),
                    c: rng.next_u32(),
                    d: rng.next_u32(),
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut expected = (self.a ^ self.b).wrapping_add(self.c).wrapping_add(self.d);

                let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(self.a))?;
                let b_bit = UInt32::constant(self.b);
                let c_bit = UInt32::constant(self.c);
                let d_bit = UInt32::alloc(cs.namespace(|| "d_bit"), Some(self.d))?;

                let r = a_bit.xor(cs.namespace(|| "xor"), &b_bit)?;
                let r = UInt32::addmany(cs.namespace(|| "addition"), &[r, c_bit, d_bit])?;

                assert!(r.value == Some(expected));

                for b in r.bits.iter() {
                    match *b {
                        Boolean::Is(ref b) => {
                            assert!(b.get_value().unwrap() == (expected & 1 == 1));
                        }
                        Boolean::Not(ref b) => {
                            assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                        }
                        Boolean::Constant(_) => unreachable!(),
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

    #[test]
    fn test_uint32_rotr() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut num = rng.next_u32();

        let a = UInt32::constant(num);

        for i in 0..32 {
            let b = a.rotr(i);
            assert_eq!(a.bits.len(), b.bits.len());

            assert!(b.value.unwrap() == num);

            let mut tmp = num;
            for b in &b.bits {
                match *b {
                    Boolean::Constant(b) => {
                        assert_eq!(b, tmp & 1 == 1);
                    }
                    _ => unreachable!(),
                }

                tmp >>= 1;
            }

            num = num.rotate_right(1);
        }
    }

    #[test]
    fn test_uint32_shr() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..50 {
            for i in 0..60 {
                let num = rng.next_u32();
                let a = UInt32::constant(num).shr(i);
                let b = UInt32::constant(num.wrapping_shr(i as u32));

                assert_eq!(a.value.unwrap(), num.wrapping_shr(i as u32));

                assert_eq!(a.bits.len(), b.bits.len());
                for (a, b) in a.bits.iter().zip(b.bits.iter()) {
                    assert_eq!(a.get_value().unwrap(), b.get_value().unwrap());
                }
            }
        }
    }

    #[test]
    fn test_uint32_sha256_maj() {
        struct TestCircuit {
            a: u32,
            b: u32,
            c: u32,
        };

        impl TestCircuit {
            fn new(rng: &mut XorShiftRng) -> Self {
                TestCircuit {
                    a: rng.next_u32(),
                    b: rng.next_u32(),
                    c: rng.next_u32(),
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut expected = (self.a & self.b) ^ (self.a & self.c) ^ (self.b & self.c);

                let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(self.a))?;
                let b_bit = UInt32::constant(self.b);
                let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(self.c))?;

                let r = UInt32::sha256_maj(cs, &a_bit, &b_bit, &c_bit)?;

                assert!(r.value == Some(expected));

                for b in r.bits.iter() {
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

    #[test]
    fn test_uint32_sha256_ch() {
        struct TestCircuit {
            a: u32,
            b: u32,
            c: u32,
        };

        impl TestCircuit {
            fn new(rng: &mut XorShiftRng) -> Self {
                TestCircuit {
                    a: rng.next_u32(),
                    b: rng.next_u32(),
                    c: rng.next_u32(),
                }
            }
        }

        impl Circuit<Fp> for TestCircuit {
            fn synthesize<CS: ConstraintSystem<Fp>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let mut expected = (self.a & self.b) ^ ((!self.a) & self.c);

                let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(self.a))?;
                let b_bit = UInt32::constant(self.b);
                let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(self.c))?;

                let r = UInt32::sha256_ch(cs, &a_bit, &b_bit, &c_bit)?;

                assert!(r.value == Some(expected));

                for b in r.bits.iter() {
                    match b {
                        Boolean::Is(ref b) => {
                            assert!(b.get_value().unwrap() == (expected & 1 == 1));
                        }
                        Boolean::Not(ref b) => {
                            assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                        }
                        &Boolean::Constant(b) => {
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
