use super::{Curve, CurveAffine};

pub fn pedersen_hash<C: CurveAffine>(bytes: &[u8], generators: &[C]) -> C {
    let mut windows = [C::Projective::zero(); 4];

    for (index, generator) in bytes
        .iter()
        .flat_map(|byte| {
            Some(byte & 0b11).into_iter()
                .chain(Some((byte >> 2) & 0b11u8))
                .chain(Some((byte >> 4) & 0b11u8))
                .chain(Some((byte >> 6) & 0b11u8))
        })
        .map(|a: u8| a as usize)
        .zip(generators.iter())
    {
        windows[index] += *generator;
    }

    let mut acc = windows[0];
    for i in 1..4 {
        let mut val = windows[i];

        match i % 4 {
            0b00 => unreachable!(),
            0b01 => {
                val = val.double();
            }
            0b10 => {
                val = val + &val.double();
            }
            0b11 => {
                val = val.double().double();
            }
            _ => unreachable!(),
        }

        acc = acc + &val;
    }

    acc.to_affine()
}
