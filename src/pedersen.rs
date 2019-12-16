use super::{Curve, CurveAffine, Field};

pub fn pedersen_hash<C: CurveAffine>(bytes: &[u8], generators: &[C]) -> C {
    let mut windows = [C::Projective::zero(); 16];

    for (index, generator) in bytes
        .iter()
        .flat_map(|byte| Some(byte & 0b1111).into_iter().chain(Some(byte >> 4)))
        .map(|a: u8| a as usize)
        .zip(generators.iter())
    {
        windows[index] += *generator;
    }

    let mut acc = C::Projective::zero();
    for i in 0..16 {
        let mut val = windows[i];

        match i % 4 {
            0b00 => {}
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

        if i & 0b0100 != 0 {
            val = -val;
        }

        if i & 0b1000 != 0 {
            val = val.endo();
        }

        acc = acc + &val;
    }

    acc.to_affine()
}