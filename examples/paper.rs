use std::time::Instant;

extern crate halo;

use halo::*;

trait OptionExt<T> {
    fn open(self) -> Result<T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn open(self) -> Result<T, SynthesisError> {
        self.ok_or(SynthesisError::AssignmentMissing)
    }
}

struct MyCircuit;

impl<F: Field> Circuit<F> for MyCircuit {
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        cs.multiply(|| Ok((F::from_u64(10), F::from_u64(10), F::from_u64(100))))?;

        Ok(())
    }
}

fn main() {
    println!("Making parameters");
    let start = Instant::now();
    let params0: Params<Ec0> = Params::new(21);
    let params1: Params<Ec1> = Params::new(21);
    println!("done, took {:?}", start.elapsed());

    let mycircuit = MyCircuit;

    println!("creating proof1");
    let start = Instant::now();
    let proof1 =
        RecursiveProof::<Ec1, Ec0>::create_proof(&params1, &params0, None, &mycircuit, &[])
            .unwrap();
    println!("done, took {:?}", start.elapsed());

    println!("verifying proof1");
    let start = Instant::now();
    assert!(proof1.verify(&params1, &params0, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());

    println!("creating proof2");
    let start = Instant::now();
    let proof2 = RecursiveProof::<Ec0, Ec1>::create_proof(
        &params0,
        &params1,
        Some(&proof1),
        &mycircuit,
        &[],
    )
    .unwrap();
    println!("done, took {:?}", start.elapsed());

    println!("verifying proof2");
    let start = Instant::now();
    assert!(proof2.verify(&params0, &params1, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());

    println!("creating proof3");
    let start = Instant::now();
    let proof3 = RecursiveProof::<Ec1, Ec0>::create_proof(
        &params1,
        &params0,
        Some(&proof2),
        &mycircuit,
        &[],
    )
    .unwrap();
    println!("done, took {:?}", start.elapsed());

    println!("verifying proof3");
    let start = Instant::now();
    assert!(proof3.verify(&params1, &params0, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());

    println!("creating proof4");
    let start = Instant::now();
    let proof4 = RecursiveProof::<Ec0, Ec1>::create_proof(
        &params0,
        &params1,
        Some(&proof3),
        &mycircuit,
        &[],
    )
    .unwrap();
    println!("done, took {:?}", start.elapsed());

    println!("verifying proof4");
    let start = Instant::now();
    assert!(proof4.verify(&params0, &params1, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());

    println!("creating proof5");
    let start = Instant::now();
    let proof5 = RecursiveProof::<Ec1, Ec0>::create_proof(
        &params1,
        &params0,
        Some(&proof4),
        &mycircuit,
        &[],
    )
    .unwrap();
    println!("done, took {:?}", start.elapsed());

    println!("verifying proof5");
    let start = Instant::now();
    assert!(proof5.verify(&params1, &params0, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());
}
