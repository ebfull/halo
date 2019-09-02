use std::time::Instant;

extern crate subsonic;

use subsonic::*;

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
    let params0: Params<Ec0> = Params::new(15);
    let params1: Params<Ec1> = Params::new(15);
    println!("done");

    let mycircuit = MyCircuit;

    let proof1 = RecursiveProof::<Ec1, Ec0>::create_proof(&params1, &params0, None, &mycircuit, &[]).unwrap();

    assert!(proof1.verify(&params1, &params0, &mycircuit).unwrap());

    let proof2 =
        RecursiveProof::<Ec0, Ec1>::create_proof(&params0, &params1, Some(&proof1), &mycircuit, &[]).unwrap();

    println!("verifying...");
    
    let start = Instant::now();
    assert!(proof2.verify(&params0, &params1, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());

    let proof3 =
        RecursiveProof::<Ec1, Ec0>::create_proof(&params1, &params0, Some(&proof2), &mycircuit, &[]).unwrap();
    
    println!("verifying...");
    let start = Instant::now();
    assert!(proof3.verify(&params1, &params0, &mycircuit).unwrap());
    println!("done, took {:?}", start.elapsed());
}
