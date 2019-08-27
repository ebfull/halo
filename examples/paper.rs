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
        cs.multiply(|| {
            Ok((F::from_u64(10),
            F::from_u64(10),
            F::from_u64(100)))
        })?;

        Ok(())
    }
}

fn main() {
    let params1: RecursiveParameters<Ec1, Ec0> = RecursiveParameters::new(11);
    let params2: RecursiveParameters<Ec0, Ec1> = params1.clone().switch();

    let mycircuit = MyCircuit;

    let proof0 = RecursiveProof::<Ec0, Ec1>::create_false_proof();

    // will fail eventually
    assert!(proof0.verify_proof(&params2, &mycircuit, &[]).unwrap());

    let proof1 = RecursiveProof::<Ec1, Ec0>::create_proof(
        &params1,
        &proof0,
        &mycircuit,
        &[],
        &[]
    ).unwrap();

    // assert!(proof1.verify_proof(&params1, &mycircuit, &[]).unwrap());

    // let proof2 = RecursiveProof::<Ec0, Ec1>::create_proof(
    //     &params2,
    //     &proof1,
    //     &mycircuit,
    //     &[],
    //     &[]
    // ).unwrap();

    // assert!(proof2.verify_proof(&params2, &mycircuit, &[]).unwrap());

    // let proof3 = RecursiveProof::<Ec1, Ec0>::create_proof(
    //     &params1,
    //     &proof2,
    //     &mycircuit,
    //     &[],
    //     &[]
    // ).unwrap();

    // assert!(proof3.verify_proof(&params1, &mycircuit, &[]).unwrap());
}
