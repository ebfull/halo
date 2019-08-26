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

struct AllocatedNum<F: Field>(Variable, Option<F>);

impl<F: Field> AllocatedNum<F> {
    fn get_value(&self) -> &Option<F> {
        &self.1
    }

    fn get_var(&self) -> Variable {
        self.0
    }

    fn alloc<CS: ConstraintSystem<F>, FF: Fn() -> Result<F, SynthesisError>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<Self, SynthesisError> {
        let value = value();
        let var = cs.alloc(|| value)?;
        let value = value.ok();

        Ok(AllocatedNum(var, value))
    }

    fn alloc_input<CS: ConstraintSystem<F>, FF: Fn() -> Result<F, SynthesisError>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<Self, SynthesisError> {
        let value = value();
        let var = cs.alloc_input(|| value)?;
        let value = value.ok();

        Ok(AllocatedNum(var, value))
    }

    fn alloc_and_square<CS: ConstraintSystem<F>, FF: Fn() -> Result<F, SynthesisError>>(
        cs: &mut CS,
        value: FF,
    ) -> Result<(Self, Self, Self), SynthesisError> {
        let value = value();
        let mut square_value = None;
        let (a, b, c) = cs.multiply(|| {
            let value = value?;
            square_value = Some(value.square());
            Ok((value, value, square_value.unwrap()))
        })?;
        let value = value.ok();

        cs.enforce_zero(LinearCombination::from(a) - b);

        Ok((
            AllocatedNum(a, value),
            AllocatedNum(b, value),
            AllocatedNum(c, square_value),
        ))
    }

    fn enforce_equal<CS: ConstraintSystem<F>>(&self, cs: &mut CS, lc: LinearCombination<F>) {
        cs.enforce_zero(lc - self.0);
    }

    fn multiply<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let value = self.1.and_then(|a| other.1.and_then(|b| Some(a * b)));

        let (a, b, c) = cs.multiply(|| {
            Ok((
                self.1.ok_or(SynthesisError::AssignmentMissing)?,
                other.1.ok_or(SynthesisError::AssignmentMissing)?,
                value.ok_or(SynthesisError::AssignmentMissing)?,
            ))
        })?;

        cs.enforce_zero(LinearCombination::from(a) - self.0);
        cs.enforce_zero(LinearCombination::from(b) - other.0);

        Ok(AllocatedNum(c, value))
    }

    fn square<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let sq_value = self.1.map(|v| v.square());

        let (a, b, c) = cs.multiply(|| {
            let value = self.1.ok_or(SynthesisError::AssignmentMissing)?;
            Ok((
                value,
                value,
                sq_value.ok_or(SynthesisError::AssignmentMissing)?,
            ))
        })?;

        cs.enforce_zero(LinearCombination::from(self.0) - a);
        cs.enforce_zero(LinearCombination::from(a) - b);

        Ok(AllocatedNum(c, sq_value))
    }
}

fn point_double<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    x: AllocatedNum<F>,
    y: AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
    /*
        \lambda * (2y)          = (3*x^2)
        \lambda * \lambda  - 2x = x'
        \lambda * (x - x') - y  = y'
    */
    let x2 = x.square(cs)?;
    let (lambda1, lambda2, lambdasq) = AllocatedNum::<F>::alloc_and_square(cs, || {
        let tmp = x2.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let tmp = tmp * F::from_u64(3);
        let y_value = y.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let tmp = tmp * ((y_value + y_value).invert().unwrap());

        Ok(tmp)
    })?;
    {
        // \lambda * (2y)          = (3*x^2)
        let (a, b, c) = cs.multiply(|| {
            let y2 = y.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let y2 = y2 + y2;
            let rhs = x2.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let rhs = F::from_u64(3) * rhs;

            Ok((
                lambda1
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?,
                y2,
                rhs,
            ))
        })?;
        cs.enforce_zero(LinearCombination::from(a) - lambda1.get_var());
        cs.enforce_zero(LinearCombination::from(b) - (Coeff::Full(F::from_u64(2)), y.get_var()));
        cs.enforce_zero(LinearCombination::from(c) - (Coeff::Full(F::from_u64(3)), x2.get_var()));
    }
    let x_prime = AllocatedNum::<F>::alloc(cs, || {
        let tmp = lambdasq
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let x_value = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;

        Ok(tmp - x_value - x_value)
    })?;
    // \lambda * \lambda  - 2x = x'
    lambdasq.enforce_equal(
        cs,
        LinearCombination::<F>::from(x_prime.get_var())
            + (Coeff::Full(F::from_u64(2)), x.get_var()),
    );
    // \lambda * (x - x') - y  = y'
    let y_prime = AllocatedNum::<F>::alloc(cs, || {
        let tmp = x_prime
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let tmp = x.get_value().ok_or(SynthesisError::AssignmentMissing)? - tmp;
        let tmp = lambda1
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
            * tmp;
        let tmp = tmp - y.get_value().ok_or(SynthesisError::AssignmentMissing)?;

        Ok(tmp)
    })?;
    {
        let (a, b, c) = cs.multiply(|| {
            let tmp = x_prime
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let b = x.get_value().ok_or(SynthesisError::AssignmentMissing)? - tmp;
            let tmp = y_prime
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let tmp = tmp + y.get_value().ok_or(SynthesisError::AssignmentMissing)?;

            Ok((
                lambda1
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?,
                b,
                tmp,
            ))
        })?;
        cs.enforce_zero(LinearCombination::<F>::from(lambda2.get_var()) - a);
        cs.enforce_zero((LinearCombination::<F>::from(x.get_var()) - x_prime.get_var()) - b);
        cs.enforce_zero((LinearCombination::<F>::from(y_prime.get_var()) + y.get_var()) - c);
    }

    Ok((x_prime, y_prime))
}

struct MyCircuit<F: Field> {
    x_input: Option<F>,
    y_input: Option<F>,
    x_output: Option<F>,
    y_output: Option<F>,
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        /*
            \lambda * (2y)          = (3*x^2)
            \lambda * \lambda  - 2x = x'
            \lambda * (x - x') - y  = y'
        */
        let x_input = AllocatedNum::alloc_input(cs, || {
            self.x_input.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_input = AllocatedNum::alloc_input(cs, || {
            self.y_input.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let (x, y) = point_double(cs, x_input, y_input)?;
        let (x, y) = point_double(cs, x, y)?;
        let (x, y) = point_double(cs, x, y)?;

        let x_output = AllocatedNum::alloc_input(cs, || {
            self.x_output.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_output = AllocatedNum::alloc_input(cs, || {
            self.y_output.ok_or(SynthesisError::AssignmentMissing)
        })?;

        x_output.enforce_equal(cs, LinearCombination::from(x.get_var()));
        y_output.enforce_equal(cs, LinearCombination::from(y.get_var()));

        Ok(())
    }
}

fn main() {
    let circuit = MyCircuit {
        x_input: Some(Fp::from_raw([
            0xdb6e8b6dfcb425f4,
            0xdb9d7c6884110585,
            0xe5af8e2b94293c57,
            0x110ec8ac0520acff,
        ])),
        y_input: Some(Fp::from_raw([
            0xb8726fb5ec64ef71,
            0xf91065bebc57cd04,
            0x7181d0ce926fb19e,
            0x4144b4a744fc23a9,
        ])),
        x_output: Some(Fp::from_raw([
            0xde5c85c0439fc8ed,
            0x1695fafd1a8c5d8a,
            0x3cc56d62335791f8,
            0x34a1874282f601bc,
        ])),
        y_output: Some(Fp::from_raw([
            0x78373da05adf8c08,
            0x7af422acb2d02b18,
            0x5621168cb14bddb5,
            0x8da4ddf78a0bac9,
        ])),
    };

    assert!(is_satisfied::<Fp, _, Basic>(
        &circuit,
        &[
            Fp::from_raw([
                0xdb6e8b6dfcb425f4,
                0xdb9d7c6884110585,
                0xe5af8e2b94293c57,
                0x110ec8ac0520acff
            ]),
            Fp::from_raw([
                0xb8726fb5ec64ef71,
                0xf91065bebc57cd04,
                0x7181d0ce926fb19e,
                0x4144b4a744fc23a9
            ]),
            Fp::from_raw([
                0xde5c85c0439fc8ed,
                0x1695fafd1a8c5d8a,
                0x3cc56d62335791f8,
                0x34a1874282f601bc
            ]),
            Fp::from_raw([
                0x78373da05adf8c08,
                0x7af422acb2d02b18,
                0x5621168cb14bddb5,
                0x8da4ddf78a0bac9
            ])
        ]
    )
    .unwrap());
}
