use crate::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Leftovers<C: Curve> {
    pub s_new_commitment: C,
    pub y_new: C::Scalar,
    pub g_new: C,
    pub challenges_new: Vec<C::Scalar>,
}

impl<C: Curve> Leftovers<C> {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut ret = vec![];

        ret.extend(self.s_new_commitment.to_bytes()[..].iter().cloned());
        ret.extend(self.y_new.to_bytes()[..].iter().cloned());
        ret.extend(self.g_new.to_bytes()[..].iter().cloned());
        for challenge in &self.challenges_new {
            ret.extend(challenge.to_bytes()[..].iter().cloned());
        }

        ret
    }

    /// Creates a phony instance of metadata from a "previous"
    /// proof that never existed; used to bootstrap the cycle.
    pub fn dummy(params: &Params<C>) -> Leftovers<C> {
        let y_new = C::Scalar::zero();
        let s_new_commitment = C::zero();
        let challenges_new = vec![C::Scalar::one(); params.k];
        let g_new =
            compute_g_for_inner_product(&params.generators, &challenges_new, C::Scalar::one());

        Leftovers {
            s_new_commitment,
            y_new,
            g_new,
            challenges_new,
        }
    }

    /// Fully verifies the proof cycle
    pub fn verify<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        params: &Params<C>,
        circuit: &CS,
    ) -> Result<bool, SynthesisError> {
        let sx = params.compute_sx::<_, S>(circuit, self.y_new)?;
        let s_new_commitment = params.commit(&sx, false);
        let mut challenges_sq = self.challenges_new.clone();
        assert_eq!(challenges_sq.len(), params.k);
        let mut allinv = C::Scalar::one();
        for c in &mut challenges_sq {
            allinv = allinv * &(*c);
            *c = c.square();
        }
        allinv = allinv.invert().unwrap();
        let g_new = compute_g_for_inner_product(&params.generators, &challenges_sq, allinv);

        Ok((g_new == self.g_new) && (s_new_commitment == self.s_new_commitment))
    }
}

#[derive(Clone)]
pub struct Proof<C: Curve> {
    // Commitments
    pub r_commitment: C,
    pub s_cur_commitment: C,
    pub t_positive_commitment: C,
    pub t_negative_commitment: C,
    pub c_commitment: C,
    pub s_new_commitment: C,

    // Openings
    pub rx_opening: C::Scalar,
    pub rxy_opening: C::Scalar,
    pub sx_old_opening: C::Scalar,
    pub sx_cur_opening: C::Scalar,
    pub tx_positive_opening: C::Scalar,
    pub tx_negative_opening: C::Scalar,
    pub sx_new_opening: C::Scalar,

    // Inner product proof
    pub inner_product: MultiPolynomialOpening<C>,
}

impl<C: Curve> Proof<C> {
    pub fn new<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        params: &Params<C>,
        circuit: &CS,
        old_leftovers: &Leftovers<C>,
    ) -> Result<(Proof<C>, Leftovers<C>), SynthesisError> {
        struct Assignment<F: Field> {
            n: usize,
            q: usize,
            a: Vec<F>,
            b: Vec<F>,
            c: Vec<F>,
            inputs: Vec<(usize, F)>,
        }

        impl<'a, F: Field> Backend<F> for &'a mut Assignment<F> {
            type LinearConstraintIndex = usize;

            fn get_var(&self, var: Variable) -> Option<F> {
                Some(match var {
                    Variable::A(index) => self.a[index - 1],
                    Variable::B(index) => self.b[index - 1],
                    Variable::C(index) => self.c[index - 1],
                })
            }

            fn set_var<FF>(&mut self, var: Variable, value: FF) -> Result<(), SynthesisError>
            where
                FF: FnOnce() -> Result<F, SynthesisError>,
            {
                let value = value()?;

                match var {
                    Variable::A(index) => {
                        self.a[index - 1] = value;
                    }
                    Variable::B(index) => {
                        self.b[index - 1] = value;
                    }
                    Variable::C(index) => {
                        self.c[index - 1] = value;
                    }
                }

                Ok(())
            }

            fn new_multiplication_gate(&mut self) {
                self.n += 1;
                self.a.push(F::zero());
                self.b.push(F::zero());
                self.c.push(F::zero());
            }

            fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex {
                self.q += 1;
                self.q
            }

            fn insert_coefficient(
                &mut self,
                _var: Variable,
                _coeff: Coeff<F>,
                _y: &Self::LinearConstraintIndex,
            ) {

            }

            /// Compute a `LinearConstraintIndex` from `q`.
            fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
                q
            }

            /// Mark y^{_index} as the power of y cooresponding to the public input
            /// coefficient for the next public input, in the k(Y) polynomial.
            fn new_k_power(
                &mut self,
                index: usize,
                value: Option<F>,
            ) -> Result<(), SynthesisError> {
                self.inputs
                    .push((index, value.ok_or(SynthesisError::AssignmentMissing)?));

                Ok(())
            }
        }

        let mut assignment = Assignment::<C::Scalar> {
            n: 0,
            q: 0,
            a: vec![],
            b: vec![],
            c: vec![],
            inputs: vec![],
        };

        S::synthesize(&mut assignment, circuit)?;

        assert!(assignment.n < params.n);
        assert!(assignment.q < params.d);

        assignment.a.resize(params.n, C::Scalar::zero());
        assignment.b.resize(params.n, C::Scalar::zero());
        assignment.c.resize(params.n, C::Scalar::zero());

        let transcript = C::Base::zero();

        // Compute s(X, y_old)
        let y_old = old_leftovers.y_new;
        let sx_old = params.compute_sx::<_, S>(circuit, y_old)?;

        // Get s(X, y_old)
        let s_old_commitment = old_leftovers.s_new_commitment;

        // Compute the coefficients for G_old
        let challenges_old_sq: Vec<C::Scalar> = old_leftovers
            .challenges_new
            .iter()
            .map(|a| a.square())
            .collect();
        let mut challenges_old_inv = old_leftovers.challenges_new.clone();
        for c in &mut challenges_old_inv {
            *c = c.invert().unwrap();
        }
        let mut allinv_old = C::Scalar::one();
        for c in &old_leftovers.challenges_new {
            allinv_old *= &c.invert().unwrap();
        }
        let gx_old = compute_g_coeffs_for_inner_product(&challenges_old_sq, allinv_old);

        // Get G_old
        let g_old_commitment = old_leftovers.g_new;

        // Compute k(Y)
        let mut ky = vec![];
        ky.push(C::Scalar::zero());
        for (index, value) in assignment.inputs {
            ky.resize(index + 1, C::Scalar::zero());
            ky[index] = value;
        }

        // Commit to k(Y)
        let k_commitment = params.commit(&ky, false);
        let transcript = append_point::<C>(transcript, &k_commitment);

        // Compute r(X, Y)
        let mut rx = Vec::with_capacity(3 * params.n + 1);
        rx.extend(assignment.c.into_iter().rev());
        rx.extend(assignment.b.into_iter().rev());
        rx.push(C::Scalar::zero());
        rx.extend(assignment.a.into_iter());
        assert_eq!(rx.len(), 3 * params.n + 1);

        // Commit to r(X, Y)
        let r_commitment = params.commit(&rx, true);
        let transcript = append_point::<C>(transcript, &r_commitment);

        // Obtain the challenge y_cur
        let (transcript, y_cur) = get_challenge::<_, C::Scalar>(transcript);
        let y_cur_inv = y_cur.invert().unwrap();

        // Compute s(X, y_cur)
        let sx_cur = params.compute_sx::<_, S>(circuit, y_cur)?;

        // Commit to s(X, y_cur)
        let s_cur_commitment = params.commit(&sx_cur, false);
        let transcript = append_point::<C>(transcript, &s_cur_commitment);

        // Compute r(X, y_cur)
        let mut rxy = rx.clone();
        {
            let mut cur = y_cur.pow(&[params.n as u64, 0, 0, 0]);
            for coefficient in rxy.iter_mut().rev() {
                *coefficient *= &cur;
                cur = cur * &y_cur_inv;
            }
        }

        // Compute s'(X, y_cur)
        let mut s_primex = sx_cur.clone();
        {
            let yn = y_cur.pow(&[params.n as u64, 0, 0, 0]);
            for coefficient in &mut s_primex {
                *coefficient *= &yn;
            }

            let mut cur_positive = y_cur;
            let mut cur_negative = y_cur_inv;
            assert_eq!(s_primex[((2 * params.n) + 1)..].len(), params.n);
            for coefficient in &mut s_primex[((2 * params.n) + 1)..] {
                *coefficient = *coefficient - &cur_positive;
                *coefficient = *coefficient - &cur_negative;
                cur_positive *= &y_cur;
                cur_negative *= &y_cur_inv;
            }
        }

        // Compute r(X, y_cur) + s'(X, y_cur)
        let mut r_primex = rxy.clone();
        r_primex.resize(4 * params.n + 1, C::Scalar::zero());
        assert_eq!(r_primex[params.n..].len(), s_primex.len());
        for (a, b) in r_primex[params.n..].iter_mut().zip(s_primex.iter()) {
            *a += b;
        }

        let mut tx = util::multiply_polynomials(rx.clone(), r_primex);
        assert_eq!(tx.len(), 7 * params.n + 1);
        //assert_eq!(tx[4 * params.n], params.compute_opening(&ky, y_cur, false) * &y_cur.pow(&[params.n as u64, 0, 0, 0]));
        tx[4 * params.n] = C::Scalar::zero(); // -k(y)

        // Commit to t^+(X, y)
        let tx_positive = &tx[4 * params.n + 1..];
        let t_positive_commitment = params.commit(tx_positive, false);
        let transcript = append_point::<C>(transcript, &t_positive_commitment);

        // Commit to t^-(X, y)
        let tx_negative = &tx[0..(4 * params.n)];
        let t_negative_commitment = params.commit(tx_negative, false);
        assert_eq!(params.generators.len(), 4 * params.n);
        let transcript = append_point::<C>(transcript, &t_negative_commitment);

        // Obtain the challenge x
        let (transcript, x) = get_challenge::<_, C::Scalar>(transcript);

        // Compute s(x, Y)
        let mut sy = params.compute_sy::<_, S>(circuit, x, params.n, assignment.q)?;
        {
            // We have to scale s(x, Y) by x^n to correspond with the
            // other commitments.
            let xn = x.pow(&[params.n as u64, 0, 0, 0]);
            for coeff in &mut sy {
                *coeff = *coeff * &xn;
            }
        }

        // Commit to s(x, Y)
        let c_commitment = params.commit(&sy, false);
        let transcript = append_point::<C>(transcript, &c_commitment);

        // Obtain the challenge y_new
        let (transcript, y_new) = get_challenge::<_, C::Scalar>(transcript);

        // Compute s(X, y_new)
        let sx_new = params.compute_sx::<_, S>(circuit, y_new)?;

        // Commit to s(X, y_new)
        let s_new_commitment = params.commit(&sx_new, false);
        let transcript = append_point::<C>(transcript, &s_new_commitment);

        // Send openings
        let ky_opening = params.compute_opening(&ky, y_cur, false);
        let transcript = append_scalar::<C>(transcript, &ky_opening);
        let rx_opening = params.compute_opening(&rx, x, true);
        let transcript = append_scalar::<C>(transcript, &rx_opening);
        let rxy_opening = params.compute_opening(&rx, x * &y_cur, true);
        let transcript = append_scalar::<C>(transcript, &rxy_opening);
        let sx_old_opening = params.compute_opening(&sx_old, x, false);
        let transcript = append_scalar::<C>(transcript, &sx_old_opening);
        let sx_cur_opening = params.compute_opening(&sx_cur, x, false);
        let transcript = append_scalar::<C>(transcript, &sx_cur_opening);
        let tx_positive_opening = params.compute_opening(&tx_positive, x, false);
        let transcript = append_scalar::<C>(transcript, &tx_positive_opening);
        let tx_negative_opening = params.compute_opening(&tx_negative, x, false);
        let transcript = append_scalar::<C>(transcript, &tx_negative_opening);
        let sx_new_opening = params.compute_opening(&sx_new, x, false);
        let transcript = append_scalar::<C>(transcript, &sx_new_opening);

        // We don't add this to the transcript, the verifier computes it.
        // That's the whole trick!
        let gx_old_opening = params.compute_opening(&gx_old, x, false);
        assert_eq!(
            gx_old_opening,
            compute_b(x, &old_leftovers.challenges_new, &challenges_old_inv)
        );

        // Obtain the challenge z
        let (transcript, z) = get_challenge::<_, C::Scalar>(transcript);

        // Compute P, the commitment to p(x), and p, the value it
        // must open to
        let p_commitment = r_commitment;
        let p_commitment = p_commitment * &z + s_old_commitment;
        let p_commitment = p_commitment * &z + s_cur_commitment;
        let p_commitment = p_commitment * &z + t_positive_commitment;
        let p_commitment = p_commitment * &z + t_negative_commitment;
        let p_commitment = p_commitment * &z + s_new_commitment;
        let p_commitment = p_commitment * &z + g_old_commitment;

        let p_opening = rx_opening;
        let p_opening = p_opening * &z + &sx_old_opening;
        let p_opening = p_opening * &z + &sx_cur_opening;
        let p_opening = p_opening * &z + &tx_positive_opening;
        let p_opening = p_opening * &z + &tx_negative_opening;
        let p_opening = p_opening * &z + &sx_new_opening;
        let p_opening = p_opening * &z + &gx_old_opening;

        let mut px = vec![C::Scalar::zero(); params.d];
        px[(params.d - rx.len())..].copy_from_slice(&rx);
        {
            fn add_to_px<F: Field>(px: &mut [F], poly: &[F]) {
                for (a, b) in px.iter_mut().zip(poly.iter()) {
                    *a += b;
                }
            }
            fn mul_px<F: Field>(px: &mut [F], z: &F) {
                for a in px.iter_mut() {
                    *a *= z;
                }
            }
            mul_px(&mut px, &z);
            add_to_px(&mut px, &sx_old);
            drop(sx_old);
            mul_px(&mut px, &z);
            add_to_px(&mut px, &sx_cur);
            drop(sx_cur);
            mul_px(&mut px, &z);
            add_to_px(&mut px, &tx_positive);
            drop(tx_positive);
            mul_px(&mut px, &z);
            add_to_px(&mut px, &tx_negative);
            drop(tx_negative);
            mul_px(&mut px, &z);
            add_to_px(&mut px, &sx_new);
            drop(sx_new);
            mul_px(&mut px, &z);
            add_to_px(&mut px, &gx_old);
            drop(gx_old);
        }

        let q_commitment = c_commitment + (k_commitment * &z);
        let qy_opening = sx_cur_opening + &(ky_opening * &z);

        let mut qy = sy.clone();
        for i in 0..ky.len() {
            qy[i] = qy[i] + &(ky[i] * &z);
        }

        let mut transcript = transcript;
        let (inner_product, challenges_new, g_new) = MultiPolynomialOpening::new_proof(
            &mut transcript,
            &[
                (
                    PolynomialOpening {
                        commitment: p_commitment,
                        opening: p_opening,
                        point: x,
                        right_edge: false,
                    },
                    &px,
                ),
                (
                    PolynomialOpening {
                        commitment: r_commitment,
                        opening: rxy_opening,
                        point: x * &y_cur,
                        right_edge: true,
                    },
                    &rx,
                ),
                (
                    PolynomialOpening {
                        commitment: c_commitment,
                        opening: sx_old_opening,
                        point: y_old,
                        right_edge: false,
                    },
                    &sy,
                ),
                (
                    PolynomialOpening {
                        commitment: q_commitment,
                        opening: qy_opening,
                        point: y_cur,
                        right_edge: false,
                    },
                    &qy,
                ),
                (
                    PolynomialOpening {
                        commitment: c_commitment,
                        opening: sx_new_opening,
                        point: y_new,
                        right_edge: false,
                    },
                    &sy,
                ),
            ],
            &params.generators,
            params.k,
        );

        let metadata = Leftovers {
            s_new_commitment,
            y_new,
            g_new,
            challenges_new,
        };

        Ok((
            Proof {
                r_commitment,
                s_cur_commitment,
                t_positive_commitment,
                t_negative_commitment,
                c_commitment,
                s_new_commitment,

                rx_opening,
                rxy_opening,
                sx_old_opening,
                sx_cur_opening,
                tx_positive_opening,
                tx_negative_opening,
                sx_new_opening,

                inner_product,
            },
            metadata,
        ))
    }

    pub fn verify<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        leftovers: &Leftovers<C>,
        params: &Params<C>,
        circuit: &CS,
        inputs: &[C::Scalar],
        k_commitment: Option<C>,
    ) -> Result<(bool, Leftovers<C>), SynthesisError> {
        struct InputMap {
            inputs: Vec<usize>,
        }

        impl<'a, F: Field> Backend<F> for &'a mut InputMap {
            type LinearConstraintIndex = ();

            fn get_for_q(&self, _q: usize) -> Self::LinearConstraintIndex {
                ()
            }

            fn new_k_power(&mut self, index: usize, _: Option<F>) -> Result<(), SynthesisError> {
                self.inputs.push(index);
                Ok(())
            }

            fn new_linear_constraint(&mut self) {
                ()
            }
        }

        let mut inputmap = InputMap { inputs: vec![] };
        S::synthesize(&mut inputmap, circuit)?;
        assert_eq!(inputs.len(), inputmap.inputs.len() - 1);

        let transcript = C::Base::zero();

        // Commitments
        let mut ky = vec![];
        ky.push(C::Scalar::zero());
        for (index, value) in inputmap
            .inputs
            .iter()
            .zip(Some(C::Scalar::one()).iter().chain(inputs.iter()))
        {
            ky.resize(index + 1, C::Scalar::zero());
            ky[*index] = *value;
        }
        let k_commitment = match k_commitment {
            Some(c) => c,
            None => params.commit(&ky, false),
        };
        let transcript = append_point::<C>(transcript, &k_commitment);
        let transcript = append_point::<C>(transcript, &self.r_commitment);
        let (transcript, y_cur) = get_challenge::<_, C::Scalar>(transcript);
        let transcript = append_point::<C>(transcript, &self.s_cur_commitment);
        let transcript = append_point::<C>(transcript, &self.t_positive_commitment);
        let transcript = append_point::<C>(transcript, &self.t_negative_commitment);
        let (transcript, x) = get_challenge::<_, C::Scalar>(transcript);
        let transcript = append_point::<C>(transcript, &self.c_commitment);
        let (transcript, y_new) = get_challenge::<_, C::Scalar>(transcript);
        let transcript = append_point::<C>(transcript, &self.s_new_commitment);

        // Openings
        let ky_opening = params.compute_opening(&ky, y_cur, false);
        let transcript = append_scalar::<C>(transcript, &ky_opening);
        let transcript = append_scalar::<C>(transcript, &self.rx_opening);
        let transcript = append_scalar::<C>(transcript, &self.rxy_opening);
        let transcript = append_scalar::<C>(transcript, &self.sx_old_opening);
        let transcript = append_scalar::<C>(transcript, &self.sx_cur_opening);
        let transcript = append_scalar::<C>(transcript, &self.tx_positive_opening);
        let transcript = append_scalar::<C>(transcript, &self.tx_negative_opening);
        let transcript = append_scalar::<C>(transcript, &self.sx_new_opening);

        // Check that circuit is satisfied...
        let xinv = x.invert().unwrap();
        let xyinv = (x * &y_cur).invert().unwrap();
        let rhs = self.tx_positive_opening * &x;
        let rhs = rhs + &(self.tx_negative_opening * &(xinv.pow(&[params.d as u64, 0, 0, 0])));
        let lhs = self.sx_cur_opening * &(xinv.pow(&[params.n as u64, 0, 0, 0]));
        let lhs = lhs * &y_cur.pow(&[params.n as u64, 0, 0, 0]);
        /// Computes x + x^2 + x^3 + ... + x^n
        fn compute_thing<F: Field>(x: F, n: u64) -> F {
            let num = (x.pow(&[n, 0, 0, 0]) - F::one()) * x;
            let denom = x - F::one();

            num * denom.invert().unwrap()
        }
        let thing = compute_thing(x * &y_cur, params.n as u64);
        let thing = thing + &compute_thing(x * &(y_cur.invert().unwrap()), params.n as u64);
        let thing = thing * &(x.pow(&[params.n as u64, 0, 0, 0]));
        let lhs = lhs - &thing;
        let lhs = lhs + &(self.rxy_opening * &(xyinv.pow(&[(params.n * 3 - 1) as u64, 0, 0, 0])));
        let lhs = lhs * &(self.rx_opening * &(xinv.pow(&[(params.n * 3 - 1) as u64, 0, 0, 0])));
        let ky = ky_opening * (&y_cur.pow(&[params.n as u64, 0, 0, 0]));
        let lhs = lhs - &ky;

        let circuit_satisfied = rhs == lhs;

        let mut challenges_old_inv = leftovers.challenges_new.clone();
        for c in &mut challenges_old_inv {
            *c = c.invert().unwrap()
        }
        // Not added to the transcript; we computed it.
        let gx_old_opening = compute_b(x, &leftovers.challenges_new, &challenges_old_inv);

        let (transcript, z) = get_challenge::<_, C::Scalar>(transcript);

        let p_commitment = self.r_commitment;
        let p_commitment = p_commitment * &z + leftovers.s_new_commitment;
        let p_commitment = p_commitment * &z + self.s_cur_commitment;
        let p_commitment = p_commitment * &z + self.t_positive_commitment;
        let p_commitment = p_commitment * &z + self.t_negative_commitment;
        let p_commitment = p_commitment * &z + self.s_new_commitment;
        let p_commitment = p_commitment * &z + leftovers.g_new;

        let p_opening = self.rx_opening;
        let p_opening = p_opening * &z + &self.sx_old_opening;
        let p_opening = p_opening * &z + &self.sx_cur_opening;
        let p_opening = p_opening * &z + &self.tx_positive_opening;
        let p_opening = p_opening * &z + &self.tx_negative_opening;
        let p_opening = p_opening * &z + &self.sx_new_opening;
        let p_opening = p_opening * &z + &gx_old_opening;

        let q_commitment = self.c_commitment + (k_commitment * &z);
        let qy_opening = self.sx_cur_opening + &(ky_opening * &z);

        let mut transcript = transcript;
        let (inner_product_satisfied, challenges_new, g_new) = self.inner_product.verify_proof(
            &mut transcript,
            &[
                PolynomialOpening {
                    commitment: p_commitment,
                    opening: p_opening,
                    point: x,
                    right_edge: false,
                },
                PolynomialOpening {
                    commitment: self.r_commitment,
                    opening: self.rxy_opening,
                    point: x * &y_cur,
                    right_edge: true,
                },
                PolynomialOpening {
                    commitment: self.c_commitment,
                    opening: self.sx_old_opening,
                    point: leftovers.y_new,
                    right_edge: false,
                },
                PolynomialOpening {
                    commitment: q_commitment,
                    opening: qy_opening,
                    point: y_cur,
                    right_edge: false,
                },
                PolynomialOpening {
                    commitment: self.c_commitment,
                    opening: self.sx_new_opening,
                    point: y_new,
                    right_edge: false,
                },
            ],
            params.k,
        );

        let metadata = Leftovers {
            s_new_commitment: self.s_new_commitment,
            y_new,
            g_new,
            challenges_new,
        };

        Ok((inner_product_satisfied & circuit_satisfied, metadata))
    }
}

#[test]
fn my_test_circuit() {
    struct CubingCircuit<F: Field> {
        x: Option<F>,
    }

    impl<F: Field> Circuit<F> for CubingCircuit<F> {
        fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut x2value = None;
            let (x, _, x2) = cs.multiply(|| {
                let x = self.x.ok_or(SynthesisError::AssignmentMissing)?;
                let x2 = x.square();

                x2value = Some(x2);

                Ok((x, x, x2))
            })?;
            let mut x3value = None;
            let (a, b, c) = cs.multiply(|| {
                let x = self.x.ok_or(SynthesisError::AssignmentMissing)?;
                let x2 = x2value.ok_or(SynthesisError::AssignmentMissing)?;
                let x3 = x * x2;

                x3value = Some(x3);

                Ok((x, x2, x3))
            })?;

            cs.enforce_zero(LinearCombination::from(x) - a);
            cs.enforce_zero(LinearCombination::from(x2) - b);

            let x3 =
                cs.alloc_input(|| "x3", || x3value.ok_or(SynthesisError::AssignmentMissing))?;

            cs.enforce_zero(LinearCombination::from(x3) - c);

            Ok(())
        }
    }

    let params: Params<Ec1> = Params::new(4);

    let mut prover_circuit: CubingCircuit<Fq> = CubingCircuit {
        x: Some(Fq::from(10)),
    };
    assert!(is_satisfied::<_, _, Basic>(&prover_circuit, &[Fq::from(1000)]).unwrap());
    let verifier_circuit: CubingCircuit<Fq> = CubingCircuit { x: None };

    // bootstrap the cycle with phony inputs
    let dummy_leftovers = Leftovers::dummy(&params);
    assert!(dummy_leftovers
        .verify::<_, Basic>(&params, &verifier_circuit)
        .unwrap());

    // create proof
    let (proof, prover_new_leftovers) =
        Proof::new::<_, Basic>(&params, &prover_circuit, &dummy_leftovers).unwrap();
    assert!(prover_new_leftovers
        .verify::<_, Basic>(&params, &verifier_circuit)
        .unwrap());

    // partially verify proof (without doing any linear time procedures)
    let (valid_proof, verifier_new_leftovers) = proof
        .verify::<_, Basic>(
            &dummy_leftovers,
            &params,
            &verifier_circuit,
            &[Fq::from(1000)],
            None,
        )
        .unwrap();
    assert!(valid_proof);
    assert!(verifier_new_leftovers
        .verify::<_, Basic>(&params, &verifier_circuit)
        .unwrap());
    assert_eq!(prover_new_leftovers, verifier_new_leftovers);

    prover_circuit.x = Some(Fq::from_u64(3));

    let (proof, prover_new_leftovers) =
        Proof::new::<_, Basic>(&params, &prover_circuit, &prover_new_leftovers).unwrap();
    assert!(prover_new_leftovers
        .verify::<_, Basic>(&params, &verifier_circuit)
        .unwrap());

    let (valid_proof, verifier_new_leftovers) = proof
        .verify::<_, Basic>(
            &verifier_new_leftovers,
            &params,
            &verifier_circuit,
            &[Fq::from(27)],
            None,
        )
        .unwrap();
    assert!(valid_proof);
    assert!(verifier_new_leftovers
        .verify::<_, Basic>(&params, &verifier_circuit)
        .unwrap());
    assert_eq!(prover_new_leftovers, verifier_new_leftovers);
}

#[derive(Clone)]
pub struct Params<C: Curve> {
    pub g: C,
    pub d: usize,
    pub n: usize,
    pub k: usize,
    pub generators: Vec<C>,
    pub generators_xy: Vec<(C::Base, C::Base)>,
}

impl<C: Curve> Params<C> {
    pub fn new(k: usize) -> Self {
        assert!(k > 3);
        let d = 1 << k;
        let n = d / 4;

        let mut generators = Vec::with_capacity(d);
        let mut generators_xy = Vec::with_capacity(d);
        // TODO: use public source of randomness
        while generators.len() < d {
            use rand_core::{OsRng, RngCore};
            let mut attempt = [0u8; 32];
            OsRng.fill_bytes(&mut attempt);
            let attempt = C::from_bytes(&attempt);
            if bool::from(attempt.is_some()) {
                let attempt = attempt.unwrap();
                generators.push(attempt);
                let (x, y, z) = attempt.get_xyz();
                assert!(z == C::Base::one());
                generators_xy.push((x, y));
            }
        }

        Params {
            g: C::one(),
            k,
            d,
            n,
            generators,
            generators_xy,
        }
    }

    pub fn commit(&self, v: &[C::Scalar], right_edge: bool) -> C {
        assert!(self.generators.len() >= v.len());
        if right_edge {
            util::multiexp(&v, &self.generators[(self.generators.len() - v.len())..])
        } else {
            util::multiexp(&v, &self.generators[0..v.len()])
        }
    }

    pub fn compute_sx<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        y: C::Scalar,
    ) -> Result<Vec<C::Scalar>, SynthesisError> {
        let mut sx = SxEval::new(y);
        S::synthesize(&mut sx, circuit)?;
        let (mut u, mut v, mut w) = sx.poly();
        u.resize(self.n, C::Scalar::zero());
        v.resize(self.n, C::Scalar::zero());
        w.resize(self.n, C::Scalar::zero());
        let mut sx = Vec::with_capacity(3 * self.n + 1);
        sx.extend(u.into_iter().rev());
        sx.push(C::Scalar::zero());
        sx.extend(v);
        sx.extend(w);
        assert_eq!(sx.len(), 3 * self.n + 1);

        Ok(sx)
    }

    pub fn compute_sy<CS: Circuit<C::Scalar>, S: SynthesisDriver>(
        &self,
        circuit: &CS,
        x: C::Scalar,
        n: usize,
        q: usize,
    ) -> Result<Vec<C::Scalar>, SynthesisError> {
        let mut sy = SyEval::new(x, n, q);
        S::synthesize(&mut sy, circuit)?;
        Ok(sy.poly())
    }

    pub fn compute_opening<F: Field>(&self, v: &[F], point: F, right_edge: bool) -> F {
        let mut acc = F::zero();
        let mut cur = F::one();
        for v in v {
            let tmp = cur * v;
            acc = acc + tmp;
            cur = cur * point;
        }

        if right_edge {
            acc = acc * point.pow(&[(self.generators.len() - v.len()) as u64, 0, 0, 0]);
        }

        acc
    }
}

pub struct PolynomialOpening<C: Curve> {
    commitment: C,
    opening: C::Scalar,
    point: C::Scalar,
    right_edge: bool,
}

#[derive(Clone)]
pub struct MultiPolynomialOpening<C: Curve> {
    rounds: Vec<InnerProductRound<C>>,
    a: Vec<C::Scalar>,
    g: C,
}

#[derive(Clone)]
#[allow(non_snake_case)]
pub struct InnerProductRound<C: Curve> {
    L: Vec<C>,
    R: Vec<C>,
    l: Vec<C::Scalar>,
    r: Vec<C::Scalar>,
}

impl<C: Curve> InnerProductRound<C> {
    fn dummy() -> Self {
        InnerProductRound {
            L: vec![C::one(); 5],
            R: vec![C::one(); 5],
            l: vec![C::Scalar::one(); 5],
            r: vec![C::Scalar::one(); 5],
        }
    }
}

impl<C: Curve> MultiPolynomialOpening<C> {
    pub fn dummy(params: &Params<C>) -> Self {
        MultiPolynomialOpening {
            rounds: vec![InnerProductRound::dummy(); params.k],
            a: vec![C::Scalar::one(); 5],
            g: C::one(),
        }
    }

    pub fn verify_proof(
        &self,
        transcript: &mut C::Base,
        instances: &[PolynomialOpening<C>],
        k: usize,
    ) -> (bool, Vec<C::Scalar>, C) {
        // TODO: verify lengths of stuff before we proceed

        let mut p = vec![];
        let mut v = vec![];

        for instance in instances {
            p.push(instance.commitment);
            v.push(instance.opening);
        }

        let mut challenges = vec![];
        let mut challenges_inv = vec![];
        let mut challenges_sq = vec![];
        let mut challenges_inv_sq = vec![];
        assert_eq!(self.rounds.len(), k);

        for round in &self.rounds {
            for j in 0..instances.len() {
                *transcript = append_point(*transcript, &round.L[j]);
                *transcript = append_point(*transcript, &round.R[j]);
                *transcript = append_scalar::<C>(*transcript, &round.l[j]);
                *transcript = append_scalar::<C>(*transcript, &round.r[j]);
            }

            let (new_transcript, challenge) = get_challenge::<_, C::Scalar>(*transcript);
            *transcript = new_transcript;
            let challenge_inv = challenge.invert().unwrap();
            let challenge_sq = challenge.square();
            let challenge_inv_sq = challenge_inv.square();

            challenges.push(challenge);
            challenges_inv.push(challenge_inv);
            challenges_sq.push(challenge_sq);
            challenges_inv_sq.push(challenge_inv_sq);

            for j in 0..instances.len() {
                p[j] = p[j] + (round.L[j] * challenge_sq);
                p[j] = p[j] + (round.R[j] * challenge_inv_sq);
                v[j] = v[j] + &(round.l[j] * &challenge_sq);
                v[j] = v[j] + &(round.r[j] * &challenge_inv_sq);
            }
        }

        for j in 0..instances.len() {
            let b = compute_b(instances[j].point, &challenges, &challenges_inv);

            if p[j] != (self.g * self.a[j]) {
                return (false, challenges, self.g);
            }

            if v[j] != (self.a[j] * &b) {
                return (false, challenges, self.g);
            }
        }

        return (true, challenges, self.g);
    }

    pub fn new_proof<'a>(
        transcript: &mut C::Base,
        instances: &'a [(PolynomialOpening<C>, &'a [C::Scalar])],
        generators: &[C],
        k: usize,
    ) -> (MultiPolynomialOpening<C>, Vec<C::Scalar>, C) {
        let mut rounds = vec![];
        let mut a = vec![];
        let mut b = vec![];
        let mut generators = generators.to_vec();

        for instance in instances {
            let mut v;
            if instance.0.right_edge {
                v = vec![C::Scalar::zero(); 1 << k];
                v[(1 << k) - instance.1.len()..].copy_from_slice(&instance.1);
            } else {
                v = instance.1.to_vec();
                v.resize(1 << k, C::Scalar::zero());
            }
            a.push(v);
            let mut v = Vec::with_capacity(1 << k);
            let mut cur = C::Scalar::one();
            for _ in 0..(1 << k) {
                v.push(cur);
                cur = cur * &instance.0.point;
            }
            b.push(v);
        }

        let mut challenges = vec![];
        {
            let mut k = k;
            #[allow(non_snake_case)]
            while k > 0 {
                let l = 1 << (k - 1);
                let mut round_L = vec![];
                let mut round_R = vec![];
                let mut round_l = vec![];
                let mut round_r = vec![];
                for j in 0..instances.len() {
                    let this_L = util::multiexp(&a[j][0..l], &generators[l..]);
                    let this_R = util::multiexp(&a[j][l..], &generators[0..l]);
                    let this_l = compute_inner_product(&a[j][0..l], &b[j][l..]);
                    let this_r = compute_inner_product(&a[j][l..], &b[j][0..l]);
                    *transcript = append_point(*transcript, &this_L);
                    *transcript = append_point(*transcript, &this_R);
                    *transcript = append_scalar::<C>(*transcript, &this_l);
                    *transcript = append_scalar::<C>(*transcript, &this_r);

                    round_L.push(this_L);
                    round_R.push(this_R);
                    round_l.push(this_l);
                    round_r.push(this_r);
                }
                let (new_transcript, challenge) = get_challenge::<_, C::Scalar>(*transcript);
                *transcript = new_transcript;
                let challenge_inv = challenge.invert().unwrap();

                challenges.push(challenge);

                for j in 0..instances.len() {
                    for i in 0..l {
                        a[j][i] = (a[j][i] * &challenge) + &(a[j][i + l] * &challenge_inv);
                        b[j][i] = (b[j][i] * &challenge_inv) + &(b[j][i + l] * &challenge);
                    }
                    a[j].truncate(l);
                    b[j].truncate(l);
                }

                for i in 0..l {
                    generators[i] =
                        (generators[i] * &challenge_inv) + &(generators[i + l] * &challenge);
                }

                generators.truncate(l);

                rounds.push(InnerProductRound {
                    L: round_L,
                    R: round_R,
                    l: round_l,
                    r: round_r,
                });

                k -= 1;
            }
        }

        let mut final_a = vec![];
        for j in 0..instances.len() {
            assert_eq!(a[j].len(), 1);
            final_a.push(a[j][0]);
        }

        assert_eq!(generators.len(), 1);

        (
            MultiPolynomialOpening {
                rounds,
                a: final_a,
                g: generators[0],
            },
            challenges,
            generators[0],
        )
    }
}

fn append_point<C: Curve>(transcript: C::Base, p: &C) -> C::Base {
    let xy = p.get_xy();
    if bool::from(xy.is_some()) {
        let (x, y) = xy.unwrap();
        rescue(&[transcript, x, y])
    } else {
        rescue(&[transcript, C::Base::zero(), C::Base::zero()])
    }
}

fn append_scalar<C: Curve>(transcript: C::Base, scalar: &C::Scalar) -> C::Base {
    append_point(transcript, &(C::one() * scalar))
}

fn get_challenge<F1: Field, F2: Field>(transcript: F1) -> (F1, F2) {
    let new_transcript = rescue(&[transcript]);
    let challenge = transcript.get_lower_128();

    (new_transcript, F2::from_u128(challenge))
}

/*
s(X, Y) =   \sum\limits_{i=1}^N u_i(Y) X^{-i}
          + \sum\limits_{i=1}^N v_i(Y) X^{i}
          + \sum\limits_{i=1}^N w_i(Y) X^{i+N}
where
    u_i(Y) = \sum\limits_{q=1}^Q Y^{q} u_{i,q}
    v_i(Y) = \sum\limits_{q=1}^Q Y^{q} v_{i,q}
    w_i(Y) = \sum\limits_{q=1}^Q Y^{q} w_{i,q}
*/
#[derive(Clone)]
struct SxEval<F: Field> {
    y: F,

    // current value of y^{q}
    cur_y: F,

    // x^{-i} (\sum\limits_{q=1}^Q y^{q} u_{i,q})
    u: Vec<F>,
    // x^{i} (\sum\limits_{q=1}^Q y^{q} v_{i,q})
    v: Vec<F>,
    // x^{i+N} (\sum\limits_{q=1}^Q y^{q} w_{i,q})
    w: Vec<F>,
}

impl<F: Field> SxEval<F> {
    fn new(y: F) -> Self {
        let u = vec![];
        let v = vec![];
        let w = vec![];

        SxEval {
            y,
            cur_y: F::one(),
            u,
            v,
            w,
        }
    }

    fn poly(self) -> (Vec<F>, Vec<F>, Vec<F>) {
        (self.u, self.v, self.w)
    }
}

impl<'a, F: Field> Backend<F> for &'a mut SxEval<F> {
    type LinearConstraintIndex = F;

    fn new_multiplication_gate(&mut self) {
        self.u.push(F::zero());
        self.v.push(F::zero());
        self.w.push(F::zero());
    }

    fn new_linear_constraint(&mut self) -> F {
        self.cur_y.mul_assign(&self.y);
        self.cur_y
    }

    fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
        self.y.pow(&[q as u64, 0, 0, 0])
    }

    fn insert_coefficient(&mut self, var: Variable, coeff: Coeff<F>, y: &F) {
        let acc = match var {
            Variable::A(index) => &mut self.u[index - 1],
            Variable::B(index) => &mut self.v[index - 1],
            Variable::C(index) => &mut self.w[index - 1],
        };

        let mut tmp = *y;
        coeff.multiply(&mut tmp);
        *acc = *acc + tmp;
    }
}

/*
s(X, Y) =   \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q} u_{i,q} x^{-i}
          + \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q} v_{i,q} x^{i}
          + \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q} w_{i,q} x^{i+N}
*/
struct SyEval<F: Field> {
    // x^{-1}, ..., x^{-N}
    a: Vec<F>,

    // x^1, ..., x^{N}
    b: Vec<F>,

    // x^{N+1}, ..., x^{2*N}
    c: Vec<F>,

    // Coefficients of s(x, Y)
    poly: Vec<F>,
    /*
        // coeffs for y^1, ..., y^{N+Q}
        positive_coeffs: Vec<E::Fr>,

        // coeffs for y^{-1}, y^{-2}, ..., y^{-N}
        negative_coeffs: Vec<E::Fr>,
    */
}

impl<F: Field> SyEval<F> {
    fn new(x: F, n: usize, q: usize) -> Self {
        let xinv = x.invert().unwrap();
        let mut tmp = F::one();
        let mut a = vec![F::zero(); n];
        for a in &mut a {
            tmp.mul_assign(&xinv); // tmp = x^{-i}
            *a = tmp;
        }

        let mut tmp = F::one();
        let mut b = vec![F::zero(); n];
        for b in &mut b {
            tmp.mul_assign(&x); // tmp = x^{i}
            *b = tmp;
        }

        let mut c = vec![F::zero(); n];
        for c in c.iter_mut() {
            tmp.mul_assign(&x); // tmp = x^{i+N}
            *c = tmp;
        }

        let mut poly = Vec::with_capacity(q);
        poly.push(F::zero()); // constant term

        SyEval {
            a,
            b,
            c,
            poly: poly,
        }
    }

    fn poly(self) -> Vec<F> {
        self.poly
    }
}

impl<'a, F: Field> Backend<F> for &'a mut SyEval<F> {
    type LinearConstraintIndex = usize;

    fn new_linear_constraint(&mut self) -> usize {
        let index = self.poly.len();
        self.poly.push(F::zero());
        index
    }

    fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex {
        q
    }

    fn insert_coefficient(&mut self, var: Variable, coeff: Coeff<F>, q: &usize) {
        match var {
            Variable::A(index) => {
                let index = index - 1;
                // Y^{q} += X^{-i} * coeff
                let mut tmp = self.a[index];
                coeff.multiply(&mut tmp);
                let yindex = *q;
                self.poly[yindex].add_assign(&tmp);
            }
            Variable::B(index) => {
                let index = index - 1;
                // Y^{q} += X^{i} * coeff
                let mut tmp = self.b[index];
                coeff.multiply(&mut tmp);
                let yindex = *q;
                self.poly[yindex].add_assign(&tmp);
            }
            Variable::C(index) => {
                let index = index - 1;
                // Y^{q} += X^{i+N} * coeff
                let mut tmp = self.c[index];
                coeff.multiply(&mut tmp);
                let yindex = *q;
                self.poly[yindex].add_assign(&tmp);
            }
        };
    }
}
