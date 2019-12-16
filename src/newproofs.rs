use super::newcircuits::{
    Backend, Basic, Circuit, Coeff, ConstraintSystem, LinearCombination, SxEval, SyEval,
    SynthesisDriver, SynthesisError, Variable,
};
use super::rescue::Rescue;
use super::util::Challenge;
use super::{Curve, CurveAffine, Field};

/// Challenge input that happens to map to a square on both fields
const MAGIC: u128 = 0;

#[derive(Clone)]
pub struct Params<C: CurveAffine> {
    pub g: C,
    pub h: C,
    pub d: usize,
    pub n: usize,
    pub k: usize,
    pub generators: Vec<C>,
}

pub struct Proof<C: CurveAffine> {
    // These are the commitments sent after K = Commit(k(Y)) has been computed
    pub r_commitment: C,
    pub s_cur_commitment: C,
    pub t_positive_commitment: C,
    pub t_negative_commitment: C,
    pub c_commitment: C,
    pub s_new_commitment: C,

    // k(x), k(x * y_cur), k(y_old), k(y_cur), k(y_new)
    pub k_openings: [C::Scalar; 5],
    // r(x, 1), r(x, y_cur), r(y_old, 1), r(y_cur, 1), r(y_new, 1)
    pub r_openings: [C::Scalar; 5],
    // s(x, x), s(x, x * y_cur), s(x, y_old), s(x, y_cur), s(x, y_new)
    pub c_openings: [C::Scalar; 5],
    // t+(x, 1)
    pub t_positive_opening: C::Scalar,
    // t-(x, 1)
    pub t_negative_opening: C::Scalar,
    // p(x * y_cur), p(y_old), p(y_cur), p(y_new)
    // Verifier computes p(x)
    pub p_openings: [C::Scalar; 4],
    // The prover commits to the quotient polynomial h(X).
    pub h_commitment: C,
    // The prover opens q(X) at a random point.
    pub q_opening: C::Scalar,
    // The prover opens the F commitment up to the expected value
    // using a variant of the inner product argument.
    pub polynomial_opening: Vec<(C, C)>,
    pub g_new_commitment: C,
    // Schnorr proof
    pub delta: C,
    pub beta: C,
    pub r1: C::Scalar,
    pub r2: C::Scalar,
}

pub struct Deferred<F: Field> {
    // Points, needed to compute expected values
    pub y_old: F,
    pub y_cur: F,
    pub y_new: F,
    pub x: F,
    pub z1: F,
    pub z2: F,
    pub z3: F,
    pub z4: F,

    // k(x), k(x * y_cur), k(y_old), k(y_cur), k(y_new)
    pub k_openings: [F; 5],
    // r(x, 1), r(x, y_cur), r(y_old, 1), r(y_cur, 1), r(y_new, 1)
    pub r_openings: [F; 5],
    // s(x, x), s(x, x * y_cur), s(x, y_old), s(x, y_cur), s(x, y_new)
    pub s_openings: [F; 5],
    // t+(x, 1)
    pub t_positive_opening: F,
    // t-(x, 1)
    pub t_negative_opening: F,
    // p(x * y_cur), p(y_old), p(y_cur), p(y_new)
    pub p_openings: [F; 4],
    // The prover opens q(X) at a random point.
    pub q_opening: F,
    // During the inner product the prover will supply these scalars
    pub polynomial_opening: Vec<(F, F)>,
    // At the end of the argument, the prover supplies a scalar `a`
    // and a group element g_new_commitment
    pub a: F,
    // Old challenges, needed to compute g_old(x)
    pub challenges_old_sq_packed: Vec<Challenge>, // length is k
    // New challenges, needed to compute b
    pub challenges_new_sq_packed: Vec<Challenge>, // length is k
}

pub struct Amortized<C: CurveAffine> {
    pub g_new_commitment: C,
    pub s_new_commitment: C,
    pub y_new: Challenge,
    pub challenges_new_sq_packed: Vec<Challenge>, // length is k
}

pub fn create_proof<C: CurveAffine, CS: Circuit<C::Scalar>>(
    params: &Params<C>,
    circuit: &CS,
    old_amortized: &Amortized<C>,
) -> Result<Proof<C>, SynthesisError> {
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
        fn new_k_power(&mut self, index: usize, value: Option<F>) -> Result<(), SynthesisError> {
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

    // TODO: this is "randomness" the prover uses to hide their commitments
    let r_r = C::Scalar::from_u64(103);
    let r_t_positive = C::Scalar::from_u64(251);
    let r_t_negative = C::Scalar::from_u64(514);
    let r_h = C::Scalar::from_u64(910);

    Basic::synthesize(&mut assignment, circuit)?;

    // TODO, better API than this
    assert!(assignment.n < params.n);
    assert!(assignment.q < params.d);

    assignment.a.resize(params.n, C::Scalar::zero());
    assignment.b.resize(params.n, C::Scalar::zero());
    assignment.c.resize(params.n, C::Scalar::zero());

    let mut transcript = Rescue::<C::Base>::new();

    // Compute s(X, y_old)
    let y_old = crate::util::get_challenge_scalar(old_amortized.y_new);
    let sx_old = params.compute_sx(circuit, y_old)?;

    // Get S_old
    let s_old_commitment = old_amortized.s_new_commitment;

    // Sanity check
    {
        let expected = params.commit(&sx_old, false);
        let expected = params.add_randomness(&expected, C::Scalar::one());
        assert_eq!(
            s_old_commitment.to_projective(),
            expected.to_projective()
        );
    }

    // Compute the coefficients for G_old
    let challenges_old_sq: Vec<C::Scalar> = old_amortized
        .challenges_new_sq_packed
        .iter()
        .map(|v| crate::util::get_challenge_scalar(*v))
        .collect();
    let challenges_old: Vec<C::Scalar> = challenges_old_sq
        .iter()
        .map(|a| a.sqrt().unwrap())
        .collect();
    let mut challenges_old_inv = challenges_old.clone();
    let allinv_old = Field::batch_invert(&mut challenges_old_inv);
    let gx_old = crate::util::compute_s(&challenges_old_sq, allinv_old);

    // Get G_old
    let g_old_commitment = old_amortized.g_new_commitment;

    // Compute k(Y)
    let mut ky = vec![];
    ky.push(C::Scalar::zero());
    for (index, value) in assignment.inputs {
        ky.resize(index + 1, C::Scalar::zero());
        ky[index] = value;
    }

    // Commit to k(Y)
    let k_commitment = params.commit(&ky, false);
    let k_commitment = params.add_randomness(&k_commitment, C::Scalar::one());
    append_point(&mut transcript, &k_commitment);

    // Compute r(X, Y)
    let mut rx = Vec::with_capacity(3 * params.n + 1);
    rx.extend(assignment.c.into_iter().rev());
    rx.extend(assignment.b.into_iter().rev());
    rx.push(C::Scalar::zero());
    rx.extend(assignment.a.into_iter());
    assert_eq!(rx.len(), 3 * params.n + 1);

    // Commit to r(X, 1)
    let r_commitment = params.commit(&rx, true);
    let r_commitment = params.add_randomness(&r_commitment, r_r);
    append_point(&mut transcript, &r_commitment);

    // Obtain the challenge y_cur
    let y_cur = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));
    let y_cur_inv = y_cur.invert().unwrap();

    // Compute s(X, y_cur)
    let sx_cur = params.compute_sx(circuit, y_cur)?;

    // Commit to s(X, y_cur)
    let s_cur_commitment = params.commit(&sx_cur, false);
    let s_cur_commitment = params.add_randomness(&s_cur_commitment, C::Scalar::one());
    append_point(&mut transcript, &s_cur_commitment);

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

    let mut tx = crate::util::multiply_polynomials(rx.clone(), r_primex);
    assert_eq!(tx.len(), 7 * params.n + 1);
    
    // Sanity check
    assert_eq!(tx[4 * params.n], params.compute_opening(&ky, y_cur, false) * &y_cur.pow(&[params.n as u64, 0, 0, 0]));
    
    tx[4 * params.n] = C::Scalar::zero(); // -k(y)

    // Commit to t^+(X, y)
    let tx_positive = &tx[4 * params.n + 1..];
    let t_positive_commitment = params.commit(tx_positive, false);
    let t_positive_commitment = params.add_randomness(&t_positive_commitment, r_t_positive);
    append_point(&mut transcript, &t_positive_commitment);

    // Commit to t^-(X, y)
    let tx_negative = &tx[0..(4 * params.n)];
    let t_negative_commitment = params.commit(tx_negative, false);
    let t_negative_commitment = params.add_randomness(&t_negative_commitment, r_t_negative);
    assert_eq!(params.generators.len(), 4 * params.n);
    append_point(&mut transcript, &t_negative_commitment);

    // Obtain the challenge x
    let x = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    // Compute s(x, Y)
    let mut sy = params.compute_sy(circuit, x, params.n, assignment.q)?;
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
    let c_commitment = params.add_randomness(&c_commitment, C::Scalar::one());
    append_point(&mut transcript, &c_commitment);

    // Obtain the challenge y_new
    let y_new = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    // Compute s(X, y_new)
    let sx_new = params.compute_sx(circuit, y_new)?;

    // Commit to s(X, y_new)
    let s_new_commitment = params.commit(&sx_new, false);
    let s_new_commitment = params.add_randomness(&s_new_commitment, C::Scalar::one());
    append_point::<C>(&mut transcript, &s_new_commitment);

    //
    // Time to send openings!
    //

    let xy_cur = x * &y_cur;

    // Transcript on the "other curve"
    let mut dual_transcript = Rescue::<C::Scalar>::new();

    // k(x), k(x * y_cur), k(y_old), k(y_cur), k(y_new)
    let k_openings: [C::Scalar; 5] = [
        params.compute_opening(&ky, x, false),
        params.compute_opening(&ky, xy_cur, false),
        params.compute_opening(&ky, y_old, false),
        params.compute_opening(&ky, y_cur, false),
        params.compute_opening(&ky, y_new, false),
    ];

    for o in k_openings.iter() {
        dual_transcript.absorb(*o);
    }

    // r(x, 1), r(x, y_cur), r(y_old, 1), r(y_cur, 1), r(y_new, 1)
    let r_openings: [C::Scalar; 5] = [
        params.compute_opening(&rx, x, true),
        params.compute_opening(&rx, xy_cur, true),
        params.compute_opening(&rx, y_old, true),
        params.compute_opening(&rx, y_cur, true),
        params.compute_opening(&rx, y_new, true),
    ];

    for o in r_openings.iter() {
        dual_transcript.absorb(*o);
    }

    // s(x, x), s(x, x * y_cur), s(x, y_old), s(x, y_cur), s(x, y_new)
    let c_openings: [C::Scalar; 5] = [
        params.compute_opening(&sy, x, false),
        params.compute_opening(&sy, xy_cur, false),
        params.compute_opening(&sy, y_old, false),
        params.compute_opening(&sy, y_cur, false),
        params.compute_opening(&sy, y_new, false),
    ];

    for o in c_openings.iter() {
        dual_transcript.absorb(*o);
    }

    // t+(x, 1)
    let t_positive_opening: C::Scalar = params.compute_opening(&tx_positive, x, false);
    dual_transcript.absorb(t_positive_opening);

    // t-(x, 1)
    let t_negative_opening: C::Scalar = params.compute_opening(&tx_negative, x, false);
    dual_transcript.absorb(t_negative_opening);

    // Sanity check; is the constraint system satisfied
    {
        let xinv = x.invert().unwrap();
        let yinv = y_cur.invert().unwrap();
        let xyinv = xinv * &yinv;

        let xinvn = xinv.pow(&[params.n as u64, 0, 0, 0]);
        let xinvd = xinvn.square().square();
        let yn = y_cur.pow(&[params.n as u64, 0, 0, 0]);
        let xn = x.pow(&[params.n as u64, 0, 0, 0]);
        let xyinvn31 = xyinv.pow(&[(3 * params.n - 1) as u64, 0, 0, 0]);
        let xinvn31 = (xinvn.square() * &xinvn) * &x;

        let rhs = t_positive_opening * &x;
        let rhs = rhs + &(t_negative_opening * &xinvd);

        let lhs = c_openings[3] * &xinvn;
        let lhs = lhs * &yn;

        // Computes x + x^2 + x^3 + ... + x^n
        fn compute_thing<F: Field>(x: F, k: usize) -> F {
            let mut acc = x;
            let mut cur = x;
            for _ in 0..k {
                let tmp = acc * cur;
                cur = cur.square();
                acc = acc + tmp;
            }
            acc
        }

        let thing = compute_thing(x * &y_cur, params.k - 2);
        let thing = thing + &compute_thing(x * &yinv, params.k - 2);
        let thing = thing * &xn;
        let lhs = lhs - &thing;
        let lhs = lhs + &(r_openings[1] * &xyinvn31);
        let lhs = lhs * &(r_openings[0] * &xinvn31);
        let ky = k_openings[3] * &yn;
        let lhs = lhs - &ky;

        assert_eq!(lhs, rhs);
    }

    // This hash is "transferred" from the other curve.
    let hash_1 = dual_transcript.squeeze();
    let hash_1 = C::Base::from_bytes(&hash_1.to_bytes()).unwrap(); // TODO: lazy; this can fail (low probability)
    transcript.absorb(hash_1);

    // Obtain the challenge z_1
    let z1 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    // Construct p(X)
    let mut px = vec![C::Scalar::zero(); params.d];
    px[0..sx_old.len()].copy_from_slice(&sx_old);

    fn add_to_px<F: Field>(px: &mut [F], poly: &[F]) {
        for (a, b) in px.iter_mut().zip(poly.iter()) {
            *a += b;
        }
    }
    fn sub_from_px<F: Field>(px: &mut [F], poly: &[F]) {
        for (a, b) in px.iter_mut().zip(poly.iter()) {
            *a -= b;
        }
    }
    fn mul_px<F: Field>(px: &mut [F], z: &F) {
        for a in px.iter_mut() {
            *a *= z;
        }
    }

    mul_px(&mut px, &z1);
    add_to_px(&mut px, &sx_cur);
    drop(sx_cur);
    mul_px(&mut px, &z1);
    add_to_px(&mut px, &tx_positive);
    drop(tx_positive);
    mul_px(&mut px, &z1);
    add_to_px(&mut px, &tx_negative);
    drop(tx_negative);
    mul_px(&mut px, &z1);
    add_to_px(&mut px, &sx_new);
    drop(sx_new);
    mul_px(&mut px, &z1);
    add_to_px(&mut px, &gx_old);
    drop(gx_old);
    
    let p_randomness = C::Scalar::one();
    let p_randomness = p_randomness * &z1 + &C::Scalar::one();
    let p_randomness = p_randomness * &z1 + &r_t_positive;
    let p_randomness = p_randomness * &z1 + &r_t_negative;
    let p_randomness = p_randomness * &z1 + &C::Scalar::one();
    let p_randomness = p_randomness * &z1;

    // Sanity check
    {
        // Is the commitment what we expect?
        let p_commitment = s_old_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &s_cur_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_positive_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_negative_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &s_new_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &g_old_commitment.to_projective();

        let expected = params.commit(&px, false);
        let expected = params.add_randomness(&expected, p_randomness);

        assert_eq!(
            p_commitment,
            expected.to_projective()
        );
    }

    let px_expected_opening_at_x =
        ((((c_openings[2] * &z1 + &c_openings[3]) * &z1 + &t_positive_opening) * &z1
            + &t_negative_opening)
            * &z1
            + &c_openings[4])
            * &z1
            + &crate::util::compute_b(x, &challenges_old, &challenges_old_inv);

    // Sanity check; does it open to the correct value at x?
    assert_eq!(params.compute_opening(&px, x, false), px_expected_opening_at_x);

    // p(x * y_cur), p(y_old), p(y_cur), p(y_new)
    let p_openings: [C::Scalar; 4] = [
        params.compute_opening(&px, xy_cur, false),
        params.compute_opening(&px, y_old, false),
        params.compute_opening(&px, y_cur, false),
        params.compute_opening(&px, y_new, false),
    ];

    // Transcript on the "other curve"
    let mut dual_transcript = Rescue::<C::Scalar>::new();

    for o in p_openings.iter() {
        dual_transcript.absorb(*o);
    }

    // This hash is "transferred" from the other curve.
    let hash_2 = dual_transcript.squeeze();
    let hash_2 = C::Base::from_bytes(&hash_2.to_bytes()).unwrap(); // TODO: lazy; this can fail (low probability)
    transcript.absorb(hash_2);

    // Obtain the challenge z_2
    let z2 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    // Construct q(X)
    let mut qx = vec![C::Scalar::zero(); params.d];
    qx[(params.d - rx.len())..].copy_from_slice(&rx);

    mul_px(&mut qx, &z2);
    add_to_px(&mut qx, &px);
    drop(px);
    mul_px(&mut qx, &z2);
    add_to_px(&mut qx, &ky);
    drop(ky);
    mul_px(&mut qx, &z2);
    add_to_px(&mut qx, &sy);
    drop(sy);

    // Sanity check, is q(X) correct?
    assert_eq!(
        params.compute_opening(&qx, x, false),
        ((r_openings[0] * &z2 + &px_expected_opening_at_x) * &z2 + &k_openings[0]) * &z2 + &c_openings[0]
    );
    assert_eq!(
        params.compute_opening(&qx, xy_cur, false),
        ((r_openings[1] * &z2 + &p_openings[0]) * &z2 + &k_openings[1]) * &z2 + &c_openings[1]
    );
    assert_eq!(
        params.compute_opening(&qx, y_old, false),
        ((r_openings[2] * &z2 + &p_openings[1]) * &z2 + &k_openings[2]) * &z2 + &c_openings[2]
    );
    assert_eq!(
        params.compute_opening(&qx, y_cur, false),
        ((r_openings[3] * &z2 + &p_openings[2]) * &z2 + &k_openings[3]) * &z2 + &c_openings[3]
    );
    assert_eq!(
        params.compute_opening(&qx, y_new, false),
        ((r_openings[4] * &z2 + &p_openings[3]) * &z2 + &k_openings[4]) * &z2 + &c_openings[4]
    );

    // Construct t(X)
    let mut tx = vec![C::Scalar::zero(); 5];
    for (j, p) in [x, xy_cur, y_old, y_cur, y_new].iter().enumerate() {
        let mut poly = vec![C::Scalar::one()];
        for (m, q) in [x, xy_cur, y_old, y_cur, y_new].iter().enumerate() {
            if m != j {
                let tmp = (*p - q).invert().unwrap();
                poly = crate::util::multiply_polynomials(poly, vec![(-*q) * &tmp, tmp])
            }
        }

        let value = match j {
            0 => ((r_openings[0] * &z2 + &px_expected_opening_at_x) * &z2 + &k_openings[0]) * &z2 + &c_openings[0],
            1 => ((r_openings[1] * &z2 + &p_openings[0]) * &z2 + &k_openings[1]) * &z2 + &c_openings[1],
            2 => ((r_openings[2] * &z2 + &p_openings[1]) * &z2 + &k_openings[2]) * &z2 + &c_openings[2],
            3 => ((r_openings[3] * &z2 + &p_openings[2]) * &z2 + &k_openings[3]) * &z2 + &c_openings[3],
            4 => ((r_openings[4] * &z2 + &p_openings[3]) * &z2 + &k_openings[4]) * &z2 + &c_openings[4],
            _ => unreachable!()
        };
        for coeff in poly.iter_mut() {
            *coeff = *coeff * &value;
        }
        add_to_px(&mut tx, &poly);
    }

    // Sanity check, is t(X) correct?
    assert_eq!(
        params.compute_opening(&tx, x, false),
        params.compute_opening(&qx, x, false)
    );
    assert_eq!(
        params.compute_opening(&tx, xy_cur, false),
        params.compute_opening(&qx, xy_cur, false)
    );
    assert_eq!(
        params.compute_opening(&tx, y_old, false),
        params.compute_opening(&qx, y_old, false)
    );
    assert_eq!(
        params.compute_opening(&tx, y_cur, false),
        params.compute_opening(&qx, y_cur, false)
    );
    assert_eq!(
        params.compute_opening(&tx, y_new, false),
        params.compute_opening(&qx, y_new, false)
    );

    // Compute h(X)
    let mut hx = qx.clone();
    sub_from_px(&mut hx, &tx);
    let hx = crate::util::divide_root(hx.into_iter().rev(), x);
    let hx = crate::util::divide_root(hx, xy_cur);
    let hx = crate::util::divide_root(hx, y_old);
    let hx = crate::util::divide_root(hx, y_cur);
    let hx = crate::util::divide_root(hx, y_new);
    let mut hx = hx.collect::<Vec<_>>();
    hx.reverse();

    // Sanity check, did we do it correctly?
    {
        let arbitrary_point = C::Scalar::from_u64(12182812);
        let q = params.compute_opening(&qx, arbitrary_point, false);
        let h = params.compute_opening(&hx, arbitrary_point, false);
        let t = params.compute_opening(&tx, arbitrary_point, false);

        let denom = (arbitrary_point - &x) * &(arbitrary_point - &xy_cur) * &(arbitrary_point - &y_old) * &(arbitrary_point - &y_cur) * &(arbitrary_point - &y_new);

        assert_eq!(h * (&denom) + &t, q);
    }
    
    // Commit to h(X)
    let h_commitment = params.commit(&hx, false);
    let h_commitment = params.add_randomness(&h_commitment, r_h);
    append_point::<C>(&mut transcript, &h_commitment);

    // Obtain the challenge z_3
    let z3 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    // Send q(z_3)
    let q_opening = params.compute_opening(&qx, z3, false);

    // Transcript on the "other curve"
    let mut dual_transcript = Rescue::<C::Scalar>::new();
    dual_transcript.absorb(q_opening);

    // This hash is "transferred" from the other curve.
    let hash_3 = dual_transcript.squeeze();
    let hash_3 = C::Base::from_bytes(&hash_3.to_bytes()).unwrap(); // TODO: lazy; this can fail (low probability)
    transcript.absorb(hash_3);

    // Obtain the challenge z_4
    let z4 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    // Compute f(X)
    let mut fx = qx;
    mul_px(&mut fx, &z4);
    add_to_px(&mut fx, &hx);
    
    // The verifier computes the expected opening of f
    let f_opening = {
        let denom = (z3 - &x) * &(z3 - &xy_cur) * &(z3 - &y_old) * &(z3 - &y_cur) * &(z3 - &y_new);
        let t = params.compute_opening(&tx, z3, false);
        (q_opening * &z4) + &((q_opening - &t) * &denom.invert().unwrap())
    };

    let f_randomness = r_r;
    let f_randomness = f_randomness * &z2 + &p_randomness;
    let f_randomness = f_randomness * &z2 + &C::Scalar::one();
    let f_randomness = f_randomness * &z2 + &C::Scalar::one();
    let f_randomness = f_randomness * &z4 + &r_h;

    // Sanity check; is the verifier gonna be happy?
    {
        let f = params.compute_opening(&fx, z3, false);

        assert_eq!(
            f,
            f_opening
        );

        // Is the commitment what we expect?
        let p_commitment = s_old_commitment;
        let p_commitment = p_commitment * z1 + &s_cur_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_positive_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_negative_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &s_new_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &g_old_commitment.to_projective();

        let q_commitment = r_commitment;
        let q_commitment = q_commitment * z2 + &p_commitment;
        let q_commitment = q_commitment * z2 + &k_commitment.to_projective();
        let q_commitment = q_commitment * z2 + &c_commitment.to_projective();
        
        let f_commitment = q_commitment;
        let f_commitment = f_commitment * z4 + &h_commitment.to_projective();

        let expected = params.commit(&fx, false);
        let expected = params.add_randomness(&expected, f_randomness);

        assert_eq!(
            f_commitment,
            expected.to_projective()
        );
    }

    // Great, we're ready to do it! Here it goes.

    let mut a = fx;
    assert_eq!(a.len(), 1 << params.k);
    let mut b = Vec::with_capacity(1 << params.k);
    {
        let mut cur = C::Scalar::one();
        for _ in 0..(1 << params.k) {
            b.push(cur);
            cur = cur * &z3;
        }
    }
    let mut generators = params.generators.to_vec();

    let mut rounds = vec![];
    let mut challenges = vec![];
    let mut challenges_inv = vec![];
    let mut challenges_sq = vec![];
    let mut challenges_sq_inv = vec![];

    let mut randomness = f_randomness;

    {
        let mut k = params.k;
        while k > 0 {
            let half = 1 << (k - 1);
            let l = crate::util::multiexp(&a[0..half], &generators[half..]).to_affine();
            let r = crate::util::multiexp(&a[half..], &generators[0..half]).to_affine();
            let value_l = crate::util::compute_inner_product(&a[0..half], &b[half..]);
            let value_r = crate::util::compute_inner_product(&a[half..], &b[0..half]);
            let l = params.add_value(&l, value_l);
            let r = params.add_value(&r, value_r);

            let mut l_randomness = C::Scalar::from_u64(999999);
            let mut r_randomness = C::Scalar::from_u64(9999998);

            let mut l = params.add_randomness(&l, l_randomness);
            let mut r = params.add_randomness(&r, r_randomness);

            let challenge = loop {
                // We'll fork the transcript to see if the challenge ends up being
                // square.
                let mut transcript = transcript.clone();
                append_point(&mut transcript, &l);
                append_point(&mut transcript, &r);
                
                let challenge_sq = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));
                let challenge = challenge_sq.sqrt();
                if challenge.is_some().into() {
                    break challenge.unwrap();
                } else {
                    // Change our randomness a little
                    l_randomness = l_randomness + &C::Scalar::one();
                    r_randomness = r_randomness + &C::Scalar::one();
                    l = (l + params.h).to_affine();
                    r = (r + params.h).to_affine();
                }
            };

            // Sanity check
            {
                let expected = crate::util::multiexp(&a[0..half], &generators[half..]).to_affine();
                let value_l = crate::util::compute_inner_product(&a[0..half], &b[half..]);
                let expected = params.add_value(&expected, value_l);
                let expected = params.add_randomness(&expected, l_randomness);
                assert_eq!(
                    l, expected
                );
            }
            {
                let expected = crate::util::multiexp(&a[half..], &generators[0..half]).to_affine();
                let value_r = crate::util::compute_inner_product(&a[half..], &b[0..half]);
                let expected = params.add_value(&expected, value_r);
                let expected = params.add_randomness(&expected, r_randomness);
                assert_eq!(
                    r, expected
                );
            }

            append_point(&mut transcript, &l);
            append_point(&mut transcript, &r);
            let challenge_sq_packed = get_challenge(&mut transcript);
            let challenge_sq = crate::util::get_challenge_scalar::<C::Scalar>(challenge_sq_packed);
            assert_eq!(challenge.square(), challenge_sq);
            let challenge_inv = challenge.invert().unwrap();
            let challenge_sq_inv = challenge_inv.square();

            challenges.push(challenge);
            challenges_inv.push(challenge_inv);
            challenges_sq.push(challenge_sq);
            challenges_sq_inv.push(challenge_sq_inv);
            rounds.push((l, r));

            // TODO: parallelize
            for i in 0..half {
                a[i] = (a[i] * &challenge) + &(a[i + half] * &challenge_inv);
                b[i] = (b[i] * &challenge_inv) + &(b[i + half] * &challenge);
            }
            a.truncate(half);
            b.truncate(half);

            crate::util::parallel_generator_collapse(&mut generators, challenge, challenge_inv);
            generators.truncate(half);

            // Update randomness
            randomness += &(l_randomness * &challenge_sq);
            randomness += &(r_randomness * &challenge_sq_inv);

            k -= 1;
        }
    }

    assert_eq!(a.len(), 1);
    let a = a[0];
    assert_eq!(b.len(), 1);
    let b = b[0];
    // Sanity check
    assert_eq!(crate::util::compute_b(z3, &challenges, &challenges_inv), b);
    assert_eq!(generators.len(), 1);
    let g = generators[0];
    // Sanity check
    {
        let mut tmp = challenges.clone();
        let allinv = C::Scalar::batch_invert(&mut tmp);
        assert_eq!(
            crate::util::compute_g(&params.generators, &challenges_sq, allinv).to_affine(),
            g
        );
    }

    // Sanity check
    {
        assert_eq!(rounds.len(), challenges_sq.len());
        assert_eq!(rounds.len(), challenges_sq_inv.len());
        let p_commitment = s_old_commitment;
        let p_commitment = p_commitment * z1 + &s_cur_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_positive_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_negative_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &s_new_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &g_old_commitment.to_projective();

        let q_commitment = r_commitment;
        let q_commitment = q_commitment * z2 + &p_commitment;
        let q_commitment = q_commitment * z2 + &k_commitment.to_projective();
        let q_commitment = q_commitment * z2 + &c_commitment.to_projective();
        
        let f_commitment = q_commitment;
        let f_commitment = f_commitment * z4 + &h_commitment.to_projective();

        let mut lhs = f_commitment;
        for ((&(l, r), challenge_sq), challenge_sq_inv) in rounds.iter().zip(challenges_sq.iter()).zip(challenges_sq_inv.iter()) {
            lhs = lhs + &(l * *challenge_sq);
            lhs = lhs + &(r * *challenge_sq_inv);
        }
        let lhs = lhs.to_affine();
        let lhs = params.add_value(&lhs, f_opening);

        let rhs = (g * a).to_affine();
        let ab = a * &b;
        let rhs = params.add_randomness(&rhs, randomness);
        let rhs = params.add_value(&rhs, ab);

        assert_eq!(lhs, rhs);
    }

    // Schnorr proof
    // TODO: randomness
    let d = C::Scalar::from_u64(987654);
    let r_delta = C::Scalar::from_u64(111112);
    let r_beta = C::Scalar::from_u64(348734);

    let delta = (g * d).to_affine();
    let delta = params.add_randomness(&delta, r_delta);

    let beta = (params.g * d).to_affine();
    let beta = params.add_randomness(&beta, r_beta);

    append_point(&mut transcript, &delta);
    append_point(&mut transcript, &beta);

    let c = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    let ab = a * &b;
    let r1 = d + &(c * &ab);
    let r2 = b * &(c * &randomness + &r_beta) + &r_delta;

    // Sanity check
    {
        let p_commitment = s_old_commitment;
        let p_commitment = p_commitment * z1 + &s_cur_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_positive_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &t_negative_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &s_new_commitment.to_projective();
        let p_commitment = p_commitment * z1 + &g_old_commitment.to_projective();

        let q_commitment = r_commitment;
        let q_commitment = q_commitment * z2 + &p_commitment;
        let q_commitment = q_commitment * z2 + &k_commitment.to_projective();
        let q_commitment = q_commitment * z2 + &c_commitment.to_projective();
        
        let f_commitment = q_commitment;
        let f_commitment = f_commitment * z4 + &h_commitment.to_projective();

        let mut acc = f_commitment;
        for ((&(l, r), challenge_sq), challenge_sq_inv) in rounds.iter().zip(challenges_sq.iter()).zip(challenges_sq_inv.iter()) {
            acc = acc + &(l * *challenge_sq);
            acc = acc + &(r * *challenge_sq_inv);
        }
        let acc = acc.to_affine();
        let acc = params.add_value(&acc, f_opening);

        assert_eq!(
            (acc * c + &beta.to_projective()) * b + &delta.to_projective(),
            (g + (params.g * b).to_affine()) * r1 + &(params.h * r2)
        );
    }

    Ok(Proof {
        r_commitment,
        s_cur_commitment,
        t_positive_commitment,
        t_negative_commitment,
        c_commitment,
        s_new_commitment,
        k_openings,
        r_openings,
        c_openings,
        t_positive_opening,
        t_negative_opening,
        p_openings,
        h_commitment,
        q_opening,
        polynomial_opening: rounds,
        g_new_commitment: g,
        delta,
        beta,
        r1,
        r2,
    })
}

pub fn verify_proof<C: CurveAffine, CS: Circuit<C::Scalar>>(
    params: &Params<C>,
    proof: &Proof<C>,
    old_amortized: &Amortized<C>,
    circuit: &CS,
    inputs: &[C::Scalar],
) -> Result<bool, SynthesisError> {
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

        fn new_linear_constraint(
            &mut self,
        ) -> Self::LinearConstraintIndex
        {
            ()
        }
    }

    let mut inputmap = InputMap { inputs: vec![] };
    Basic::synthesize(&mut inputmap, circuit)?;
    assert_eq!(inputs.len(), inputmap.inputs.len() - 1);

    let mut transcript = Rescue::<C::Base>::new();

    // k(Y)
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
    let k_commitment = params.commit(&ky, false);
    let k_commitment = params.add_randomness(&k_commitment, C::Scalar::one());
    append_point(&mut transcript, &k_commitment);

    append_point(&mut transcript, &proof.r_commitment);
    let y_cur = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));
    append_point(&mut transcript, &proof.s_cur_commitment);
    append_point(&mut transcript, &proof.t_positive_commitment);
    append_point(&mut transcript, &proof.t_negative_commitment);
    let x = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));
    append_point(&mut transcript, &proof.c_commitment);
    let y_new = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));
    append_point(&mut transcript, &proof.s_new_commitment);

    let mut dual_transcript = Rescue::<C::Scalar>::new();
    for o in &proof.k_openings {
        dual_transcript.absorb(*o);
    }
    for o in &proof.r_openings {
        dual_transcript.absorb(*o);
    }
    for o in &proof.c_openings {
        dual_transcript.absorb(*o);
    }

    dual_transcript.absorb(proof.t_positive_opening);
    dual_transcript.absorb(proof.t_negative_opening);

    // Sanity check; is the constraint system satisfied
    {
        let xinv = x.invert().unwrap();
        let yinv = y_cur.invert().unwrap();
        let xyinv = xinv * &yinv;

        let xinvn = xinv.pow(&[params.n as u64, 0, 0, 0]);
        let xinvd = xinvn.square().square();
        let yn = y_cur.pow(&[params.n as u64, 0, 0, 0]);
        let xn = x.pow(&[params.n as u64, 0, 0, 0]);
        let xyinvn31 = xyinv.pow(&[(3 * params.n - 1) as u64, 0, 0, 0]);
        let xinvn31 = (xinvn.square() * &xinvn) * &x;

        let rhs = proof.t_positive_opening * &x;
        let rhs = rhs + &(proof.t_negative_opening * &xinvd);

        let lhs = proof.c_openings[3] * &xinvn;
        let lhs = lhs * &yn;

        // Computes x + x^2 + x^3 + ... + x^n
        fn compute_thing<F: Field>(x: F, k: usize) -> F {
            let mut acc = x;
            let mut cur = x;
            for _ in 0..k {
                let tmp = acc * cur;
                cur = cur.square();
                acc = acc + tmp;
            }
            acc
        }

        let thing = compute_thing(x * &y_cur, params.k - 2);
        let thing = thing + &compute_thing(x * &yinv, params.k - 2);
        let thing = thing * &xn;
        let lhs = lhs - &thing;
        let lhs = lhs + &(proof.r_openings[1] * &xyinvn31);
        let lhs = lhs * &(proof.r_openings[0] * &xinvn31);
        let ky = proof.k_openings[3] * &yn;
        let lhs = lhs - &ky;

        assert_eq!(lhs, rhs);
    }

    let hash_1 = dual_transcript.squeeze();
    let hash_1 = C::Base::from_bytes(&hash_1.to_bytes()).unwrap(); // TODO: lazy; this can fail (low probability)
    transcript.absorb(hash_1);

    let z1 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    let p_commitment = old_amortized.s_new_commitment.to_projective();
    let p_commitment = p_commitment * z1 + &proof.s_cur_commitment.to_projective();
    let p_commitment = p_commitment * z1 + &proof.t_positive_commitment.to_projective();
    let p_commitment = p_commitment * z1 + &proof.t_negative_commitment.to_projective();
    let p_commitment = p_commitment * z1 + &proof.s_new_commitment.to_projective();
    let p_commitment = p_commitment * z1 + &old_amortized.g_new_commitment.to_projective();

    let mut dual_transcript = Rescue::<C::Scalar>::new();
    for o in proof.p_openings.iter() {
        dual_transcript.absorb(*o);
    }

    // This hash is "transferred" from the other curve.
    let hash_2 = dual_transcript.squeeze();
    let hash_2 = C::Base::from_bytes(&hash_2.to_bytes()).unwrap(); // TODO: lazy; this can fail (low probability)
    transcript.absorb(hash_2);

    // Obtain the challenge z_2
    let z2 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    let q_commitment = proof.r_commitment;
    let q_commitment = q_commitment * z2 + &p_commitment;
    let q_commitment = q_commitment * z2 + &k_commitment.to_projective();
    let q_commitment = q_commitment * z2 + &proof.c_commitment.to_projective();
    
    append_point::<C>(&mut transcript, &proof.h_commitment);

    // Obtain the challenge z_3
    let z3 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    let mut dual_transcript = Rescue::<C::Scalar>::new();
    dual_transcript.absorb(proof.q_opening);

    let hash_3 = dual_transcript.squeeze();
    let hash_3 = C::Base::from_bytes(&hash_3.to_bytes()).unwrap(); // TODO: lazy; this can fail (low probability)
    transcript.absorb(hash_3);

    // Obtain the challenge z_4
    let z4 = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    let f_commitment = q_commitment;
    let f_commitment = f_commitment * z4 + &proof.h_commitment.to_projective();

    // Compute expected opening of F
    let f_opening = {
        let xy_cur = x * &y_cur;
        let y_old = crate::util::get_challenge_scalar::<C::Scalar>(old_amortized.y_new);
        let denom = (z3 - &x) * &(z3 - &xy_cur) * &(z3 - &y_old) * &(z3 - &y_cur) * &(z3 - &y_new);

        let challenges_old_sq: Vec<C::Scalar> = old_amortized
            .challenges_new_sq_packed
            .iter()
            .map(|v| crate::util::get_challenge_scalar(*v))
            .collect();
        let challenges_old: Vec<C::Scalar> = challenges_old_sq
            .iter()
            .map(|a| a.sqrt().unwrap())
            .collect();
        let mut challenges_old_inv = challenges_old.clone();
        Field::batch_invert(&mut challenges_old_inv);

        let px_expected_opening_at_x =
        ((((proof.c_openings[2] * &z1 + &proof.c_openings[3]) * &z1 + &proof.t_positive_opening) * &z1
            + &proof.t_negative_opening)
            * &z1
            + &proof.c_openings[4])
            * &z1
            + &crate::util::compute_b(x, &challenges_old, &challenges_old_inv);

        let mut t = C::Scalar::zero();
        for (j, p) in [x, xy_cur, y_old, y_cur, y_new].iter().enumerate() {
            let mut basis_num = C::Scalar::one();
            let mut basis_den = C::Scalar::one();
            for (m, q) in [x, xy_cur, y_old, y_cur, y_new].iter().enumerate() {
                if j != m {
                    basis_num = basis_num * &(z3 - q);
                    basis_den = basis_den * &(*p - q);
                }
            }
            let value = match j {
                0 => ((proof.r_openings[0] * &z2 + &px_expected_opening_at_x) * &z2 + &proof.k_openings[0]) * &z2 + &proof.c_openings[0],
                1 => ((proof.r_openings[1] * &z2 + &proof.p_openings[0]) * &z2 + &proof. k_openings[1]) * &z2 + &proof.c_openings[1],
                2 => ((proof.r_openings[2] * &z2 + &proof.p_openings[1]) * &z2 + &proof. k_openings[2]) * &z2 + &proof.c_openings[2],
                3 => ((proof.r_openings[3] * &z2 + &proof.p_openings[2]) * &z2 + &proof. k_openings[3]) * &z2 + &proof.c_openings[3],
                4 => ((proof.r_openings[4] * &z2 + &proof.p_openings[3]) * &z2 + &proof. k_openings[4]) * &z2 + &proof.c_openings[4],
                _ => unreachable!()
            };
            t += &(value * &(basis_num * &(basis_den.invert().unwrap())));
        }

        // let t = params.compute_opening(&tx, z3, false);
        (proof.q_opening * &z4) + &((proof.q_opening - &t) * &denom.invert().unwrap())
    };

    let mut acc = f_commitment;

    let mut challenges_sq = vec![];
    let mut challenges = vec![];

    for &(l, r) in &proof.polynomial_opening {
        append_point(&mut transcript, &l);
        append_point(&mut transcript, &r);
        let challenge_sq = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));
        let challenge_sq_inv = challenge_sq.invert().unwrap(); // TODO?
        acc = acc + &(l * challenge_sq) + &(r * challenge_sq_inv);

        challenges.push(challenge_sq.sqrt().unwrap());
        challenges_sq.push(challenge_sq);
    }

    let acc = params.add_value(&acc.to_affine(), f_opening);

    let mut challenges_inv = challenges.clone();
    let allinv = C::Scalar::batch_invert(&mut challenges_inv);

    let b = crate::util::compute_b(z3, &challenges, &challenges_inv);
    let expected_g = crate::util::compute_g(&params.generators, &challenges_sq, allinv);

    assert_eq!(expected_g.to_affine(), proof.g_new_commitment);

    append_point(&mut transcript, &proof.delta);
    append_point(&mut transcript, &proof.beta);

    let c = crate::util::get_challenge_scalar::<C::Scalar>(get_challenge(&mut transcript));

    let lhs = acc * c;
    let lhs = lhs + &proof.beta.to_projective();
    let lhs = lhs * b;
    let lhs = lhs + &proof.delta.to_projective();

    let rhs = params.g * b;
    let rhs = rhs + &proof.g_new_commitment.to_projective();
    let rhs = rhs * proof.r1;
    let rhs = rhs + &(params.h * proof.r2);

    Ok(lhs == rhs)
}

impl<C: CurveAffine> Amortized<C> {
    pub fn new<CS: Circuit<C::Scalar>>(params: &Params<C>, circuit: &CS) -> Result<Self, SynthesisError> {
        let y_new = Challenge(0);
        let y_new_scalar: C::Scalar = crate::util::get_challenge_scalar(y_new);
        //let s_new_commitment = params.commit(&[], false, C::Scalar::one());
        let sx_new = params.compute_sx(circuit, y_new_scalar)?;
        let s_new_commitment = params.commit(&sx_new, false);
        let s_new_commitment = params.add_randomness(&s_new_commitment, C::Scalar::one());
        let challenges_new_sq_packed = vec![Challenge(MAGIC); params.k];
        let challenges_new_sq: Vec<C::Scalar> = challenges_new_sq_packed
            .clone()
            .into_iter()
            .map(|v| crate::util::get_challenge_scalar(v))
            .collect();
        let challenges_new: Vec<C::Scalar> = challenges_new_sq
            .iter()
            .map(|v| v.sqrt().unwrap())
            .collect();
        let mut challenges_inv_new = challenges_new;
        let allinv = Field::batch_invert(&mut challenges_inv_new);

        let g_new_commitment =
            crate::util::compute_g(&params.generators, &challenges_new_sq, allinv).to_affine();

        Ok(Amortized {
            g_new_commitment,
            s_new_commitment,
            y_new,
            challenges_new_sq_packed,
        })
    }
}

impl<C: CurveAffine> Params<C> {
    pub fn new(k: usize) -> Self {
        use crossbeam_utils::thread;
        use rand::{rngs::SmallRng, RngCore, SeedableRng};

        assert!(k > 3);
        let d = 1 << k;
        let n = d / 4;

        let mut generators = vec![C::zero(); d];
        let num_cpus = num_cpus::get();
        let mut chunk = d / num_cpus;
        if chunk < num_cpus {
            chunk = d;
        }

        thread::scope(|scope| {
            for gen in generators.chunks_mut(chunk) {
                scope.spawn(move |_| {
                    // TODO: use a secure method to generate
                    let mut attempt = [0u8; 32];
                    let mut rng = SmallRng::seed_from_u64(1 << 15);

                    'outer: for gen in gen.iter_mut() {
                        loop {
                            rng.fill_bytes(&mut attempt);
                            let attempt = C::from_bytes(&attempt);
                            if bool::from(attempt.is_some()) {
                                let attempt = attempt.unwrap();
                                *gen = attempt;
                                continue 'outer;
                            }
                        }
                    }
                });
            }
        })
        .unwrap();

        let g;
        let h;
        {
            // TODO: not secure
            let mut attempt = [0u8; 32];
            let mut rng = SmallRng::seed_from_u64(1 << 14);

            loop {
                rng.fill_bytes(&mut attempt);
                let attempt = C::from_bytes(&attempt);
                if bool::from(attempt.is_some()) {
                    let attempt = attempt.unwrap();
                    g = attempt;
                    break;
                }
            }

            loop {
                rng.fill_bytes(&mut attempt);
                let attempt = C::from_bytes(&attempt);
                if bool::from(attempt.is_some()) {
                    let attempt = attempt.unwrap();
                    h = attempt;
                    break;
                }
            }
        }

        Params {
            g,
            h,
            k,
            d,
            n,
            generators,
        }
    }

    pub fn add_randomness(
        &self,
        to: &C,
        r: C::Scalar,
    ) -> C
    {
        ((self.h * r) + &to.to_projective()).to_affine()
    }

    pub fn add_value(
        &self,
        to: &C,
        value: C::Scalar,
    ) -> C
    {
        ((self.g * value) + &to.to_projective()).to_affine()
    }

    pub fn commit(
        &self,
        v: &[C::Scalar],
        right_edge: bool,
    ) -> C {
        // TODO: could let caller convert to affine

        assert!(self.generators.len() >= v.len());
        let mut tmp = if right_edge {
            crate::util::multiexp(&v, &self.generators[(self.generators.len() - v.len())..])
        } else {
            crate::util::multiexp(&v, &self.generators[0..v.len()])
        };

        // TODO: could fold this into multiexp
        // tmp = tmp + &(self.g * randomness);

        tmp.to_affine()
    }

    pub fn compute_sx<CS: Circuit<C::Scalar>>(
        &self,
        circuit: &CS,
        y: C::Scalar,
    ) -> Result<Vec<C::Scalar>, SynthesisError> {
        let mut sx = SxEval::new(y);
        Basic::synthesize(&mut sx, circuit)?;
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

    pub fn compute_sy<CS: Circuit<C::Scalar>>(
        &self,
        circuit: &CS,
        x: C::Scalar,
        n: usize,
        q: usize,
    ) -> Result<Vec<C::Scalar>, SynthesisError> {
        let mut sy = SyEval::new(x, n, q);
        Basic::synthesize(&mut sy, circuit)?;
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

fn append_point<C: CurveAffine>(transcript: &mut Rescue<C::Base>, p: &C) {
    let xy = p.get_xy();
    if bool::from(xy.is_some()) {
        let (x, y) = xy.unwrap();
        transcript.absorb(x);
        transcript.absorb(y);
    } else {
        transcript.absorb(C::Base::zero());
        transcript.absorb(C::Base::zero());
    }
}

fn get_challenge<F: Field>(transcript: &mut Rescue<F>) -> Challenge {
    let challenge = transcript.squeeze();
    let challenge = challenge.get_lower_128();

    Challenge(challenge)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::curves::{EpAffine, EqAffine};
    use crate::fields::{Fp, Fq};

    struct CubingCircuit<F: Field> {
        x: Option<F>,
    }

    impl<F: Field> Circuit<F> for CubingCircuit<F> {
        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
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
                //let x3 = -(x * x2);
                let x3 = x * x2;

                x3value = Some(x3);

                Ok((x, x2, x3))
            })?;

            cs.enforce_zero(LinearCombination::from(x) - a);
            cs.enforce_zero(LinearCombination::from(x2) - b);

            let x3 = cs.alloc_input(|| x3value.ok_or(SynthesisError::AssignmentMissing))?;

            cs.enforce_zero(LinearCombination::from(x3) - c);

            Ok(())
        }
    }

    #[test]
    fn test_magic() {
        let ep_params = Params::<EpAffine>::new(4);
        let eq_params = Params::<EqAffine>::new(4);

        let verifier_circuit_a: CubingCircuit<Fq> = CubingCircuit { x: None };
        let verifier_circuit_b: CubingCircuit<Fp> = CubingCircuit { x: None };

        let a = Amortized::<EpAffine>::new(&ep_params, &verifier_circuit_a);
        let b = Amortized::<EqAffine>::new(&eq_params, &verifier_circuit_b);
    }

    #[test]
    fn my_test_circuit() {
        let params = Params::<EpAffine>::new(4);

        let mut prover_circuit: CubingCircuit<Fq> = CubingCircuit {
            x: Some(Fq::from(10)),
        };
        let verifier_circuit: CubingCircuit<Fq> = CubingCircuit { x: None };

        // // phony deferred should be valid
        // let a = Deferred::<<Ec1 as Curve>::Scalar>::dummy(params.k);
        // assert!(a.verify(params.k));
        // let a = Deferred::<<Ec0 as Curve>::Scalar>::dummy(params.k);
        // assert!(a.verify(params.k));

        // bootstrap the cycle with phony inputs
        let dummy_amortized = Amortized::new(&params, &verifier_circuit).unwrap();
        // assert!(dummy_leftovers
        //     .verify::<_, Basic>(&params, &verifier_circuit)
        //     .unwrap());

        // create proof
        let proof = create_proof(&params, &prover_circuit, &dummy_amortized).unwrap();
        
        assert!(
            verify_proof(
                &params,
                &proof,
                &dummy_amortized,
                &verifier_circuit,
                &[Fq::from(1000)]
            ).unwrap()
        );
        /*
        assert!(prover_new_leftovers
            .verify::<_, Basic>(&params, &verifier_circuit)
            .unwrap());

        // partially verify proof (without doing any linear time procedures)
        let (valid_proof, verifier_new_leftovers, deferred, _) = proof
            .verify::<_, Basic>(
                &dummy_leftovers,
                &params,
                &verifier_circuit,
                &[Fq::from(1000)],
                None,
            )
            .unwrap();
        assert!(valid_proof);
        assert!(deferred.verify(params.k));
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

        let (valid_proof, verifier_new_leftovers, deferred, _) = proof
            .verify::<_, Basic>(
                &verifier_new_leftovers,
                &params,
                &verifier_circuit,
                &[Fq::from(27)],
                None,
            )
            .unwrap();
        assert!(deferred.verify(params.k));
        assert!(valid_proof);
        assert!(verifier_new_leftovers
            .verify::<_, Basic>(&params, &verifier_circuit)
            .unwrap());
        assert_eq!(prover_new_leftovers, verifier_new_leftovers);
        */
    }
}
