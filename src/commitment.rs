use crate::{util, Curve, Field, Transcript};

#[derive(Debug)]
pub struct GrothCommitment<C: Curve>(Vec<C>);

impl<C: Curve> GrothCommitment<C> {
    pub fn dummy_commitment(m: usize, n: usize) -> Self {
        let points = (0..m).map(|_| C::one()).collect();

        GrothCommitment(points)
    }
}

impl<C: Curve> GrothCommitment<C> {
    pub fn get_points(&self) -> &[C] {
        &self.0
    }
}

fn get_coeff<F: Field>(coeffs: &[F], index: usize, edge: bool, offset: usize) -> F {
    // If `edge` is specified, the polynomial is being committed to at the
    // right edge of possible polynomials to degree bound it. As a result,
    // all queries to coeffs at `index` smaller than `offset` are implicitly
    // zero
    if edge {
        if index < offset {
            F::zero()
        } else {
            coeffs[index - offset]
        }
    } else {
        coeffs.get(index).map(|a| *a).unwrap_or_else(|| F::zero())
    }
}

pub fn create_groth_commitment<F: Field, C: Curve<Scalar = F>>(
    coefficients: &[F],
    edge: bool,
    generators: &[C],
    m: usize,
    n: usize,
) -> GrothCommitment<C> {
    assert!(coefficients.len() <= (m * n));
    assert_eq!(generators.len(), n);

    let offset = (m * n) - coefficients.len();

    let mut results = vec![C::zero(); m];
    let mut v = vec![F::zero(); n];
    for i in 0..m {
        for j in 0..n {
            v[j] = get_coeff(&coefficients, (j * m) + i, edge, offset);
        }
        results[i] = util::multiexp(&v, &generators);
    }

    GrothCommitment(results)
}

pub struct GrothOpeningProof<C: Curve> {
    value: C::Scalar,
    rounds: Vec<(C::Scalar, C, C::Scalar, C)>,
    a: C::Scalar,
}

/// Creates an opening proof assuming that the commitment has
/// already been appended to the transcript.
pub fn create_groth_opening<F: Field, C: Curve<Scalar = F>>(
    transcript: &mut Transcript<C>,
    edge: bool,
    coefficients: &[F],
    generators: &[C],
    m: usize,
    n: usize,
    x: F,
) -> GrothOpeningProof<C> {
    assert!(coefficients.len() <= (m * n));
    assert_eq!(generators.len(), n);

    let offset = (m * n) - coefficients.len();

    let mut powers_of_x = vec![F::zero(); m];
    {
        let mut cur = F::one();
        for i in 0..m {
            powers_of_x[i] = cur;
            cur = cur * x;
        }
    }

    let mut a = vec![F::zero(); n];
    for j in 0..n {
        let jm = j * m;
        let mut acc = F::zero();
        for i in 0..m {
            acc = acc + (get_coeff(&coefficients, jm + i, edge, offset) * powers_of_x[i]);
        }
        a[j] = acc;
    }
    drop(powers_of_x);

    let mut b = {
        let mut powers_of_x = vec![F::zero(); n];
        let mut cur = F::one();
        let xm = x.pow(m as u64);
        for i in 0..n {
            powers_of_x[i] = cur;
            cur = cur * xm;
        }
        powers_of_x
    };

    // Now, we create an inner product proof
    let mut k = 1;
    while (1 << k) < a.len() {
        k += 1;
    }
    a.resize(1 << k, F::zero());
    b.resize(1 << k, F::zero());

    let value = util::compute_inner_product(&a, &b);
    transcript.append_scalar(value);

    let mut rounds = Vec::with_capacity(k);

    let mut generators = generators.to_vec();
    generators.resize(1 << k, C::zero());

    while k > 0 {
        let l = 1 << (k - 1);

        let lvalue = util::compute_inner_product(&a[0..l], &b[l..]);
        let lv = util::multiexp(&a[0..l], &generators[l..]);
        let rvalue = util::compute_inner_product(&a[l..], &b[0..l]);
        let rv = util::multiexp(&a[l..], &generators[0..l]);
        transcript.append_scalar(lvalue);
        transcript.append_point(&lv);
        transcript.append_scalar(rvalue);
        transcript.append_point(&rv);
        rounds.push((lvalue, lv, rvalue, rv));

        let u: F = transcript.get_challenge();
        let uinv = u.invert().unwrap();

        for i in 0..l {
            a[i] = (a[i] * u) + (a[i + l] * uinv);
            b[i] = (b[i] * uinv) + (b[i + l] * u);
            generators[i] = (generators[i] * uinv) + (generators[i + l] * u);
        }
        a.truncate(l);
        b.truncate(l);
        generators.truncate(l);

        k -= 1;
    }

    assert_eq!(a.len(), 1);
    assert_eq!(b.len(), 1);
    assert_eq!(generators.len(), 1);

    GrothOpeningProof {
        value,
        rounds,
        a: a[0],
    }
}

/// Verify a groth opening assuming the commitment has
/// already been appended to the transcript.
pub fn verify_groth_opening<F: Field, C: Curve<Scalar = F>>(
    transcript: &mut Transcript<C>,
    commitment: &GrothCommitment<C>,
    opening: &GrothOpeningProof<C>,
    generators: &[C],
    m: usize,
    n: usize,
    x: F,
) -> bool {
    assert_eq!(commitment.0.len(), m);
    assert_eq!(generators.len(), n);

    let mut powers_of_x = vec![F::zero(); m];
    {
        let mut cur = F::one();
        for i in 0..m {
            powers_of_x[i] = cur;
            cur = cur * x;
        }
    }

    let mut acc = util::multiexp(&powers_of_x, &commitment.0);

    let mut k = 1;
    while (1 << k) < n {
        k += 1;
    }

    let mut generators = generators.to_vec();
    generators.resize(1 << k, C::zero());

    assert_eq!(opening.rounds.len(), k);

    transcript.append_scalar(opening.value);
    let mut value_acc = opening.value;

    let mut challenges = Vec::with_capacity(k);
    let mut challenges_inv = Vec::with_capacity(k);

    for (lvalue, lv, rvalue, rv) in &opening.rounds {
        transcript.append_scalar(*lvalue);
        transcript.append_point(lv);
        transcript.append_scalar(*rvalue);
        transcript.append_point(rv);

        let u: F = transcript.get_challenge();
        challenges.push(u);
        challenges_inv.push(u);
    }

    let allinv = F::batch_invert(&mut challenges_inv);

    let mut challenges_sq = challenges.clone();
    let mut challenges_inv_sq = challenges_inv.clone();
    for c in &mut challenges_sq {
        *c = c.square();
    }
    for c in &mut challenges_inv_sq {
        *c = c.square();
    }

    for (i, (lvalue, lv, rvalue, rv)) in opening.rounds.iter().enumerate() {
        value_acc = value_acc + (*lvalue * challenges_sq[i]) + (*rvalue * challenges_inv_sq[i]);
        acc = acc + (*lv * challenges_sq[i]) + (*rv * challenges_inv_sq[i]);
    }

    let b = compute_b_for_inner_product(m as u64, n, &challenges_sq, allinv, x);
    let rhs = compute_g_for_inner_product(&generators, &challenges_sq, allinv) * opening.a;

    let ab = opening.a * b;

    ab == value_acc && acc == rhs
}

pub fn compute_b_for_inner_product<F: Field>(
    m: u64,
    n: usize,
    challenges_sq: &[F],
    allinv: F,
    x: F,
) -> F {
    let lg_n = challenges_sq.len();
    assert!((1 << lg_n) >= n);

    let mut s = Vec::with_capacity(n);
    s.push(allinv);
    for i in 1..n {
        let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
        let k = 1 << lg_i;
        let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
        s.push(s[i - k] * u_lg_i_sq);
    }

    // Use Horner's rule
    let mut acc = F::zero();
    let xm = x.pow(m);
    for s in s.into_iter().rev() {
        acc = acc * xm;
        acc = acc + s;
    }

    acc
}

pub fn compute_g_for_inner_product<F: Field, C: Curve<Scalar = F>>(
    generators: &[C],
    challenges_sq: &[F],
    allinv: F,
) -> C {
    let n = generators.len();
    let lg_n = challenges_sq.len();
    assert_eq!(n, 1 << lg_n);

    let mut s = Vec::with_capacity(n);
    s.push(allinv);
    for i in 1..n {
        let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
        let k = 1 << lg_i;
        let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
        s.push(s[i - k] * u_lg_i_sq);
    }

    util::multiexp(&s, &generators)
}

#[test]
fn test_groth_commitments() {
    use crate::{Ec1, Fp};

    // mn is chosen to be an even power of two, i.e.
    // mn = 2^4
    // so that mn = (m/2)(n*2)
    // and also for the inner product argument

    let m = 13;
    let n = 18;
    let coeffs = (0..m * n)
        .map(|i| Fp::from_u64(i as u64))
        .collect::<Vec<_>>();
    let mut generators = Vec::with_capacity(n);
    {
        let mut cur = Ec1::one();
        for _ in 0..n {
            generators.push(cur);
            cur = cur * Fp::from_u64(123728);
        }
    }
    let x = Fp::from_u64(384734);
    let commitment = create_groth_commitment(&coeffs, false, &generators, m, n);

    let mut transcript = Transcript::new();
    transcript.append_groth_commitment(&commitment);
    let opening = create_groth_opening(&mut transcript, false, &coeffs, &generators, m, n, x);

    let mut expected_value = Fp::zero();
    for coeff in coeffs.iter().rev() {
        expected_value = expected_value * x;
        expected_value = expected_value + *coeff;
    }

    assert_eq!(expected_value, opening.value);

    {
        let mut transcript = Transcript::new();
        transcript.append_groth_commitment(&commitment);

        assert!(verify_groth_opening(
            &mut transcript,
            &commitment,
            &opening,
            &generators,
            m,
            n,
            x
        ));
    }
}

#[test]
fn test_edge_commitment() {
    use crate::{Ec1, Fp};

    let m = 15;
    let n = 10;

    // mn = 150

    // poly with 30 coefficients
    let coeffs = (0..30).map(|i| Fp::from_u64(i as u64)).collect::<Vec<_>>();

    let mut generators = Vec::with_capacity(n);
    {
        let mut cur = Ec1::one();
        for _ in 0..n {
            generators.push(cur);
            cur = cur * Fp::from_u64(123728);
        }
    }
    let x = Fp::from_u64(384734);
    let commitment = create_groth_commitment(&coeffs, true, &generators, m, n);

    let mut transcript = Transcript::new();
    transcript.append_groth_commitment(&commitment);
    let opening = create_groth_opening(&mut transcript, true, &coeffs, &generators, m, n, x);

    let mut expected_value = Fp::zero();
    for coeff in coeffs.iter().rev() {
        expected_value = expected_value * x;
        expected_value = expected_value + *coeff;
    }

    // expected value should actually be multiplied by x^(30 - 150 = 120)
    expected_value = expected_value * x.pow(120);

    assert_eq!(expected_value, opening.value);

    {
        let mut transcript = Transcript::new();
        transcript.append_groth_commitment(&commitment);

        assert!(verify_groth_opening(
            &mut transcript,
            &commitment,
            &opening,
            &generators,
            m,
            n,
            x
        ));
    }
}
