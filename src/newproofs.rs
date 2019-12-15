use super::{Challenge, Curve, CurveAffine, Field};

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
    pub polynomial_opening: Vec<(C, C, C::Scalar, C::Scalar)>,
    // At the end of the argument, the prover supplies a scalar `a`
    // and a group element g_new_commitment
    pub a: C::Scalar,
    pub g_new_commitment: C,
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
