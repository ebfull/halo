use crate::{Curve, CurveAffine, Field};
use crossbeam_utils::thread;
use num_cpus;

/// Divides this polynomial by (X - b)
pub fn divide_root<F: Field, I: IntoIterator<Item = F>>(
    a: I,
    mut b: F,
) -> impl Iterator<Item = F> + ExactSizeIterator
where
    I::IntoIter: ExactSizeIterator,
{
    b = -b;
    let a = a.into_iter();

    let len = a.len() - 1;

    let mut tmp = F::zero();
    a.take(len).map(move |mut lead_coeff| {
        lead_coeff.sub_assign(&tmp);
        let tmp2 = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
        tmp2
    })
}

/// Divides polynomial `a` in `X` by `X - b` with
/// no remainder.
pub fn kate_divison<'a, F: Field, I: IntoIterator<Item = &'a F>>(a: I, mut b: F) -> Vec<F>
where
    I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
{
    b = -b;
    let a = a.into_iter();

    let mut q = vec![F::zero(); a.len() - 1];

    let mut tmp = F::zero();
    for (q, r) in q.iter_mut().rev().zip(a.rev()) {
        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

pub fn parallel_generator_collapse<C: CurveAffine>(
    g: &mut [C],
    challenge: C::Scalar,
    challenge_inv: C::Scalar,
) {
    let l = g.len() / 2;

    let (g_lo, g_hi) = g.split_at_mut(l);

    let num_cpus = num_cpus::get();
    let mut chunk = l / num_cpus;
    if chunk < num_cpus {
        chunk = l;
    }

    thread::scope(|scope| {
        for (lo, hi) in g_lo.chunks_mut(chunk).zip(g_hi.chunks(chunk)) {
            scope.spawn(move |_| {
                let mut tmp = Vec::with_capacity(lo.len());
                for (lo, hi) in lo.iter().zip(hi.iter()) {
                    // TODO: could use multiexp
                    tmp.push(((*lo) * challenge_inv) + &((*hi) * challenge));
                }
                C::Projective::batch_to_affine(&tmp, lo);
            });
        }
    })
    .unwrap();
}

pub fn compute_inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    let mut acc = F::zero();

    for (a, b) in a.iter().zip(b.iter()) {
        acc += (*a) * (*b);
    }

    acc
}

pub fn multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Projective {
    assert_eq!(coeffs.len(), bases.len());

    let num_cpus = num_cpus::get();
    if coeffs.len() > num_cpus {
        let chunk = coeffs.len() / num_cpus;
        let num_chunks = coeffs.chunks(chunk).len();
        let mut results = vec![C::Projective::zero(); num_chunks];
        thread::scope(|scope| {
            let chunk = coeffs.len() / num_cpus;

            for ((coeffs, bases), acc) in coeffs
                .chunks(chunk)
                .zip(bases.chunks(chunk))
                .zip(results.iter_mut())
            {
                scope.spawn(move |_| {
                    let coeffs: Vec<[u8; 32]> = coeffs.iter().map(|a| a.to_bytes()).collect();

                    let c = if bases.len() < 32 {
                        3
                    } else {
                        (f64::from(bases.len() as u32)).ln().ceil() as usize
                    };

                    fn get_at(segment: usize, c: usize, bytes: &[u8; 32]) -> usize {
                        let skip_bits = segment * c;
                        let skip_bytes = skip_bits / 8;

                        if skip_bytes >= 32 {
                            return 0;
                        }

                        let mut v = [0; 8];
                        for (v, o) in v.iter_mut().zip(bytes[skip_bytes..].iter()) {
                            *v = *o;
                        }

                        let mut tmp = u64::from_le_bytes(v);
                        tmp >>= skip_bits - (skip_bytes * 8);
                        tmp = tmp % (1 << c);

                        tmp as usize
                    }

                    let segments = (256 / c) + 1;

                    for current_segment in (0..segments).rev() {
                        for _ in 0..c {
                            *acc = acc.double();
                        }

                        let mut buckets = vec![C::Projective::zero(); (1 << c) - 1];

                        for (coeff, base) in coeffs.iter().zip(bases.iter()) {
                            let coeff = get_at(current_segment, c, coeff);
                            if coeff != 0 {
                                buckets[coeff - 1] += *base;
                            }
                        }

                        // Summation by parts
                        // e.g. 3a + 2b + 1c = a +
                        //                    (a) + b +
                        //                    ((a) + b) + c
                        let mut running_sum = C::Projective::zero();
                        for exp in buckets.into_iter().rev() {
                            running_sum = running_sum + &exp;
                            *acc = *acc + &running_sum;
                        }
                    }
                });
            }
        })
        .unwrap();
        results.iter().fold(C::Projective::zero(), |a, b| a + b)
    } else {
        // TODO: use better algo
        let mut acc = C::Projective::zero();
        for (coeff, base) in coeffs.iter().zip(bases.iter()) {
            let coeff = *coeff;
            let base: C = *base;
            let product = base * coeff;
            acc = acc + &product;
        }
        acc
    }
}

pub fn multiply_polynomials<F: Field>(mut a: Vec<F>, mut b: Vec<F>) -> Vec<F> {
    let degree_of_result = (a.len() - 1) + (b.len() - 1);
    let coeffs_of_result = degree_of_result + 1;

    // Compute the size of our evaluation domain
    let mut m = 1;
    let mut exp = 0;
    while m < coeffs_of_result {
        m *= 2;
        exp += 1;

        // The pairing-friendly curve may not be able to support
        // large enough (radix2) evaluation domains.
        if exp >= F::S {
            panic!("polynomial too large");
        }
    }

    // Compute the 2^exp primitive root of unity
    let mut alpha = F::ROOT_OF_UNITY;
    for _ in exp..F::S {
        alpha = alpha.square();
    }

    // Extend the vectors with zeroes
    a.resize(m, F::zero());
    b.resize(m, F::zero());

    best_fft(&mut a, alpha, exp);
    best_fft(&mut b, alpha, exp);

    // Multiply pairwise
    let num_cpus = num_cpus::get();
    if a.len() > num_cpus {
        thread::scope(|scope| {
            let chunk = a.len() / num_cpus::get();

            for (a, b) in a.chunks_mut(chunk).zip(b.chunks(chunk)) {
                scope.spawn(move |_| {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        *a *= *b;
                    }
                });
            }
        })
        .unwrap();
    } else {
        for (a, b) in a.iter_mut().zip(b.iter()) {
            *a *= *b;
        }
    }

    // Inverse FFT
    let alpha_inv = alpha.invert().unwrap();
    best_fft(&mut a, alpha_inv, exp);

    // Divide all elements by m = a.len()
    let minv = F::from_u64(m as u64).invert().unwrap();
    if a.len() > num_cpus {
        thread::scope(|scope| {
            let chunk = a.len() / num_cpus::get();

            for a in a.chunks_mut(chunk) {
                scope.spawn(move |_| {
                    for a in a.iter_mut() {
                        *a *= minv;
                    }
                });
            }
        })
        .unwrap();
    } else {
        for a in a.iter_mut() {
            *a *= minv;
        }
    }

    a.truncate(coeffs_of_result);

    a
}

fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow + 1)) <= num {
        pow += 1;
    }

    pow
}

fn best_fft<F: Field>(a: &mut [F], omega: F, log_n: u32) {
    let cpus = num_cpus::get();
    let log_cpus = log2_floor(cpus);

    if log_n <= log_cpus {
        serial_fft(a, omega, log_n);
    } else {
        parallel_fft(a, omega, log_n, log_cpus);
    }
}

fn serial_fft<F: Field>(a: &mut [F], omega: F, log_n: u32) {
    fn bitreverse(mut n: u32, l: u32) -> u32 {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    let n = a.len() as u32;
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk as usize, k as usize);
        }
    }

    let mut m = 1;
    for _ in 0..log_n {
        let w_m = omega.pow(&[u64::from(n / (2 * m)), 0, 0, 0]);

        let mut k = 0;
        while k < n {
            let mut w = F::one();
            for j in 0..m {
                let mut t = a[(k + j + m) as usize];
                t *= w;
                a[(k + j + m) as usize] = a[(k + j) as usize] - t;
                a[(k + j) as usize] += t;
                w *= w_m;
            }

            k += 2 * m;
        }

        m *= 2;
    }
}

fn parallel_fft<F: Field>(a: &mut [F], omega: F, log_n: u32, log_cpus: u32) {
    assert!(log_n >= log_cpus);

    let num_cpus = 1 << log_cpus;
    let log_new_n = log_n - log_cpus;
    let mut tmp = vec![vec![F::zero(); 1 << log_new_n]; num_cpus];
    let new_omega = omega.pow(&[num_cpus as u64, 0, 0, 0]);

    thread::scope(|scope| {
        let a = &*a;

        for (j, tmp) in tmp.iter_mut().enumerate() {
            scope.spawn(move |_| {
                // Shuffle into a sub-FFT
                let omega_j = omega.pow(&[j as u64, 0, 0, 0]);
                let omega_step = omega.pow(&[(j as u64) << log_new_n, 0, 0, 0]);

                let mut elt = F::one();
                for i in 0..(1 << log_new_n) {
                    for s in 0..num_cpus {
                        let idx = (i + (s << log_new_n)) % (1 << log_n);
                        let mut t = a[idx];
                        t *= elt;
                        tmp[i] += t;
                        elt *= omega_step;
                    }
                    elt *= omega_j;
                }

                // Perform sub-FFT
                serial_fft(tmp, new_omega, log_new_n);
            });
        }
    })
    .unwrap();

    // Unshuffle
    let mask = (1 << log_cpus) - 1;
    for (idx, a) in a.iter_mut().enumerate() {
        *a = tmp[idx & mask][idx >> log_cpus];
    }
}

#[test]
fn test_fft() {
    use crate::fields::Fp;

    let a = (0..1000).map(Fp::from_u64).collect::<Vec<_>>();
    let b = (0..1000)
        .map(|i| Fp::from_u64(i + 1000))
        .collect::<Vec<_>>();

    let mut naive_product = vec![Fp::zero(); (a.len() + b.len()) - 1];
    for (i, a) in a.iter().enumerate() {
        for (j, b) in b.iter().enumerate() {
            naive_product[i + j] += (*a) * (*b);
        }
    }
    let valid_product = multiply_polynomials(a, b);

    assert_eq!(valid_product, naive_product);
}

#[derive(Copy, Clone)]
pub struct Challenge(pub(crate) u128);

pub fn get_challenge_scalar<F: Field>(challenge: Challenge) -> F {
    let mut acc = (F::ZETA + F::one()).double();

    // i = 63
    // i * 2 = 126
    // i * 2 + 1 = 127
    for i in (0..64).rev() {
        let should_negate = ((challenge.0 >> ((i << 1) + 1)) & 1) == 1;
        let should_endo = ((challenge.0 >> (i << 1)) & 1) == 1;

        let q = if should_negate { -F::one() } else { F::one() };
        let q = if should_endo { q * F::ZETA } else { q };
        acc = acc + q + acc;
    }

    acc
}

pub fn compute_b<F: Field>(x: F, challenges: &[F], challenges_inv: &[F]) -> F {
    assert!(!challenges.is_empty());
    assert_eq!(challenges.len(), challenges_inv.len());
    if challenges.len() == 1 {
        return *challenges_inv.last().unwrap() + *challenges.last().unwrap() * x;
    } else {
        return (*challenges_inv.last().unwrap() + *challenges.last().unwrap() * x)
            * compute_b(
                x.square(),
                &challenges[0..(challenges.len() - 1)],
                &challenges_inv[0..(challenges.len() - 1)],
            );
    }
}

pub fn compute_s<F: Field>(challenges_sq: &[F], allinv: F) -> Vec<F> {
    let lg_n = challenges_sq.len();
    let n = 1 << lg_n;

    let mut s = Vec::with_capacity(n);
    s.push(allinv);
    for i in 1..n {
        let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
        let k = 1 << lg_i;
        let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
        s.push(s[i - k] * u_lg_i_sq);
    }

    s
}

pub fn compute_g<C: CurveAffine>(
    generators: &[C],
    challenges_sq: &[C::Scalar],
    allinv: C::Scalar,
) -> C::Projective {
    let s = compute_s::<C::Scalar>(challenges_sq, allinv);

    assert_eq!(generators.len(), s.len());

    multiexp(&s, &generators)
}

#[test]
fn test_compute_b() {
    use crate::Fp;
    let k = 4;
    let x = Fp::from_u64(100).invert().unwrap();

    let mut powers_of_x = vec![];
    let mut cur = Fp::one();
    for _ in 0..(1 << k) {
        powers_of_x.push(cur);
        cur *= x;
    }

    let mut challenges = vec![];
    let mut challenges_inv = vec![];

    let mut b = powers_of_x.clone();
    let mut cur_k = k;
    let mut curchallenge = Fp::from_u64(109).invert().unwrap();
    while b.len() > 1 {
        let l = 1 << (cur_k - 1);
        let curchallenge_inv = curchallenge.invert().unwrap();
        challenges.push(curchallenge);
        challenges_inv.push(curchallenge_inv);

        for j in 0..l {
            b[j] = (b[j] * curchallenge_inv) + (b[j + l] * curchallenge);
        }

        b.truncate(l);

        cur_k -= 1;
        curchallenge = (curchallenge + Fp::from_u64(129)).square();
    }

    assert_eq!(b[0], compute_b(x, &challenges, &challenges_inv));
}

/// Compute a + b + carry, returning the result and the new carry over.
#[inline(always)]
pub const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + (b as u128) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}

/// Compute a - (b + borrow), returning the result and the new borrow.
#[inline(always)]
pub const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
    (ret as u64, (ret >> 64) as u64)
}

/// Compute a + (b * c) + carry, returning the result and the new carry over.
#[inline(always)]
pub const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}

macro_rules! impl_add_binop_specify_output {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> Add<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: &'b $rhs) -> $output {
                &self + rhs
            }
        }

        impl<'a> Add<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs) -> $output {
                self + &rhs
            }
        }

        impl Add<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs) -> $output {
                &self + &rhs
            }
        }
    };
}

macro_rules! impl_sub_binop_specify_output {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> Sub<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: &'b $rhs) -> $output {
                &self - rhs
            }
        }

        impl<'a> Sub<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs) -> $output {
                self - &rhs
            }
        }

        impl Sub<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs) -> $output {
                &self - &rhs
            }
        }
    };
}

macro_rules! impl_binops_additive_specify_output {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl_add_binop_specify_output!($lhs, $rhs, $output);
        impl_sub_binop_specify_output!($lhs, $rhs, $output);
    };
}

macro_rules! impl_binops_multiplicative_mixed {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> Mul<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: &'b $rhs) -> $output {
                &self * rhs
            }
        }

        impl<'a> Mul<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                self * &rhs
            }
        }

        impl Mul<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                &self * &rhs
            }
        }
    };
}

macro_rules! impl_binops_additive {
    ($lhs:ident, $rhs:ident) => {
        impl_binops_additive_specify_output!($lhs, $rhs, $lhs);

        impl SubAssign<$rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: $rhs) {
                *self = &*self - &rhs;
            }
        }

        impl AddAssign<$rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: $rhs) {
                *self = &*self + &rhs;
            }
        }

        impl<'b> SubAssign<&'b $rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self - rhs;
            }
        }

        impl<'b> AddAssign<&'b $rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self + rhs;
            }
        }
    };
}

macro_rules! impl_binops_multiplicative {
    ($lhs:ident, $rhs:ident) => {
        impl_binops_multiplicative_mixed!($lhs, $rhs, $lhs);

        impl MulAssign<$rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: $rhs) {
                *self = &*self * &rhs;
            }
        }

        impl<'b> MulAssign<&'b $rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self * rhs;
            }
        }
    };
}
