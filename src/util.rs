use crate::{Curve, Field};
use crossbeam_utils::thread;
use num_cpus;

pub fn compute_inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    let mut acc = F::zero();

    for (a, b) in a.iter().zip(b.iter()) {
        acc = acc + ((*a) * (*b));
    }

    acc
}

/// TODO: Naive multiexp for now.
pub fn multiexp<F: Field, C: Curve<Scalar = F>>(coeffs: &[C::Scalar], bases: &[C]) -> C {
    assert_eq!(coeffs.len(), bases.len());

    let num_cpus = num_cpus::get();
    if coeffs.len() > num_cpus {
        let chunk = coeffs.len() / num_cpus;
        let num_chunks = coeffs.chunks(chunk).len();
        let mut results = vec![C::zero(); num_chunks];
        thread::scope(|scope| {
            let chunk = coeffs.len() / num_cpus;

            for ((coeffs, bases), acc) in coeffs
                .chunks(chunk)
                .zip(bases.chunks(chunk))
                .zip(results.iter_mut())
            {
                scope.spawn(move |_| {
                    for (coeff, base) in coeffs.iter().zip(bases.iter()) {
                        let coeff: F = *coeff;
                        let base: C = *base;
                        let product = base * coeff;
                        *acc = (*acc) + product;
                    }
                });
            }
        })
        .unwrap();
        results.iter().fold(C::zero(), |a, b| a + *b)
    } else {
        let mut acc = C::zero();
        for (coeff, base) in coeffs.iter().zip(bases.iter()) {
            let coeff: F = *coeff;
            let base: C = *base;
            let product = base * coeff;
            acc = acc + product;
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

    // Compute alpha, the 2^exp primitive root of unity
    let mut alpha = F::ALPHA;
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
                        *a = (*a) * (*b);
                    }
                });
            }
        })
        .unwrap();
    } else {
        for (a, b) in a.iter_mut().zip(b.iter()) {
            *a = (*a) * (*b);
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
                        *a = *a * minv;
                    }
                });
            }
        })
        .unwrap();
    } else {
        for a in a.iter_mut() {
            *a = *a * minv;
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
        let w_m = omega.pow(&[(n / (2 * m)) as u64, 0, 0, 0]);

        let mut k = 0;
        while k < n {
            let mut w = F::one();
            for j in 0..m {
                let mut t = a[(k + j + m) as usize];
                t = t * w;
                a[(k + j + m) as usize] = a[(k + j) as usize] - t;
                a[(k + j) as usize] = a[(k + j) as usize] + t;
                w = w * w_m;
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
                        t = t * elt;
                        tmp[i] = tmp[i] + t;
                        elt = elt * omega_step;
                    }
                    elt = elt * omega_j;
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

    let a = (0..1000).map(|i| Fp::from_u64(i)).collect::<Vec<_>>();
    let b = (0..1000)
        .map(|i| Fp::from_u64(i + 1000))
        .collect::<Vec<_>>();

    let mut naive_product = vec![Fp::zero(); (a.len() + b.len()) - 1];
    for (i, a) in a.iter().enumerate() {
        for (j, b) in b.iter().enumerate() {
            naive_product[i + j] = naive_product[i + j] + ((*a) * (*b));
        }
    }
    let valid_product = multiply_polynomials(a, b);

    assert_eq!(valid_product, naive_product);
}

pub fn compute_b<F: Field>(x: F, challenges: &[F], challenges_inv: &[F]) -> F {
    assert!(challenges.len() >= 1);
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
        cur = cur * x;
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

        cur_k = cur_k - 1;
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

// TODO: This should be upstreamed to subtle.
// See https://github.com/dalek-cryptography/subtle/pull/48
pub trait CtOptionExt<T> {
    /// Calls f() and either returns self if it contains a value,
    /// or returns the output of f() otherwise.
    fn or_else<F: FnOnce() -> subtle::CtOption<T>>(self, f: F) -> subtle::CtOption<T>;
}

impl<T: subtle::ConditionallySelectable> CtOptionExt<T> for subtle::CtOption<T> {
    fn or_else<F: FnOnce() -> subtle::CtOption<T>>(self, f: F) -> subtle::CtOption<T> {
        let is_none = self.is_none();
        let f = f();

        subtle::ConditionallySelectable::conditional_select(&self, &f, is_none)
    }
}
