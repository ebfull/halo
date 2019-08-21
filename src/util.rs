use crate::fields::Field;
use crossbeam_utils::thread;
use num_cpus;

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
        let w_m = omega.pow((n / (2 * m)) as u64);

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
    let new_omega = omega.pow(num_cpus as u64);

    thread::scope(|scope| {
        let a = &*a;

        for (j, tmp) in tmp.iter_mut().enumerate() {
            scope.spawn(move |_| {
                // Shuffle into a sub-FFT
                let omega_j = omega.pow(j as u64);
                let omega_step = omega.pow((j as u64) << log_new_n);

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
