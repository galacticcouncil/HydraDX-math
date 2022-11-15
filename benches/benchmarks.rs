use criterion::{black_box, criterion_group, criterion_main, Criterion};

use fixed::traits::{FixedUnsigned, ToFixed};
use fixed::types::U89F39 as FixedBalance;

use hydra_dx_math::transcendental::pow;

use num_traits::{One, Zero};
use rand::distributions::uniform::SampleUniform;
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro256Plus};
use std::ops::{AddAssign, BitOrAssign, ShlAssign, Shr, ShrAssign};

const SEED: u64 = 42_069;
const DATASET_SIZE: usize = 10;

fn gen_non_zero<T, R>(rng: &mut R, min: &T, max: &T) -> T
where
    R: Rng + ?Sized,
    T: Zero + One + PartialEq + SampleUniform + PartialOrd + Copy,
    Standard: Distribution<T>,
{
    let value: T = rng.gen_range(*min..*max);
    if value != T::zero() {
        value
    } else {
        T::one()
    }
}

fn gen_tuple_dataset<T>(cap: usize, min: &T, max: &T) -> Vec<(T, T)>
where
    T: Zero + One + PartialEq + SampleUniform + PartialOrd + Copy,
    Standard: Distribution<T>,
{
    let mut rng: Xoshiro256Plus = Xoshiro256Plus::seed_from_u64(SEED);
    (0..cap)
        .map(|_| (rng.gen_range(*min..*max), gen_non_zero(&mut rng, min, max)))
        .collect()
}

fn bench_pow<F>(c: &mut Criterion)
where
    F: FixedUnsigned + One,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
    Standard: Distribution<F::Bits>,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> =
        gen_tuple_dataset(DATASET_SIZE, &F::from_num(0).to_bits(), &F::from_num(2).to_bits());

    let fixed_dataset: Vec<(F, F)> = bits_dataset
        .into_iter()
        .map(|(l, r)| (F::from_bits(l), F::from_bits(r)))
        .collect();

    c.bench_function("pow", |b| {
        b.iter(|| {
            for (o, e) in &fixed_dataset {
                pow::<F, F>(black_box(*o), black_box(*e)).unwrap();
            }
        })
    });
}

use rug::{Integer, Rational};
use num_traits::Pow;
use rug::ops::PowAssign;

fn round(r: &mut Rational) {
    r.mutate_numer_denom(|n, d| {
        let n_digits = n.significant_digits::<bool>();
        let d_digits = d.significant_digits::<bool>();
        if n_digits > 256 || d_digits > 256 {
            let shift = n_digits.saturating_sub(256).max(d_digits.saturating_sub(256));
            n.shr_assign(shift);
            d.shr_assign(shift);
        }
    });
}

fn rational_pow(r: Rational, i: u32) -> Rational {
    r.pow(i)
}

fn stepwise_pow(mut r: Rational, i: u32) -> Rational {
    if i <= 256 {
        return r.pow(i);
    }
    let next_power = i.next_power_of_two();
    let mut iter = if next_power == i { i } else { next_power / 2 };
    let rest = i - iter;
    let mut res_rest = stepwise_pow(r.clone(), rest);
    round(&mut res_rest);
    while iter > 1 {
        iter /= 2;
        r.pow_assign(2);
        round(&mut r);
    }
    r * res_rest
}

#[test]
fn stepwise_pow_close_enough() {
    let num = Rational::one() - Rational::from((2u64, 100_001));

    let res_pow = rational_pow(num.clone(), 65536);
    let res_step = stepwise_pow(num.clone(), 65536);
    dbg!(res_pow.clone().to_f64());
    dbg!(res_step.clone().to_f64());
    dbg!((res_pow.clone() - res_step.clone()).abs().to_f64());
    dbg!(Rational::from((1, u128::MAX)).to_f64());
    assert!((res_pow - res_step).abs() < Rational::from((1, u128::MAX)));
}

fn bench_rational_pow(c: &mut Criterion)
{
    let num = Rational::one() - Rational::from((2u64, 100_001));
    c.bench_function("pow_rational 16", |b| {
        b.iter_with_large_drop(|| {
            rational_pow(black_box(num.clone()), black_box(16))
        })
    });

    c.bench_function("pow_rational 256", |b| {
        b.iter_with_large_drop(|| {
            rational_pow(black_box(num.clone()), black_box(256))
        })
    });

    c.bench_function("pow_rational 1k", |b| {
        b.iter_with_large_drop(|| {
            rational_pow(black_box(num.clone()), black_box(1_000))
        })
    });

    c.bench_function("pow_rational 10k", |b| {
        b.iter_with_large_drop(|| {
            rational_pow(black_box(num.clone()), black_box(10_000))
        })
    });

    c.bench_function("pow_rational 65536", |b| {
        b.iter_with_large_drop(|| {
            rational_pow(black_box(num.clone()), black_box(65536))
        })
    });

    c.bench_function("pow_rational 100_000", |b| {
        b.iter_with_large_drop(|| {
            rational_pow(black_box(num.clone()), black_box(100_000))
        })
    });

    c.bench_function("pow_stepwise 16", |b| {
        b.iter_with_large_drop(|| {
            stepwise_pow(black_box(num.clone()), black_box(16))
        })
    });

    c.bench_function("pow_stepwise 256", |b| {
        b.iter_with_large_drop(|| {
            stepwise_pow(black_box(num.clone()), black_box(256))
        })
    });

    c.bench_function("pow_stepwise 65536", |b| {
        b.iter_with_large_drop(|| {
            stepwise_pow(black_box(num.clone()), black_box(65536))
        })
    });

    c.bench_function("pow_stepwise 100_000", |b| {
        b.iter_with_large_drop(|| {
            stepwise_pow(black_box(num.clone()), black_box(100_000))
        })
    });
}

criterion_group!(benches, bench_pow<FixedBalance>, bench_rational_pow);
criterion_main!(benches);
