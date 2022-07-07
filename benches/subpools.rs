use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::fmt::Debug;

use fixed::traits::{FixedUnsigned, ToFixed};
use fixed::types::U89F39 as FixedBalance;

use hydra_dx_math::subpools::math::{calculate_stable_out_given_lrna_in, calculate_stable_out_given_stable_in};
use hydra_dx_math::transcendental::pow;

use hydra_dx_math::stableswap::math::calculate_out_given_in;
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
    T: Zero + One + PartialEq + SampleUniform,
    Standard: Distribution<T>,
{
    let value: T = rng.gen_range(min, max);
    if value != T::zero() {
        value
    } else {
        T::one()
    }
}

fn gen_reserves<T>(cap: usize, min: &T, max: &T) -> Vec<(T, T)>
where
    T: Zero + One + PartialEq + SampleUniform,
    Standard: Distribution<T>,
{
    let mut rng: Xoshiro256Plus = Xoshiro256Plus::seed_from_u64(SEED);
    (0..cap)
        .map(|_| (rng.gen_range(min, max), gen_non_zero(&mut rng, min, max)))
        .collect()
}

fn gen_trade_amount<T>(cap: usize, min: &T, max: &T) -> Vec<T>
where
    T: Zero + One + PartialEq + SampleUniform,
    Standard: Distribution<T>,
{
    let mut rng: Xoshiro256Plus = Xoshiro256Plus::seed_from_u64(SEED);
    (0..cap).map(|_| rng.gen_range(min, max)).collect()
}

fn bench_stableswap<F>(c: &mut Criterion)
where
    F: Zero
        + One
        + PartialEq
        + SampleUniform
        + Shr
        + ShrAssign
        + ShlAssign
        + ToFixed
        + Copy
        + AddAssign
        + BitOrAssign
        + From<u128>
        + Into<u128>
        + Debug,
    Standard: Distribution<F>,
{
    let reserves_in: Vec<(F, F)> = gen_reserves(DATASET_SIZE, &F::from(0u128), &F::from(1000_000_000_000_000u128));

    let reserves_out: Vec<(F, F)> = gen_reserves(DATASET_SIZE, &F::from(0u128), &F::from(1000_000_000_000_000u128));

    let trade_amounts: Vec<F> = gen_trade_amount(DATASET_SIZE, &F::from(0u128), &F::from(1000_000_000_000_000u128));
    let reserve_lrna_in: Vec<F> = gen_trade_amount(DATASET_SIZE, &F::from(0u128), &F::from(1000_000_000_000_000u128));
    let reserve_lrna_out: Vec<F> = gen_trade_amount(DATASET_SIZE, &F::from(0u128), &F::from(1000_000_000_000_000u128));

    c.bench_function("calculate_stable_out_given_lrna_in", |b| {
        b.iter(|| {
            for ((reserve, amount_in), lrna) in reserves_in
                .iter()
                .zip(trade_amounts.clone())
                .zip(reserve_lrna_in.clone())
            {
                calculate_stable_out_given_lrna_in::<127, 63>(
                    black_box(lrna.into()),
                    black_box(&[reserve.0.into(), reserve.1.into()]),
                    black_box(amount_in.into()),
                    0,
                    100,
                    1000u128,
                );
            }
        })
    });
    c.bench_function("calculate_stable_out_given_stable_in", |b| {
        b.iter(|| {
            for idx in 0..DATASET_SIZE {
                calculate_stable_out_given_stable_in::<127, 63>(
                    black_box(reserve_lrna_in[idx].into()),
                    black_box(&[reserves_in[idx].0.into(), reserves_in[idx].1.into()]),
                    black_box(reserve_lrna_out[idx].into()),
                    black_box(&[reserves_out[idx].0.into(), reserves_out[idx].1.into()]),
                    black_box(trade_amounts[idx].into()),
                    0,
                    1,
                    100,
                    1000,
                    1000u128,
                );
            }
        })
    });

    c.bench_function("calculate_out_given_in", |b| {
        b.iter(|| {
            for ((reserve, amount_in), lrna) in reserves_in
                .iter()
                .zip(trade_amounts.clone())
                .zip(reserve_lrna_in.clone())
            {
                calculate_out_given_in::<127, 63>(
                    black_box(reserve.0.into()),
                    black_box(reserve.1.into()),
                    black_box(amount_in.into()),
                    100,
                    1000u128,
                );
            }
        })
    });
}

criterion_group!(benches, bench_stableswap<u128>);
criterion_main!(benches);
