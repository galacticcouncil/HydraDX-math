use criterion::{black_box, criterion_group, criterion_main, Bencher, Criterion};

use fixed::traits::{FixedUnsigned, ToFixed};
use fixed::types::U89F39 as FixedBalance;
use hydra_dx_math::p12::p12::pow as pow12;
use hydra_dx_math::p12::p12::Balance256;
use hydra_dx_math::to_u256;
use hydra_dx_math::transcendental::pow;
use hydra_dx_math::types::Balance;
use hydra_dx_math::types::HYDRA_ONE;

use num_traits::{One, Zero};
use rand::distributions::uniform::SampleUniform;
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro256Plus};
use std::convert::TryInto;
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

fn gen_tuple_dataset<T>(cap: usize, min: &T, max: &T) -> Vec<(T, T)>
where
    T: Zero + One + PartialEq + SampleUniform,
    Standard: Distribution<T>,
{
    let mut rng: Xoshiro256Plus = Xoshiro256Plus::seed_from_u64(SEED);
    (0..cap)
        .map(|_| (rng.gen_range(min, max), gen_non_zero(&mut rng, min, max)))
        .collect()
}

fn convert_from_fixed<F>(value: F) -> Option<Balance256>
where
    F: FixedUnsigned,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
{
    let w: Balance = value.int().to_num();
    let frac: Balance = value.frac().checked_mul(F::from_num(HYDRA_ONE))?.to_num();

    let r = w.checked_mul(HYDRA_ONE)?.checked_add(frac)?;
    Some(Balance256::from(r))
}

fn bench_pow12<F>(c: &mut Criterion)
where
    F: FixedUnsigned,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
    Standard: Distribution<F::Bits>,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> =
        gen_tuple_dataset(DATASET_SIZE, &F::from_num(0).to_bits(), &F::from_num(2).to_bits());

    let fixed_dataset: Vec<(Balance256, Balance256)> = bits_dataset
        .into_iter()
        .map(|(l, r)| (F::from_bits(l), F::from_bits(r)))
        .map(|(l, r)| (convert_from_fixed(l).unwrap(), convert_from_fixed(r).unwrap()))
        .collect();

    c.bench_function("pow12", |b| {
        b.iter(|| {
            for (o, e) in &fixed_dataset {
                pow12(black_box(*o), black_box(*e)).unwrap();
            }
        })
    });
}

fn bench_pow<F>(c: &mut Criterion)
where
    F: FixedUnsigned,
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

criterion_group!(benches, bench_pow<FixedBalance>, bench_pow12<FixedBalance>);
criterion_main!(benches);
