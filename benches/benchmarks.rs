use criterion::{black_box, criterion_group, criterion_main, Criterion};

use fixed::traits::{FixedUnsigned, ToFixed};
use fixed::types::U89F39 as FixedBalance;

use hydra_dx_math::to_u256;

use hydra_dx_math::transcendental::{get_y_stableswap, pow, get_d, get_y_constant_product};
use hydra_dx_math::xyk::{calculate_out_given_in, calculate_spot_price};
use hydra_dx_math::types::Balance;
use hydra_dx_math::fee::calculate_pool_trade_fee;

#[cfg(feature = "p12")]
use hydra_dx_math::p12::p12::{Balance256, pow as pow12};
#[cfg(feature = "p12")]
use hydra_dx_math::types::HYDRA_ONE;
#[cfg(feature = "p12")]
use std::convert::TryInto;

use num_traits::{One, Zero};
use rand::distributions::uniform::SampleUniform;
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro256Plus};
use std::ops::{AddAssign, BitOrAssign, ShlAssign, Shr, ShrAssign};
use primitive_types::U256;


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

#[cfg(feature = "p12")]
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

fn bench_pow<F>(c: &mut Criterion)
where
    F: FixedUnsigned,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
    Standard: Distribution<F::Bits>,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> =
        gen_tuple_dataset(DATASET_SIZE, &F::from_num(0).to_bits(), &F::from_num(2).to_bits());

    let fixed_dataset: Vec<(F, F)> = bits_dataset.clone()
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

    #[cfg(feature = "p12")]
    let balance_dataset: Vec<(Balance256, Balance256)> = bits_dataset
        .into_iter()
        .map(|(l, r)| (F::from_bits(l), F::from_bits(r)))
        .map(|(l, r)| (convert_from_fixed(l).unwrap(), convert_from_fixed(r).unwrap()))
        .collect();

    #[cfg(feature = "p12")]
    c.bench_function("pow12", |b| {
        b.iter(|| {
            for (o, e) in &balance_dataset{
                pow12(black_box(*o), black_box(*e)).unwrap();
            }
        })
    });
}

fn bench_get_d<F>(c: &mut Criterion)
where
    F: FixedUnsigned,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
    Standard: Distribution<F::Bits>,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> =
        gen_tuple_dataset(DATASET_SIZE, &F::from_num(0).to_bits(), &F::from_num(2).to_bits());

    let fixed_xp: Vec<(F, F)> = bits_dataset.clone()
        .into_iter()
        .map(|(l, r)| (F::from_bits(l), F::from_bits(r)))
        .collect();

    let xp = [to_u256!(1_000_000_000_000_000_i128), to_u256!(10_000_000_000_000_000_i128)];
    let a = to_u256!(200_i128);

    // This represents worst case if we require at least a single unit in the pool for each token.
    let xp2 = [to_u256!(1_000_000_000_000_i128), to_u256!(999_000_000_000_000_000_000_000_i128)];

    let input = [(xp, a), (xp2, a)];

    c.bench_function("get_d", |b| {
        b.iter(|| {
            for (xp, a) in input{
                        get_d(xp, a).unwrap();
            }
        })
    });
}

fn bench_get_y_stableswap<F>(c: &mut Criterion)
where
    F: FixedUnsigned,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
    Standard: Distribution<F::Bits>,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> =
        gen_tuple_dataset(DATASET_SIZE, &F::from_num(0).to_bits(), &F::from_num(2).to_bits());

    let fixed_xp: Vec<(F, F)> = bits_dataset.clone()
        .into_iter()
        .map(|(l, r)| (F::from_bits(l), F::from_bits(r)))
        .collect();

    let i = 0_i128;
    let j = 1_i128;
    let x = to_u256!(1_010_000_000_000_000_i128);
    let xp = [to_u256!(1_000_000_000_000_000_i128), to_u256!(10_000_000_000_000_000_i128)];
    let a = to_u256!(200_i128);

    // This represents worst case if we require at least a single unit in the pool for each token.
    let xp2 = [to_u256!(1_000_000_000_000_i128), to_u256!(999_000_000_000_000_000_000_000_i128)];
    let x2 = to_u256!(1_010_000_000_000_i128);


    //let input = [(xp, a), (xp2, a)];
    //let input = [(i, j, x, xp, a)];
    let input = [(i, j, x2, xp2, a)];

    c.bench_function("get_y_stableswap", |b| {
        b.iter(|| {
            for (i, j, x, xp, a) in input{
                        get_y_stableswap(i, j, x, xp, a).unwrap();
            }
        })
    });
}

fn bench_get_y_constant_product(c: &mut Criterion)
{
    let i = 0_i128;
    let j = 1_i128;
    let x = to_u256!(1_010_000_000_000_000_i128);
    let xp = [to_u256!(1_000_000_000_000_000_i128), to_u256!(10_000_000_000_000_000_i128)];

    // This represents worst case if we require at least a single unit in the pool for each token.
    let x2 = 1_010_000_000_000_u128;
    let xp2 = [1_000_000_000_000_u128, 999_000_000_000_000_000_000_000_u128];

    //let input = [(xp, a), (xp2, a)];
    //let input = [(i, j, x, xp, a)];
    let input = [(i, j, x2, xp2)];

    c.bench_function("get_y_constant_product", |b| {
        b.iter(|| {
            for (i, j, x, xp) in input{
                        get_y_constant_product(i, j, x, xp).unwrap();
            }
        })
    });
}

fn bench_calculate_out_given_in<F>(c: &mut Criterion)
where
    F: FixedUnsigned,
    F::Bits:
        Zero + One + PartialEq + SampleUniform + Shr + ShrAssign + ShlAssign + ToFixed + Copy + AddAssign + BitOrAssign,
    Standard: Distribution<F::Bits>,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> =
        gen_tuple_dataset(DATASET_SIZE, &F::from_num(0).to_bits(), &F::from_num(2).to_bits());

    let fixed_xp: Vec<(F, F)> = bits_dataset.clone()
        .into_iter()
        .map(|(l, r)| (F::from_bits(l), F::from_bits(r)))
        .collect();

    let i = 0 as usize;
    let j = 1 as usize;
    let x = 1_010_000_000_000_000 as Balance;
    let xp = [1_000_000_000_000_000 as Balance, 10_000_000_000_000_000 as Balance];

    // This represents worst case if we require at least a single unit in the pool for each token.
    let x2 = 1_010_000_000_000 as Balance;
    let xp2 = [1_000_000_000_000 as Balance, 999_000_000_000_000_000_000_000 as Balance];

    //let input = [(xp, a), (xp2, a)];
    //let input = [(i, j, x, xp, a)];
    let input = [(i, j, x2, xp2)];

    c.bench_function("calculate_out_given_in", |b| {
        b.iter(|| {
            for (i, j, x, xp) in input{
                        calculate_out_given_in(xp[i],
                                               xp[j],
                                               x).unwrap();
            }
        })
    });
}

//calculate_pool_trade_fee(amount: Balance, fee: (u32, u32))
fn bench_calculate_pool_trade_fee(c: &mut Criterion)
{

    let amount = 100_000_000_000_000 as Balance;
    let fee1 = 1 as u32;
    let fee2 = 100 as u32;

    let input = [(amount, fee1, fee2)];

    c.bench_function("calculate_pool_trade_fee", |b| {
        b.iter(|| {
            for (amount, fee1, fee2) in input{
                        calculate_pool_trade_fee(amount, (fee1, fee2)).unwrap();
            }
        })
    });
}

//calculate_pool_trade_fee(amount: Balance, fee: (u32, u32))
fn bench_calculate_spot_price(c: &mut Criterion)
{

    let reserve1 = 100_000_000_000_000_000 as Balance;
    let reserve2 = 100_000_000_000_000_000 as Balance;
    let amount = 10 as Balance;

    let input = [(reserve1, reserve2, amount)];

    c.bench_function("calculate_spot_price", |b| {
        b.iter(|| {
            for (reserve1, reserve2, amount) in input{
                        calculate_spot_price(reserve1, reserve2, amount).unwrap();
            }
        })
    });
}

//criterion_group!(benches, bench_get_d<FixedBalance>);
criterion_group!(benches,
    bench_get_y_stableswap<FixedBalance>,
    //bench_get_y_constant_product,  // ~ 100ns for U256
    //bench_calculate_out_given_in<FixedBalance>,  // ~ 100ns
    //bench_calculate_pool_trade_fee,  //pretty trivial, on the order of 10 ns
    //bench_calculate_spot_price,  // ~ 100ns
);
criterion_main!(benches);
