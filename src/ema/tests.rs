use super::*;

use crate::transcendental::saturating_powi_high_precision;
use crate::types::fraction;
use crate::types::{Balance, Fraction, Price};
use high_precision::fraction_to_rational;

use num_traits::{Bounded, One, Zero};
use rug::Rational;
use sp_arithmetic::{FixedPointNumber, FixedU128};

macro_rules! assert_rational_approx_eq {
    ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x - $y } else { $y - $x };
        assert!(
            diff <= $z,
            "\n{}\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            $r,
            $x.to_f64(),
            $y.to_f64(),
            diff.to_f64(),
            $z.to_f64()
        );
    }};
}

macro_rules! assert_approx_eq {
    ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x - $y } else { $y - $x };
        assert!(
            diff <= $z,
            "\n{}\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            $r,
            $x,
            $y,
            diff,
            $z
        );
    }};
}

pub const TEN_MINUTES_PERIOD: u64 = 100;
pub const DAY_PERIOD: u64 = 14_400;
pub const WEEK_PERIOD: u64 = 100_800;

#[test]
fn weighted_averages_work_on_small_values_with_correct_ratios() {
    let smoothing = smoothing_from_period(7);

    // price
    let start_price = 4.into();
    let incoming_price = 8.into();
    let next_price = price_weighted_average(start_price, incoming_price, smoothing);
    assert_eq!(next_price, 5.into());

    let start_price = Price::saturating_from_rational(4, 100);
    let incoming_price = Price::saturating_from_rational(8, 100);
    let next_price = price_weighted_average(start_price, incoming_price, smoothing);
    assert_eq!(next_price, Price::saturating_from_rational(5, 100));

    // balance
    let start_balance = 4u128;
    let incoming_balance = 8u128;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
    assert_eq!(next_balance, 5u128);

    // volume
    let start_volume = (4u128, 1u128, 8u128, 0u128);
    let incoming_volume = (8u128, 1u128, 4u128, 0u128);
    let next_volume = volume_weighted_average(start_volume, incoming_volume, smoothing);
    assert_eq!(next_volume, (5u128, 1u128, 7u128, 0u128));
}

#[test]
fn balance_weighted_averages_work_on_typical_values_with_minutes_smoothing() {
    let smoothing = smoothing_from_period(TEN_MINUTES_PERIOD);
    let start_balance = 4_000_000_000_000u128;
    let incoming_balance = 8_000_000_000_000u128;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
    let expected_balance: Rational =
        start_balance + Rational::from((incoming_balance - start_balance, 1)) * 2 / (TEN_MINUTES_PERIOD + 1);
    assert_eq!(next_balance, expected_balance.round());
}

#[test]
fn balance_weighted_averages_work_on_typical_values_with_day_smoothing() {
    let smoothing = smoothing_from_period(DAY_PERIOD);
    let start_balance = 4_000_000_000_000u128;
    let incoming_balance = 8_000_000_000_000u128;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
    let expected: Rational =
        start_balance + Rational::from((incoming_balance - start_balance, 1)) * 2 / (DAY_PERIOD + 1);
    let tolerance = 1;
    let expected_balance = expected.round();
    assert_approx_eq!(
        next_balance,
        expected_balance.clone(),
        tolerance,
        "averaged balance values should be within 1 of the expected value"
    );
}

#[test]
fn balance_weighted_averages_work_on_typical_values_with_week_smoothing() {
    let smoothing = smoothing_from_period(WEEK_PERIOD);
    let start_balance = 4_000_000_000_000u128;
    let incoming_balance = 8_000_000_000_000u128;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
    let expected_balance: Rational =
        start_balance + Rational::from((incoming_balance - start_balance, 1)) * 2 / (WEEK_PERIOD + 1);
    assert_eq!(next_balance, expected_balance.round());
}

#[test]
fn price_weighted_average_boundary_values() {
    let smoothing = fraction::frac(1, 2);
    debug_assert!(smoothing <= Fraction::one());

    // previously zero, incoming max
    let next_price = price_weighted_average(Price::zero(), Price::max_value(), smoothing);
    assert_eq!(next_price, Price::max_value() / 2.into());
    // the oracle is biased towards the previous value
    let bias = Price::saturating_from_rational(1, Price::DIV);
    // previously max, incoming zero
    let next_price = price_weighted_average(Price::max_value(), Price::zero(), smoothing);
    assert_eq!(next_price, Price::max_value() / 2.into() + bias);
}

#[test]
fn balance_weighed_average_does_not_saturate_on_big_balances() {
    let smoothing = Fraction::one();
    let start_balance = u128::MAX;
    let incoming_balance = u128::MAX;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
    assert_eq!(next_balance, incoming_balance);
}

#[test]
fn exp_smoothing_works() {
    let smoothing = smoothing_from_period(7);
    let alpha = exp_smoothing(smoothing, 10);
    let expected_complement: Fraction = saturating_powi_high_precision(fraction::frac(3, 4), 10);
    assert_eq!(alpha, Fraction::one() - expected_complement);
}

#[test]
fn smoothing_from_period_works() {
    let period = 0;
    assert_eq!(smoothing_from_period(period), Fraction::one());

    let period = 3;
    assert_eq!(smoothing_from_period(period), fraction::frac(1, 2));

    let period = 999;
    assert_eq!(smoothing_from_period(period), fraction::frac(2, 1_000));
}

#[test]
fn exponential_smoothing_small_period() {
    let smoothing = Fraction::from_num(0.999);
    let iterations = 100_000;
    let exp = exp_smoothing(smoothing, iterations);
    let rug_exp = high_precision::rug_exp_smoothing(high_precision::fraction_to_rational(smoothing), iterations);

    let tolerance = high_precision::fixed_to_rational(FixedU128::from_inner(1));
    assert_rational_approx_eq!(
        fraction_to_rational(exp),
        rug_exp.clone(),
        tolerance,
        "high precision should be equal to low precision within low precision tolerance"
    );
}

#[test]
fn accuracy_of_exponentiation_should_be_high_enough() {
    let smoothing = smoothing_from_period(100_800); // weekly oracle
    let rug_smoothing = fraction_to_rational(smoothing);
    let iterations = 100_000;
    let start_balance = 1e12 as Balance;
    let incoming_balance = 1e21 as Balance;
    let mut next_balance = start_balance;
    let mut next_rug_balance = start_balance;
    for i in 0..iterations {
        next_balance = balance_weighted_average(next_balance, incoming_balance, smoothing);
        next_rug_balance =
            high_precision::rug_balance_weighted_average(next_rug_balance, incoming_balance, rug_smoothing.clone())
                .to_u128()
                .unwrap();
        if i % 100_000 == 0 {
            println!("iwa {}: {}", i, next_balance);
            println!("rug {}: {}", i, next_rug_balance);
            println!("");
        }
    }
    let exponential_balance = iterated_balance_ema(iterations, start_balance, incoming_balance, smoothing);
    let rug_exp_smoothing =
        high_precision::rug_exp_smoothing(high_precision::fraction_to_rational(smoothing), iterations);
    let exponential_rug_balance =
        high_precision::rug_balance_weighted_average(start_balance, incoming_balance, rug_exp_smoothing)
            .to_u128()
            .unwrap();
    println!("===== final:");
    println!("initial balance: {}", start_balance);
    println!(" target balance: {}", incoming_balance);
    println!("       iterated: {}", next_balance);
    println!("    exponential: {}", exponential_balance);
    println!("   rug iterated: {}", next_rug_balance);
    println!("rug exponential: {}", exponential_rug_balance);

    let tolerance = 100;
    assert_approx_eq!(
        next_balance,
        exponential_rug_balance,
        tolerance,
        "iterated balance should be within tolerance of the high precision balance"
    );
    let tolerance = 1;
    assert_approx_eq!(
        exponential_balance,
        exponential_rug_balance,
        tolerance,
        "exponentially determined balance should be within tolerance of the high precision balance"
    );
}

#[test]
fn rug_balance_ema_works() {
    let history = vec![1e12 as Balance, 2e12 as Balance, 3e12 as Balance, 4e12 as Balance];
    let smoothing = FixedU128::from((1, 4));
    let expected = {
        let res =
            ((Rational::from(history[0]) * 3 / 4 + history[1] / 4) * 3 / 4 + history[2] / 4) * 3 / 4 + history[3] / 4;
        high_precision::into_rounded_integer(res)
    };
    let ema = high_precision::rug_balance_ema(history, high_precision::fixed_to_rational(smoothing));
    assert_eq!(expected, ema);
}

#[test]
fn rug_price_ema_works() {
    let history = vec![
        FixedU128::from((1, 8)),
        FixedU128::one(),
        FixedU128::from(8),
        FixedU128::from(4),
    ];
    let smoothing = FixedU128::from((1, 4));
    let expected = ((high_precision::fixed_to_rational(history[0]) * 3 / 4
        + high_precision::fixed_to_rational(history[1]) / 4)
        * 3
        / 4
        + high_precision::fixed_to_rational(history[2]) / 4)
        * 3
        / 4
        + high_precision::fixed_to_rational(history[3]) / 4;
    let ema = high_precision::rug_price_ema(history, high_precision::fixed_to_rational(smoothing));
    assert_eq!(expected, ema);
}
