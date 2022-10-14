use super::*;

use crate::types::{Balance, Price};

use num_traits::{Bounded, One, Pow, Zero};
use rug::Rational;
use sp_arithmetic::{traits::Saturating, FixedPointNumber, FixedU128};

macro_rules! assert_eq_approx {
	( $x:expr, $y:expr, $z:expr, $r:expr) => {{
		let diff = if $x >= $y { $x - $y } else { $y - $x };
		if diff > $z {
			panic!("\n{} not equal\nleft: {:?}\nright: {:?}\n", $r, $x.to_f64(), $y.to_f64());
		}
	}};
}

#[test]
fn weighted_averages_work() {
    let alpha = smoothing_from_period(7);
    debug_assert!(alpha <= Price::one());

    // price
    let start_price = 4.into();
    let incoming_price = 8.into();
    let next_price = price_weighted_average(start_price, incoming_price, alpha);
    assert_eq!(next_price, 5.into());

    let start_price = Price::saturating_from_rational(4, 100);
    let incoming_price = Price::saturating_from_rational(8, 100);
    let next_price = price_weighted_average(start_price, incoming_price, alpha);
    assert_eq!(next_price, Price::saturating_from_rational(5, 100));

    // balance
    let start_balance = 4u128;
    let incoming_balance = 8u128;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, alpha);
    assert_eq!(next_balance, 5u128);

    // volume
    let start_volume = (4u128, 1u128, 8u128, 0u128);
    let incoming_volume = (8u128, 1u128, 4u128, 0u128);
    let next_volume = volume_weighted_average(start_volume, incoming_volume, alpha);
    assert_eq!(next_volume, (5u128, 1u128, 7u128, 0u128));
}

#[test]
fn price_weighted_average_boundary_values() {
    let alpha = Price::saturating_from_rational(1, 2);
    debug_assert!(alpha <= Price::one());

    // previously zero, incoming max
    let next_price = price_weighted_average(Price::zero(), Price::max_value(), alpha);
    assert_eq!(next_price, Price::max_value() / 2.into());
    // the oracle is biased towards the previous value
    let bias = Price::saturating_from_rational(1, Price::DIV);
    // previously max, incoming zero
    let next_price = price_weighted_average(Price::max_value(), Price::zero(), alpha);
    assert_eq!(next_price, Price::max_value() / 2.into() + bias);
}

#[test]
fn balance_weighed_average_does_not_saturate_on_big_balances() {
    let alpha = Price::one();

    let start_balance = u128::MAX;
    let incoming_balance = u128::MAX;
    let next_balance = balance_weighted_average(start_balance, incoming_balance, alpha);
    assert_eq!(next_balance, incoming_balance);
}

#[test]
fn exp_smoothing_works() {
    let smoothing = smoothing_from_period(7);
    let alpha = exp_smoothing(smoothing, 10);
    let expected_complement = FixedU128::saturating_from_rational(3_u8, 4_u8).saturating_pow(10);
    assert_eq!(alpha, FixedU128::one() - expected_complement);
}

#[test]
fn smoothing_from_period_works() {
    let period = 0;
    let smoothing = smoothing_from_period(period);
    assert_eq!(smoothing, FixedU128::one());

    let period = 3;
    let smoothing = smoothing_from_period(period);
    assert_eq!(smoothing, FixedU128::saturating_from_rational(1, 2));

    let period = 999;
    let smoothing = smoothing_from_period(period);
    assert_eq!(smoothing, FixedU128::saturating_from_rational(2, 1_000));
}

use high_precision::fixed_to_rational;
#[test]
fn exponential_smoothing() {
    let smoothing = smoothing_from_period(1_000_800); // weekly oracle
    let iterations = 100_000;
    let exp = exp_smoothing(smoothing, iterations);
    let rug_exp = high_precision::rug_exp_smoothing(smoothing, iterations);

    let difference = fixed_to_rational(exp.clone()) - rug_exp.clone();
    println!("difference: {:?}", difference.to_f64());
    println!("epsilon: {:?}", FixedU128::from_inner(1).to_float());
    
    let tolerance = fixed_to_rational(FixedU128::from_float(2e14));
    assert_eq_approx!(fixed_to_rational(exp), rug_exp.clone(), tolerance, "high precision should be equal to low precision within low precision tolerance");
    assert!(false);
}

#[test]
fn exponential_smoothing_small_period() {
    let smoothing = FixedU128::from_float(0.974);
    let iterations = 100_000;
    let exp = exp_smoothing(smoothing, iterations);
    let rug_exp = high_precision::rug_exp_smoothing(smoothing, iterations);

    let difference = fixed_to_rational(exp.clone()) - rug_exp.clone();
    println!("difference: {:?}", difference.to_f64());
    println!("epsilon: {:?}", FixedU128::from_inner(1).to_float());
    
    let tolerance = fixed_to_rational(FixedU128::from_float(2e14));
    assert_eq_approx!(fixed_to_rational(exp), rug_exp.clone(), tolerance, "high precision should be equal to low precision within low precision tolerance");
    assert!(false);
}

#[test]
fn exponential_accuracy() {
    let smoothing = smoothing_from_period(100_800); // weekly oracle
    let rug_smoothing = fixed_to_rational(smoothing);
    let iterations = 100_000;
    let start_balance = 1e12 as Balance;
    let incoming_balance = 1e21 as Balance;
    let mut next_balance = start_balance;
    let mut next_rug_balance = start_balance;
    for i in 0..iterations {
        next_balance = balance_weighted_average(next_balance, incoming_balance, smoothing);
        next_rug_balance = high_precision::rug_balance_ma(next_rug_balance, incoming_balance, rug_smoothing.clone()).to_u128().unwrap();
        if i % 100_000 == 0 {
            println!("iwa {}: {}", i, next_balance);
            println!("rug {}: {}", i, next_rug_balance);
            println!("");
        }
    }
    let exponential_balance = iterated_balance_ema(iterations, start_balance, incoming_balance, smoothing);
    let rug_exp_smoothing = high_precision::rug_exp_smoothing(smoothing, iterations);
    let exponential_rug_balance = high_precision::rug_balance_ma(start_balance, incoming_balance, rug_exp_smoothing).to_u128().unwrap();
    println!("===== final:");
    println!("initial balance: {}", start_balance);
    println!(" target balance: {}", incoming_balance);
    println!("       iterated: {}", next_balance);
    println!("    exponential: {}", exponential_balance);
    println!("   rug iterated: {}", next_rug_balance);
    println!("rug exponential: {}", exponential_rug_balance);

    assert_eq!(next_balance, exponential_balance);
}
