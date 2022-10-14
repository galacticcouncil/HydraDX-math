use super::*;

use crate::types::Price;

use num_traits::{Bounded, One, Zero};
use sp_arithmetic::{traits::Saturating, FixedPointNumber, FixedU128};

#[test]
fn ema_works() {
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
fn price_ma_boundary_values() {
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
fn ema_does_not_saturate_on_big_balances() {
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
    let alpha = smoothing_from_period(period);
    assert_eq!(alpha, FixedU128::one());

    let period = 3;
    let alpha = smoothing_from_period(period);
    assert_eq!(alpha, FixedU128::saturating_from_rational(1, 2));

    let period = 999;
    let alpha = smoothing_from_period(period);
    assert_eq!(alpha, FixedU128::saturating_from_rational(2, 1_000));
}
