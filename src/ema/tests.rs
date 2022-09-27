use super::*;

use crate::types::Price;

use num_traits::{One, Zero};
use sp_arithmetic::FixedPointNumber;

#[test]
fn ema_stays_stable_if_the_value_does_not_change() {
    let alpha = smoothing_from_period(7);
    debug_assert!(alpha <= Price::one());
    let complement = Price::one() - alpha;

    let start_price = Price::saturating_from_integer(4u32);
    let incoming_price = start_price;
    let next_price = price_ema(start_price, complement, incoming_price, alpha);
    assert_eq!(next_price, Some(start_price));
    let start_balance = 4u32.into();
    let incoming_balance = start_balance;
    let next_balance = balance_ema(start_balance, complement, incoming_balance, alpha);
    assert_eq!(next_balance, Some(start_balance));
}

#[test]
fn ema_works() {
    let alpha = smoothing_from_period(7);
    debug_assert!(alpha <= Price::one());
    let complement = Price::one() - alpha;

    // price
    let start_price = 4.into();
    let incoming_price = 8.into();
    let next_price = price_ema(start_price, complement, incoming_price, alpha).unwrap();
    assert_eq!(next_price, 5.into());

    let start_price = Price::saturating_from_rational(4, 100);
    let incoming_price = Price::saturating_from_rational(8, 100);
    let next_price = price_ema(start_price, complement, incoming_price, alpha).unwrap();
    assert_eq!(next_price, Price::saturating_from_rational(5, 100));

    // balance
    let start_balance = 4u128;
    let incoming_balance = 8u128;
    let next_balance = balance_ema(start_balance, complement, incoming_balance, alpha).unwrap();
    assert_eq!(next_balance, 5u128);

    // volume
    let start_volume = (
        4u128,
         1u128,
         8u128,
         0u128,
    );
    let incoming_volume = (
        8u128,
         1u128,
         4u128,
         0u128,
    );
    let next_volume = volume_ema(start_volume, complement, incoming_volume, alpha).unwrap();
    assert_eq!(
        next_volume,
        (
            5u128,
             1u128,
             7u128,
             0u128
        )
    );
}

#[test]
fn ema_does_not_saturate() {
    let alpha = Price::one();
    let complement = Price::zero();

    let start_balance = u128::MAX;
    let incoming_balance = u128::MAX;
    let next_balance = balance_ema(start_balance, complement, incoming_balance, alpha);
    assert_eq!(next_balance, Some(incoming_balance));
}
