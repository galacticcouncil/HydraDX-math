use crate::ema::*;
use crate::types::{Balance, Price};

use proptest::prelude::*;
use sp_arithmetic::{
    traits::{One, Zero},
    FixedPointNumber, FixedU128,
};

use num_traits::Bounded;

fn inner_between_one_and_div() -> impl Strategy<Value = u128> {
    1..FixedU128::DIV
}

fn inner_for_non_zero_fixed() -> impl Strategy<Value = u128> {
    1..u128::MAX
}

fn non_zero_balance() -> impl Strategy<Value = Balance> {
    any::<Balance>().prop_filter("balance should be greater than 0", |b| b > &0)
}

// Tests
proptest! {
    #[test]
    fn one_price_iteration_ema_is_same_as_simple_version(
        smoothing in inner_between_one_and_div(),
        (prev_price, incoming_price) in (inner_for_non_zero_fixed(), inner_for_non_zero_fixed())
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        let prev_price = Price::from_inner(prev_price);
        let incoming_price = Price::from_inner(incoming_price);
        // actual test
        let iter_price = iterated_price_ema(1, prev_price, incoming_price, smoothing);
        prop_assert!(smoothing <= FixedU128::one());
        let complement = FixedU128::one() - smoothing;
        let simple_price = price_ema(prev_price, complement, incoming_price, smoothing);
        prop_assert!(iter_price.is_some());
        prop_assert!(simple_price.is_some());
        prop_assert_eq!(iter_price.unwrap(), simple_price.unwrap());
    }
}

proptest! {
    #[test]
    fn one_balance_iteration_ema_is_same_as_simple_version(
        smoothing in inner_between_one_and_div(),
        (prev_balance, incoming_balance) in (non_zero_balance(), non_zero_balance())
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        // actual test
        let iter_balance = iterated_balance_ema(1, prev_balance, incoming_balance, smoothing);
        prop_assert!(smoothing <= FixedU128::one());
        let complement = FixedU128::one() - smoothing;
        let simple_balance = balance_ema(prev_balance, complement, incoming_balance, smoothing);
        prop_assert!(iter_balance.is_some());
        prop_assert!(simple_balance.is_some());
        prop_assert_eq!(iter_balance.unwrap(), simple_balance.unwrap());
    }
}
