use crate::ema::*;
use crate::types::{Balance, Price};

use proptest::prelude::*;
use sp_arithmetic::{
    traits::One,
    FixedPointNumber, FixedU128,
};

fn inner_between_one_and_div() -> impl Strategy<Value = u128> {
    1..FixedU128::DIV
}

fn non_zero_balance() -> impl Strategy<Value = Balance> {
    any::<Balance>().prop_filter("balance should be greater than 0", |b| b > &0)
}

// Tests
proptest! {
    #[test]
    fn one_price_iteration_ema_is_same_as_simple_version(
        smoothing in inner_between_one_and_div(),
        (prev_price, incoming_price) in (any::<u128>(), any::<u128>())
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        let prev_price = Price::from_inner(prev_price);
        let incoming_price = Price::from_inner(incoming_price);
        // actual test
        let iter_price = iterated_price_ema(1, prev_price, incoming_price, smoothing);
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
        let complement = FixedU128::one() - smoothing;
        let simple_balance = balance_ema(prev_balance, complement, incoming_balance, smoothing);
        prop_assert!(iter_balance.is_some());
        prop_assert!(simple_balance.is_some());
        prop_assert_eq!(iter_balance.unwrap(), simple_balance.unwrap());
    }
}

proptest! {
    #[test]
    fn new_oracle_is_less_or_equal_to_new_value(
        smoothing in inner_between_one_and_div(),
        iterations in any::<u32>(),
        (prev_balance, incoming_balance) in 
            (0..(Balance::MAX - 1)).prop_perturb(|n, mut rng| (n, rng.gen_range(n..Balance::MAX)))
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        // actual test
        let balance = iterated_balance_ema(iterations, prev_balance, incoming_balance, smoothing);
        prop_assert!(balance.is_some());
        prop_assert!(balance.unwrap() <= incoming_balance);
    }
}

