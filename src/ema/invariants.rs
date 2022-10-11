use crate::ema::*;
use crate::types::{Balance, Price};
use high_precision::fixed_to_rational;

use proptest::prelude::*;
use rug::{Integer, Rational};
use sp_arithmetic::{
    traits::{One, Zero},
    FixedPointNumber, FixedU128,
};

// Strategy for generating a random fixed point number between near 0 and 1.
fn inner_between_one_and_div() -> impl Strategy<Value = u128> {
    1..FixedU128::DIV
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
        let simple_price = price_ema(prev_price, incoming_price, smoothing);
        prop_assert_eq!(iter_price, simple_price);
    }
}

proptest! {
    #[test]
    fn one_balance_iteration_ema_is_same_as_simple_version(
        smoothing in inner_between_one_and_div(),
        (prev_balance, incoming_balance) in (any::<Balance>(), any::<Balance>())
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        // actual test
        let iter_balance = iterated_balance_ema(1, prev_balance, incoming_balance, smoothing);
        let simple_balance = balance_ema(prev_balance, incoming_balance, smoothing);
        prop_assert_eq!(iter_balance, simple_balance);
    }
}

proptest! {
    #[test]
    fn new_oracle_is_between_old_and_new_value(
        smoothing in inner_between_one_and_div(),
        iterations in any::<u32>(),
        (prev_balance, incoming_balance) in
            (0..(Balance::MAX - 1)).prop_perturb(|n, mut rng| (n, rng.gen_range(n..Balance::MAX)))
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        // actual test
        let balance = iterated_balance_ema(iterations, prev_balance, incoming_balance, smoothing);
        prop_assert!(balance <= incoming_balance);
        prop_assert!(prev_balance <= balance);
    }
}

proptest! {
    #[test]
    fn smoothing_is_greater_zero_and_less_equal_one(
        period in 0_u64..2_000_000_000_000_000_000,
    ) {
        let smoothing = smoothing_from_period(period);
        prop_assert!(smoothing > FixedU128::zero());
        prop_assert!(smoothing <= FixedU128::one());
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_small_balance_values(
        smoothing in inner_between_one_and_div(),
        (prev_balance, incoming_balance) in (0..Balance::from(u64::MAX), 0..Balance::from(u64::MAX))
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        // actual test
        let balance = balance_ema(prev_balance, incoming_balance, smoothing);
        let rug_balance = high_precision::rug_balance_ma(
            prev_balance, incoming_balance,  fixed_to_rational(smoothing));
        prop_assert_eq!(Integer::from(balance), rug_balance);
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_small_balance_values_in_extreme_smoothing_value_cases(
        (prev_balance, incoming_balance) in (0..Balance::from(u64::MAX), 0..Balance::from(u64::MAX))
    ) {
        {
            // work around lack of `Strategy` impl for `FixedU128`
            let smoothing = FixedU128::from_inner(1);
            // actual test
            let balance = balance_ema(prev_balance, incoming_balance, smoothing);
            let rug_balance = high_precision::rug_balance_ma(
                prev_balance, incoming_balance,  fixed_to_rational(smoothing));
            prop_assert_eq!(Integer::from(balance), rug_balance);
        }

        {
            // work around lack of `Strategy` impl for `FixedU128`
            let smoothing = FixedU128::from_inner(FixedU128::DIV - 1);
            // actual test
            let balance = balance_ema(prev_balance, incoming_balance, smoothing);
            let rug_balance = high_precision::rug_balance_ma(
                prev_balance, incoming_balance,  fixed_to_rational(smoothing));
            prop_assert_eq!(Integer::from(balance), rug_balance);
        }
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_prices(
        smoothing in inner_between_one_and_div(),
        (prev_price, incoming_price) in (0..u128::MAX, 0..u128::MAX)
    ) {
        // work around lack of `Strategy` impl for `FixedU128`
        let smoothing = FixedU128::from_inner(smoothing);
        let prev_price = Price::from_inner(prev_price);
        let incoming_price = Price::from_inner(incoming_price);
        // actual test
        let price = price_ema(prev_price, incoming_price, smoothing);
        let rug_price = high_precision::rug_price_ma(prev_price, incoming_price, fixed_to_rational(smoothing));
        let epsilon = Rational::from((1, Price::DIV));
        let price = fixed_to_rational(price);
        prop_assert!(price <= rug_price.clone() + epsilon.clone());
        prop_assert!(price >= rug_price - epsilon);
    }
}
