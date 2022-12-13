use crate::ema::*;
use crate::fraction;
use crate::test_utils::{
    any_rational, fraction_to_arbitrary_precision, rational_to_arbitrary_precision,
    prop_assert_rational_relative_approx_eq, prop_assert_approx_eq, prop_assert_rational_approx_eq,
};
use crate::test_utils::{MAX_BALANCE, MIN_BALANCE};
use crate::types::{Balance, Fraction};

use proptest::prelude::*;

use rug::Rational;
use sp_arithmetic::{
    traits::{One, Zero},
    Rational128
};

/// 2 weeks at 6s block time
pub const MAX_ITERATIONS: u32 = 201_600;

//
// --- Strategies
//

/// Strategy for generating a random fixed point number between near 0 and 1.
fn fraction_above_zero_and_less_or_equal_one() -> impl Strategy<Value = Fraction> {
    (1..fraction::DIV).prop_map(|x| Fraction::from_bits(x))
}

fn typical_period() -> impl Strategy<Value = u64> {
    1_u64..110_000
}

fn long_period() -> impl Strategy<Value = u64> {
    10_000_u64..110_000
}

fn realistic_balance() -> impl Strategy<Value = Balance> {
    MIN_BALANCE..MAX_BALANCE
}

fn iterations_up_to(max: u32) -> impl Strategy<Value = u32> {
    1_u32..max
}

fn iterations() -> impl Strategy<Value = u32> {
    1_u32..MAX_ITERATIONS
}

fn typical_price_rational() -> impl Strategy<Value = Rational128> {
    ((MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE)).prop_map(|(n, d)| Rational128::from(n, d))
}

fn period_fraction() -> impl Strategy<Value = Fraction> {
    (typical_period()).prop_map(|period| smoothing_from_period(period))
}

prop_compose! {
    fn period_and_iterations()(p in long_period())(
        period in Just(p),
        iterations in iterations_up_to(p as u32 * 2),
    ) -> (u64, u32) {
      (period, iterations)
    }
}

fn ema_price_history() -> impl Strategy<Value = Vec<(Rational128, u32)>> {
    prop::collection::vec((any_rational(), iterations()), 2..50)
}

prop_compose! {
    fn ema_balance_crash_history()(p in long_period())(
        period in Just(p),
        initial_balance in realistic_balance(),
        big_balance in (1e16 as Balance)..MAX_BALANCE, big_iter in iterations_up_to(p as u32 * 2),
        small_balance in MIN_BALANCE..100_000, small_iter in iterations_up_to(p as u32 * 2)
    ) -> (u64, Vec<(Balance, u32)>) {
      (period, vec![
        (initial_balance, 1),
        (big_balance, big_iter),
        (small_balance, small_iter)
      ])
    }
}

fn ema_balance_history() -> impl Strategy<Value = Vec<(Balance, u32)>> {
    prop::collection::vec(((1e6 as Balance)..(1e28 as Balance), 1_u32..MAX_ITERATIONS), 2..50)
}

//
// --- Tests
//
proptest! {
    #[test]
    fn price_ema_stays_stable_if_the_value_does_not_change(
        smoothing in period_fraction(),
        price in typical_price_rational(),
    ) {
        let next_price = price_weighted_average(price, price, smoothing);
        prop_assert_eq!(next_price, price);
    }
}

proptest! {
    #[test]
    fn balance_ema_stays_stable_if_the_value_does_not_change(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        balance in any::<Balance>()
    ) {
        let next_balance = balance_weighted_average(balance, balance, smoothing);
        prop_assert_eq!(next_balance, balance);
    }
}

proptest! {
    #[test]
    fn one_price_iteration_ema_is_same_as_simple_version(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        (prev_price, incoming_price) in (any_rational(), any_rational())
    ) {
        let iter_price = iterated_price_ema(1, prev_price, incoming_price, smoothing);
        let simple_price = price_weighted_average(prev_price, incoming_price, smoothing);
        prop_assert_eq!(iter_price, simple_price);
    }
}

proptest! {
    #[test]
    fn one_balance_iteration_ema_is_same_as_simple_version(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        (prev_balance, incoming_balance) in (any::<Balance>(), any::<Balance>())
    ) {
        let iter_balance = iterated_balance_ema(1, prev_balance, incoming_balance, smoothing);
        let simple_balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
        prop_assert_eq!(iter_balance, simple_balance);
    }
}

proptest! {
    #[test]
    fn new_oracle_is_between_old_and_new_value(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        iterations in any::<u32>(),
        (prev_balance, incoming_balance) in
            (0..(Balance::MAX - 1)).prop_perturb(|n, mut rng| (n, rng.gen_range(n..Balance::MAX)))
    ) {
        let balance = iterated_balance_ema(iterations, prev_balance, incoming_balance, smoothing);
        prop_assert!(balance <= incoming_balance);
        prop_assert!(prev_balance <= balance);
    }
}

proptest! {
    #[test]
    fn balance_weighted_averages_work_on_typical_values_with_typical_smoothing(
        period in typical_period(),
        (start_balance, incoming_balance) in
                (1e6 as Balance..(1e26 as Balance))
                    .prop_perturb(|n, mut rng| (n, rng.gen_range(n..(1e26 as Balance))))
    ) {
        let smoothing = smoothing_from_period(period);
        let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
        let expected: Rational =
            start_balance + Rational::from(incoming_balance - start_balance) * 2 / (period + 1);
        let tolerance = 1;
        let expected_balance = expected.round();
        prop_assert_approx_eq!(
            next_balance,
            expected_balance.clone(),
            tolerance,
            "averaged balance values should be within tolerance of the expected value"
        );
    }
}

proptest! {
    #[test]
    fn smoothing_is_greater_zero_and_less_equal_one(
        // We run into precision issues eventually, but any sane period value will be <10M
        period in 0_u64..2_000_000_000_000_000_000,
    ) {
        let smoothing = smoothing_from_period(period);
        prop_assert!(smoothing > Fraction::zero());
        prop_assert!(smoothing <= Fraction::one());
    }
}

proptest! {
    #[test]
    fn smoothing_precision(
        // We run into precision issues eventually, but any sane period value will be <10M
        period in 0_u64..2_000_000_000_000_000_000,
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_smoothing = high_precision::smoothing_from_period(period);
        let epsilon = Rational::from((1, 1e18 as u128));
        let smoothing = fraction_to_arbitrary_precision(smoothing);
        prop_assert_rational_approx_eq!(smoothing, rug_smoothing, epsilon);
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_balances(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        (prev_balance, incoming_balance) in (any::<Balance>(), any::<Balance>())
    ) {
        let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
        let rug_balance = high_precision::precise_balance_weighted_average(
            prev_balance, incoming_balance, fraction_to_arbitrary_precision(smoothing));
        prop_assert_eq!(balance, rug_balance);
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_small_balance_values_with_small_smoothing_value(
        (prev_balance, incoming_balance) in (0..Balance::from(u64::MAX), 0..Balance::from(u64::MAX))
    ) {
        let smoothing = fraction::SMALLEST_NON_ZERO;
        let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
        let rug_balance = high_precision::precise_balance_weighted_average(
            prev_balance, incoming_balance,  fraction_to_arbitrary_precision(smoothing));
        prop_assert_eq!(balance, rug_balance);
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_small_balance_values_with_big_smoothing_value(
        (prev_balance, incoming_balance) in (0..Balance::from(u64::MAX), 0..Balance::from(u64::MAX))
    ) {
        let smoothing = Fraction::from_bits(fraction::DIV - 1);
        let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
        let rug_balance = high_precision::precise_balance_weighted_average(
            prev_balance, incoming_balance, fraction_to_arbitrary_precision(smoothing));
        prop_assert_eq!(balance, rug_balance);
    }
}

proptest! {
    #[test]
    fn low_precision_loss_for_prices(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        (prev_price, incoming_price) in (typical_price_rational(), typical_price_rational())
    ) {
        let price = price_weighted_average(prev_price, incoming_price, smoothing);
        let rug_price = high_precision::precise_weighted_average(rational_to_arbitrary_precision(prev_price), rational_to_arbitrary_precision(incoming_price), fraction_to_arbitrary_precision(smoothing));
        let tolerance = Rational::from((1, 1e30 as u128));
        let price = rational_to_arbitrary_precision(price);
        prop_assert_rational_relative_approx_eq!(price, rug_price, tolerance);
    }
}

proptest! {
    #[test]
    fn exponential_smoothing_precision_should_be_high_enough(
        period in typical_period(),
        iterations in 1_u32..MAX_ITERATIONS,
    ) {
        let smoothing = smoothing_from_period(period);
        let result = exp_smoothing(smoothing, iterations);
        let expected = high_precision::precise_exp_smoothing(fraction_to_arbitrary_precision(smoothing), iterations);

        let tolerance = Rational::from((1, 1e18 as u128));
        prop_assert_rational_approx_eq!(
            fraction_to_arbitrary_precision(result),
            expected,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[test]
    fn iterated_balance_precision(
        period in typical_period(),
        iterations in 1_u32..MAX_ITERATIONS,
        (start_balance, incoming_balance) in
                (1e6 as Balance..(1e26 as Balance))
                    .prop_perturb(|n, mut rng| (n, rng.gen_range(n..(1e26 as Balance))))
    ) {
        let smoothing = smoothing_from_period(period);

        let expected = high_precision::precise_balance_weighted_average(start_balance, incoming_balance, high_precision::precise_exp_smoothing(fraction_to_arbitrary_precision(smoothing), iterations));
        let new_oracle = iterated_balance_ema(iterations, start_balance, incoming_balance, smoothing);

        let tolerance = 1;
        prop_assert_approx_eq!(
            new_oracle,
            expected.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2_000))]
    #[test]
    fn iterated_price_precision(
        (period, iterations) in period_and_iterations(),
        (a, b) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
        (c, d) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
    ) {
        let smoothing = smoothing_from_period(period);
        let prev = Rational128::from(a, b);
        let incoming = Rational128::from(c, d);

        let res = iterated_price_ema(iterations, prev, incoming, smoothing);
        let smoothing_adj = high_precision::precise_exp_smoothing(fraction_to_arbitrary_precision(smoothing), iterations);
        let expected = high_precision::precise_weighted_average(rational_to_arbitrary_precision(prev), rational_to_arbitrary_precision(incoming), smoothing_adj);

        let res = rational_to_arbitrary_precision(res);
        let tolerance = Rational::from((1, 1e30 as u128));

        prop_assert_rational_relative_approx_eq!(
            res,
            expected,
            tolerance
        );
    }
}

proptest! {
    #[test]
    fn ema_balance_history_precision(
        history in ema_balance_history(),
        period in typical_period(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::precise_balance_ema(history.clone(), fraction_to_arbitrary_precision(smoothing));

        let mut ema = history[0].0;
        for (balance, iterations) in history.into_iter().skip(1) {
            ema = iterated_balance_ema(iterations, ema, balance, smoothing);
        }

        let tolerance = 1;
        prop_assert_approx_eq!(
            ema,
            rug_ema,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[test]
    fn ema_balance_history_precision_crash_scenario(
        (period, history) in ema_balance_crash_history(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::precise_balance_ema(history.clone(), fraction_to_arbitrary_precision(smoothing));

        let mut ema = history[0].0;
        for (balance, iterations) in history.into_iter().skip(1) {
            ema = iterated_balance_ema(iterations, ema, balance, smoothing);
        }

        let tolerance = 1;
        prop_assert_approx_eq!(
            ema,
            rug_ema,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[ignore]
    #[test]
    fn ema_price_history_precision(
        history in ema_price_history(),
        period in typical_period(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::precise_price_ema(history.clone(), fraction_to_arbitrary_precision(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, 1e24 as u128));
        prop_assert_rational_relative_approx_eq!(
            rational_to_arbitrary_precision(ema),
            rug_ema,
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}
