use crate::ema::*;
use crate::types::{Balance, Price};
use high_precision::fixed_to_rational;

use proptest::prelude::*;
use rug::Rational;
use sp_arithmetic::{
    traits::{One, Zero},
    FixedPointNumber, FixedU128,
};

const MAX_ITERATIONS: u32 = 10_000; // slow but more informative: 5_256_000 (= 1 year)

macro_rules! prop_assert_rational_approx_eq {
    ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x - $y } else { $y - $x };
        prop_assert!(
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

macro_rules! prop_assert_approx_eq {
    ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x - $y } else { $y - $x };
        prop_assert!(
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

// --- Strategies

/// Strategy for generating a random fixed point number between near 0 and 1.
fn fixed_above_zero_and_less_or_equal_one() -> impl Strategy<Value = FixedU128> {
    (1..FixedU128::DIV).prop_map(|x| FixedU128::from_inner(x))
}

/// Strategy for generating a random fixed point number working around the lack of built-in strategy.
fn any_fixed() -> impl Strategy<Value = FixedU128> {
    any::<u128>().prop_map(|x| FixedU128::from_inner(x))
}

fn typical_smoothing_factor() -> impl Strategy<Value = (FixedU128, u32)> {
    (0usize..2).prop_map(|i| {
        [
            (smoothing_from_period(100), 100),
            (smoothing_from_period(14_400), 14_400),
            (smoothing_from_period(100_800), 100_800),
        ][i]
    })
}

// --- Tests
proptest! {
    #[test]
    fn price_ema_stays_stable_if_the_value_does_not_change(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
        price in any_fixed()
    ) {
        let next_price = price_weighted_average(price, price, smoothing);
        prop_assert_eq!(next_price, price);
    }
}

proptest! {
    #[test]
    fn balance_ema_stays_stable_if_the_value_does_not_change(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
        balance in any::<Balance>()
    ) {
        let next_balance = balance_weighted_average(balance, balance, smoothing);
        prop_assert_eq!(next_balance, balance);
    }
}

proptest! {
    #[test]
    fn one_price_iteration_ema_is_same_as_simple_version(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
        (prev_price, incoming_price) in (any_fixed(), any_fixed())
    ) {
        let iter_price = iterated_price_ema(1, prev_price, incoming_price, smoothing);
        let simple_price = price_weighted_average(prev_price, incoming_price, smoothing);
        prop_assert_eq!(iter_price, simple_price);
    }
}

proptest! {
    #[test]
    fn one_balance_iteration_ema_is_same_as_simple_version(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
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
        smoothing in fixed_above_zero_and_less_or_equal_one(),
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
        (smoothing, period) in typical_smoothing_factor(),
        (start_balance, incoming_balance) in
                (1e12 as Balance..(1e24 as Balance))
                    .prop_perturb(|n, mut rng| (n, rng.gen_range(n..(1e26 as Balance))))
    ) {
        let next_balance = balance_weighted_average(start_balance, incoming_balance, smoothing);
        let expected: Rational =
            start_balance + Rational::from(incoming_balance - start_balance) * 2 / (period + 1);
        let tolerance = 90_000_000;
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
    fn balance_weighted_averages_work_on_typical_values_via_manual_weighting(
        period in 1u32..5_000_000,
        (start_balance, incoming_balance) in
                (1e10 as Balance..(1e24 as Balance))
                    .prop_perturb(|n, mut rng| (n, rng.gen_range(n..(1e28 as Balance))))
    ) {
        use sp_arithmetic::helpers_128bit::multiply_by_rational_with_rounding;
        use sp_arithmetic::per_things::Rounding;
        let next_balance = start_balance + multiply_by_rational_with_rounding(incoming_balance - start_balance, 2, (period + 1).into(), Rounding::NearestPrefDown).expect("no overflow");
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
        prop_assert!(smoothing > FixedU128::zero());
        prop_assert!(smoothing <= FixedU128::one());
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_small_balance_values(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
        (prev_balance, incoming_balance) in (0..Balance::from(u64::MAX), 0..Balance::from(u64::MAX))
    ) {
        let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
        let rug_balance = high_precision::rug_balance_weighted_average(
            prev_balance, incoming_balance, fixed_to_rational(smoothing));
        prop_assert_eq!(balance, rug_balance);
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_small_balance_values_in_extreme_smoothing_value_cases(
        (prev_balance, incoming_balance) in (0..Balance::from(u64::MAX), 0..Balance::from(u64::MAX))
    ) {
        {
            let smoothing = FixedU128::from_inner(1);
            let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
            let rug_balance = high_precision::rug_balance_weighted_average(
                prev_balance, incoming_balance,  fixed_to_rational(smoothing));
            prop_assert_eq!(balance, rug_balance);
        }
        {
            let smoothing = FixedU128::from_inner(FixedU128::DIV - 1);
            let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
            let rug_balance = high_precision::rug_balance_weighted_average(
                prev_balance, incoming_balance,  fixed_to_rational(smoothing));
            prop_assert_eq!(balance, rug_balance);
        }
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_prices(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
        (prev_price, incoming_price) in (any_fixed(), any_fixed())
    ) {
        let price = price_weighted_average(prev_price, incoming_price, smoothing);
        let rug_price = high_precision::rug_price_weighted_average(prev_price, incoming_price, fixed_to_rational(smoothing));
        let epsilon = Rational::from((1, Price::DIV));
        let price = fixed_to_rational(price);
        prop_assert!(price <= rug_price.clone() + epsilon.clone());
        prop_assert!(price >= rug_price - epsilon);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn exponential_smoothing_precision_minutes(
        iterations in 1_u32..MAX_ITERATIONS,
    ) {
        let smoothing = smoothing_from_period(100); // 10 min
        let exp = exp_smoothing(smoothing, iterations);
        let rug_exp = high_precision::rug_exp_smoothing(smoothing, iterations);

        let tolerance = Rational::from((1_000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fixed_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn exponential_smoothing_precision_day(
        iterations in 1u32..MAX_ITERATIONS,
    ) {
        let smoothing = smoothing_from_period(14_400); // 1 day
        let exp = exp_smoothing(smoothing, iterations);
        let rug_exp = high_precision::rug_exp_smoothing(smoothing, iterations);

        let tolerance = Rational::from((1_000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fixed_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn exponential_smoothing_precision_week(
        iterations in 1_u32..MAX_ITERATIONS,
    ) {
        let smoothing = smoothing_from_period(100_800); // 1 week
        let exp = exp_smoothing(smoothing, iterations);
        let rug_exp = high_precision::rug_exp_smoothing(smoothing, iterations);

        let tolerance = Rational::from((20_000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fixed_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn exponential_smoothing_precision_arbitrary_smoothing(
        period in 1u64..200_000,
        iterations in 1_u32..MAX_ITERATIONS,
    ) {
        let smoothing = smoothing_from_period(period);
        let exp = exp_smoothing(smoothing, iterations);
        let rug_exp = high_precision::rug_exp_smoothing(smoothing, iterations);

        let tolerance = Rational::from((20_000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fixed_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

fn ema_balance_history() -> impl Strategy<Value = Vec<(Balance, u32)>> {
    prop::collection::vec(((1e12 as Balance)..(1e28 as Balance), 1_u32..10), 1..100)
}

fn to_regular_history<T: Copy>(history: Vec<(T, u32)>) -> Vec<T> {
    let expanded: Vec<Vec<_>> = history
        .into_iter()
        .map(|(v, iterations)| vec![v; iterations as usize])
        .collect();
    expanded.concat()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn ema_balance_history_precision(
        history in ema_balance_history(),
        period in 1u64..200_000,
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_balance_ema(to_regular_history(history.clone()), smoothing);

        let mut ema = history[0].0;
        // for (balance, iterations) in history.into_iter().skip(1) {
        //     ema = iterated_balance_ema(iterations, ema, balance, smoothing);
        // }
        for balance in to_regular_history(history).into_iter().skip(1) {
            ema = balance_weighted_average(ema, balance, smoothing);
        }

        let tolerance = 1000;
        prop_assert_approx_eq!(
            rug_ema.clone(),
            ema,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}
