use crate::ema::*;
use crate::types::fraction;
use crate::types::{Balance, Fraction, Price};
use high_precision::{fixed_to_rational, fraction_to_rational, rational_to_rational};

use proptest::prelude::*;

use num_traits::Pow;
use rug::Rational;
use sp_arithmetic::{
    traits::{One, Zero},
    FixedPointNumber, FixedU128,
};

// 2 weeks
pub const MAX_ITERATIONS: u32 = 201_600;
// existential deposit for BTC will likely be 100 satoshis
pub const MIN_BALANCE: Balance = 50;
// total issuance of BSX is about 1e22, total issuance of FRAX is about 1e27
pub const MAX_BALANCE: Balance = 1e22 as Balance;

macro_rules! prop_assert_rational_approx_eq {
    ($x:expr, $y:expr, $z:expr, $r:expr) => {{
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

macro_rules! prop_assert_rational_relative_approx_eq {
    ($x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x.clone() - $y.clone() } else { $y.clone() - $x.clone() };
        prop_assert!(
            diff.clone() / $x.clone() <= $z.clone(),
            "\n{}\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            $r,
            $x.clone().to_f64(),
            $y.to_f64(),
            diff.to_f64(),
            ($x * $z).to_f64()
        );
    }};
}

macro_rules! assert_rational_relative_approx_eq {
    ($x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x.clone() - $y.clone() } else { $y.clone() - $x.clone() };
        assert!(
            diff.clone() / $x.clone() <= $z.clone(),
            "\n{}\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            $r,
            $x.clone().to_f64(),
            $y.to_f64(),
            diff.to_f64(),
            ($x * $z).to_f64()
        );
    }};
}

macro_rules! prop_assert_approx_eq {
    ($x:expr, $y:expr, $z:expr, $r:expr) => {{
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
fn fraction_above_zero_and_less_or_equal_one() -> impl Strategy<Value = Fraction> {
    (1..fraction::DIV).prop_map(|x| Fraction::from_bits(x))
}

/// Strategy for generating a random fixed point number working around the lack of built-in strategy.
fn any_fixed() -> impl Strategy<Value = FixedU128> {
    any::<u128>().prop_map(|x| FixedU128::from_inner(x))
}

fn big_fixed() -> impl Strategy<Value = FixedU128> {
    ((1e10 as u64)..(1e15 as u64)).prop_map(|x| FixedU128::saturating_from_integer(x))
}

fn small_fixed() -> impl Strategy<Value = FixedU128> {
    ((1e10 as u64)..(1e15 as u64)).prop_map(|x| FixedU128::saturating_from_rational(1, x))
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
    1_u32..(max * 2)
}

fn iterations() -> impl Strategy<Value = u32> {
    1_u32..MAX_ITERATIONS
}

fn small_rational_close_to_one() -> impl Strategy<Value = Rational> {
    (1u64..1_000, 5_000u64..200_000).prop_map(|(a, b)| Rational::one() - Rational::from((a, b)))
}

fn period_fraction() -> impl Strategy<Value = Fraction> {
    (typical_period()).prop_map(|period| smoothing_from_period(period))
}

// --- History Strategies
fn ema_price_history() -> impl Strategy<Value = Vec<(Price, u32)>> {
    prop::collection::vec((any_fixed(), iterations()), 2..50)
}

prop_compose! {
    fn ema_small_price_history()(p in long_period())(
        period in Just(p),
        history in prop::collection::vec((small_fixed(), iterations_up_to(p as u32)), 2..100)
    ) -> (u64, Vec<(Price, u32)>) {
      (period, history)
    }
}

fn typical_price_rational() -> impl Strategy<Value = Rational128> {
    ((MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE)).prop_map(|(n, d)| Rational128::from(n, d))
}

fn small_rational() -> impl Strategy<Value = Rational128> {
    ((1e10 as u128)..(1e15 as u128)).prop_map(|x| Rational128::from(1, x))
}

prop_compose! {
    fn ema_small_rational_price_history()(p in long_period())(
        period in Just(p),
        history in prop::collection::vec((small_rational(), iterations_up_to(p as u32)), 2..100)
    ) -> (u64, Vec<(Rational128, u32)>) {
      (period, history)
    }
}

prop_compose! {
    fn ema_rational_price_history()(p in long_period())(
        period in Just(p),
        history in prop::collection::vec((typical_price_rational(), iterations_up_to(p as u32 / 4)), 2..5)
    ) -> (u64, Vec<(Rational128, u32)>) {
      (period, history)
    }
}

prop_compose! {
    fn ema_price_crash_history()(p in long_period())(
        period in Just(p),
        initial_price in any_fixed(),
        big_price in big_fixed(), big_iter in iterations_up_to(p as u32),
        small_price in small_fixed(), small_iter in iterations_up_to(p as u32)
    ) -> (u64, Vec<(Price, u32)>) {
      (period, vec![
        (initial_price, 1),
        (big_price, big_iter),
        (small_price, small_iter)
      ])
    }
}

prop_compose! {
    fn ema_balance_crash_history()(p in long_period())(
        period in Just(p),
        initial_balance in realistic_balance(),
        big_balance in (1e16 as Balance)..MAX_BALANCE, big_iter in iterations_up_to(p as u32),
        small_balance in MIN_BALANCE..100_000, small_iter in iterations_up_to(p as u32)
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

// --- Tests
proptest! {
    #[test]
    fn price_ema_stays_stable_if_the_value_does_not_change(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        price in any_fixed()
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
        let epsilon = Rational::from((1, FixedU128::DIV));
        let smoothing = fraction_to_rational(smoothing);
        prop_assert!(smoothing <= rug_smoothing.clone() + epsilon.clone());
        prop_assert!(smoothing >= rug_smoothing - epsilon);
    }
}

proptest! {
    #[test]
    fn no_precision_loss_for_balances(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        (prev_balance, incoming_balance) in (any::<Balance>(), any::<Balance>())
    ) {
        let balance = balance_weighted_average(prev_balance, incoming_balance, smoothing);
        let rug_balance = high_precision::rug_balance_weighted_average(
            prev_balance, incoming_balance, fraction_to_rational(smoothing));
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
        let rug_balance = high_precision::rug_balance_weighted_average(
            prev_balance, incoming_balance,  fraction_to_rational(smoothing));
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
        let rug_balance = high_precision::rug_balance_weighted_average(
            prev_balance, incoming_balance, fraction_to_rational(smoothing));
        prop_assert_eq!(balance, rug_balance);
    }
}

proptest! {
    #[test]
    fn low_precision_loss_for_prices(
        smoothing in fraction_above_zero_and_less_or_equal_one(),
        (prev_price, incoming_price) in (any_fixed(), any_fixed())
    ) {
        let price = price_weighted_average(prev_price, incoming_price, smoothing);
        let rug_price = high_precision::rug_price_weighted_average(prev_price, incoming_price, fraction_to_rational(smoothing));
        let epsilon = Rational::from((1, Price::DIV));
        let price = fixed_to_rational(price);
        prop_assert!(price <= rug_price.clone() + epsilon.clone());
        prop_assert!(price >= rug_price - epsilon);
    }
}

proptest! {
    #[test]
    fn exponential_smoothing_precision_should_be_higher_than_smallest_fixed_u128_value(
        period in typical_period(),
        iterations in 1_u32..MAX_ITERATIONS,
    ) {
        let smoothing = smoothing_from_period(period);
        let exp = exp_smoothing(smoothing, iterations);
        let rug_exp = high_precision::rug_exp_smoothing(fraction_to_rational(smoothing), iterations);

        let tolerance = Rational::from((1, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fraction_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[test]
    fn fraction_times_fixed_precision(
        smoothing in period_fraction(),
        fixed in any_fixed(),
    ) {
        let rational = fixed_to_rational(fixed) * fraction_to_rational(smoothing);
        let conversion = fixed * fraction::to_fixed(smoothing);
        let conversion_distance = (rational.clone() - fixed_to_rational(conversion)).abs();
        let multiply = fraction::multiply_by_fixed(smoothing, fixed);
        let multiply_distance = (rational.clone() - fixed_to_rational(multiply)).abs();
        prop_assert!(multiply_distance <= conversion_distance);
    }
}

proptest! {
    // #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn iterated_ema_precision(
        period in typical_period(),
        iterations in 1_u32..MAX_ITERATIONS,
        (start_balance, incoming_balance) in
                (1e6 as Balance..(1e26 as Balance))
                    .prop_perturb(|n, mut rng| (n, rng.gen_range(n..(1e26 as Balance))))
    ) {
        let smoothing = smoothing_from_period(period);

        let expected = high_precision::rug_balance_weighted_average(start_balance, incoming_balance, high_precision::rug_exp_smoothing(fraction_to_rational(smoothing), iterations));
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
    #[test]
    fn ema_balance_history_precision(
        history in ema_balance_history(),
        period in typical_period(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_balance_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (balance, iterations) in history.into_iter().skip(1) {
            ema = iterated_balance_ema(iterations, ema, balance, smoothing);
        }

        let tolerance = 1;
        prop_assert_approx_eq!(
            rug_ema.clone(),
            ema,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[test]
    fn ema_price_history_precision(
        history in ema_price_history(),
        period in typical_period(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, 1e24 as u128));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            fixed_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[test]
    fn ema_price_history_precision_crash_scenario(
        (period, history) in ema_price_crash_history(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, 1e15 as u128));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            fixed_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #[test]
    fn ema_small_price_history_precision(
        (period, history) in ema_small_price_history(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, 1e9 as u128));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            fixed_to_rational(ema),
            relative_tolerance,
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
        let rug_ema = high_precision::rug_fast_balance_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (balance, iterations) in history.into_iter().skip(1) {
            ema = iterated_balance_ema(iterations, ema, balance, smoothing);
        }

        let tolerance = 1;
        prop_assert_approx_eq!(
            rug_ema.clone(),
            ema,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    #[test]
    fn stepwise_pow_close_enough(
        num in small_rational_close_to_one(),
        exponent in 1u32..200_000,
    ) {
            let res_pow = num.clone().pow(exponent);
            let res_step = high_precision::stepwise_pow_approx(num.clone(), exponent);
            dbg!(res_pow.clone().to_f64());
            dbg!(res_step.clone().to_f64());
            dbg!((res_pow.clone() - res_step.clone()).abs().to_f64());
            dbg!(Rational::from((1, u128::MAX)).to_f64());
            prop_assert!((res_pow - res_step).abs() < Rational::from((1, u128::MAX)));
    }
}

use sp_arithmetic::Rational128;
use super::rational;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]
    #[test]
    fn fraction_times_rational(
        smoothing in typical_period().prop_map(smoothing_from_period),
        price in (MIN_BALANCE..u128::MAX, MIN_BALANCE..u128::MAX),
    ) {
        let price = Rational128::from(price.0, price.1);

        let res = rational::multiply_by_rational(smoothing, price);
        let expected = fraction_to_rational(smoothing) * Rational::from((price.n(), price.d()));

        let res = Rational::from((res.n(), res.d()));
        let tolerance = Rational::from((1, 1u128 << 85));

        let diff = if res >= expected { res.clone() - expected.clone() } else { expected.clone() - res.clone() };
        let small_enough = diff.clone() / expected.clone() <= tolerance;
        let max_diff = expected.clone() * tolerance.clone();
        prop_assert!(
            small_enough,
            "\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            res.clone().to_f64(),
            expected.clone().to_f64(),
            diff.to_f64(),
            max_diff.to_f64()
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_000_000))]
    #[test]
    fn rational_rounding_add(
        (a, b) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
        (c, d) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
    ) {
        let price1 = Rational128::from(a, b);
        let price2 = Rational128::from(c, d);

        let res = rational::rounding_add(price1, price2); //(a.into(), b.into()), (c.into(), d.into()));
        let expected = Rational::from((a, b)) + Rational::from((c, d));

        let res = rational_to_rational(res);
        let tolerance = Rational::from((1, 1u128 << 100));

        let diff = if res >= expected { res.clone() - expected.clone() } else { expected.clone() - res.clone() };
        let small_enough = diff.clone() / expected.clone() <= tolerance;
        let max_diff = expected.clone() * tolerance.clone();
        prop_assert!(
            small_enough,
            "\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            res.clone().to_f64(),
            expected.clone().to_f64(),
            diff.to_f64(),
            max_diff.to_f64()
        );
    }
}

prop_compose! {
    fn period_and_iterations()(p in long_period())(
        period in Just(p),
        iterations in iterations_up_to(p as u32),
    ) -> (u64, u32) {
      (period, iterations)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5_000))]
    #[test]
    fn iterated_price_u256_precision(
        (period, iterations) in period_and_iterations(),
        (a, b) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
        (c, d) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
    ) {
        let smoothing = smoothing_from_period(period);
        let prev = Rational128::from(a, b);
        let incoming = Rational128::from(c, d);

        let res = rational::iterated_price_ema_u256(iterations, prev, incoming, smoothing);
        let smoothing_adj = high_precision::rug_exp_smoothing(fraction_to_rational(smoothing), iterations);
        let expected = high_precision::rug_weighted_average(rational_to_rational(prev), rational_to_rational(incoming), smoothing_adj);

        let res = rational_to_rational(res);
        let tolerance = Rational::from((1, 1e30 as u128));

        let diff = if res >= expected { res.clone() - expected.clone() } else { expected.clone() - res.clone() };
        let small_enough = diff.clone() / expected.clone() <= tolerance;
        let max_diff = expected.clone() * tolerance.clone();
        prop_assert!(
            small_enough,
            "\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            res.clone().to_f64(),
            expected.clone().to_f64(),
            diff.to_f64(),
            max_diff.to_f64()
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100_000))]
    #[test]
    fn iterated_price_precision(
        (period, iterations) in period_and_iterations(),
        (a, b) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
        (c, d) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
    ) {
        let smoothing = smoothing_from_period(period);
        let prev = Rational128::from(a, b);
        let incoming = Rational128::from(c, d);

        let res = rational::iterated_price_ema(iterations, prev, incoming, smoothing);
        let smoothing_adj = high_precision::rug_exp_smoothing(fraction_to_rational(smoothing), iterations);
        let expected = high_precision::rug_weighted_average(rational_to_rational(prev), rational_to_rational(incoming), smoothing_adj);

        let res = rational_to_rational(res);
        let tolerance = Rational::from((1, 1e30 as u128));

        let diff = if res >= expected { res.clone() - expected.clone() } else { expected.clone() - res.clone() };
        let small_enough = diff.clone() / expected.clone() <= tolerance;
        let max_diff = expected.clone() * tolerance.clone();
        prop_assert!(
            small_enough,
            "\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            res.clone().to_f64(),
            expected.clone().to_f64(),
            diff.to_f64(),
            max_diff.to_f64()
        );
    }
}

fn bigger_and_smaller_rational() -> impl Strategy<Value = ((u128, u128), (u128, u128))> {
    ((MIN_BALANCE+1)..MAX_BALANCE, MIN_BALANCE..(MAX_BALANCE - 1)).prop_perturb(
        |(a, b), mut rng| ((a, b), (rng.gen_range(MIN_BALANCE..a), rng.gen_range(b..MAX_BALANCE)))
    )
}

use rational::u256_tuple_to_rational;
proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_000_000))]
    #[test]
    fn rational_rounding_sub(
        ((a, b), (c, d)) in bigger_and_smaller_rational()
    ) {
        let res = rational::rounding_sub(Rational128::from(a, b), Rational128::from(c, d)); //(a.into(), b.into()), (c.into(), d.into()));
        let expected = Rational::from((a, b)) - Rational::from((c, d));

        let res = rational_to_rational(res);
        let tolerance = Rational::from((1, 1u128 << 100));

        let diff = if res >= expected { res.clone() - expected.clone() } else { expected.clone() - res.clone() };
        let small_enough = diff.clone() / expected.clone() <= tolerance;
        let max_diff = expected.clone() * tolerance.clone();
        prop_assert!(
            small_enough,
            "\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
            res.clone().to_f64(),
            expected.clone().to_f64(),
            diff.to_f64(),
            max_diff.to_f64()
        );
    }
}

fn to_tuple(r: &Rational128) -> (u128, u128) {
    (r.n(), r.d())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn ema_small_rational_price_history_precision(
        (period, history) in ema_small_rational_price_history(),
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_rational_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = rational::iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, 1e20 as u128));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            rational_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]
    #[test]
    fn ema_rational_price_history_precision_variable_tolerance(
        (period, history) in ema_rational_price_history(),
        tolerance in (5_u32..120),
    ) {
        let tolerance = 2_u128.pow(tolerance);
        let smoothing = smoothing_from_period(period);
        println!("history:");
        for (r, i) in history.iter() {
            println!("{:?}, {}", to_tuple(r), i);
        }
        let rug_ema = high_precision::rug_fast_rational_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = rational::iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, tolerance));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            rational_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]
    #[test]
    fn comparison_ema_rational_price_history_precision(
        (period, history) in ema_rational_price_history(),
    ) {
        let tolerance = 2_u128.pow(10_u32);
        let smoothing = smoothing_from_period(period);
        println!("history:");
        for (r, i) in history.iter() {
            println!("{:?}, {}", to_tuple(r), i);
        }
        let rug_ema = high_precision::rug_fast_rational_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = rational::iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, tolerance));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            rational_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

prop_compose! {
    fn derived_price(p: Rational128)(p in Just(p))(
        price in Just(p).prop_perturb(|p, mut rng| {
            (
                rng.gen_range((p.n() / 10).max(MIN_BALANCE)..(p.n() * 10).max(MAX_BALANCE)),
                rng.gen_range((p.d() / 10).max(MIN_BALANCE)..(p.d() * 10).max(MAX_BALANCE)),
            )
        }
    )) -> (u128, u128) {
        price
    }
}

prop_compose! {
    fn slowly_changing_price_history(l: usize)(p in long_period(), initial_price in typical_price_rational())(
        period in Just(p),
        history in prop::collection::vec((derived_price(initial_price), iterations_up_to(100 as u32)), 2..l)
    ) -> (u64, Vec<((u128, u128), u32)>) {
        (period, history)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100_000))]
    #[test]
    fn slowly_changing_price_history_precision(
        (period, history) in slowly_changing_price_history(5),
    ) {
        let tolerance = 2_u128.pow(50_u32);
        let smoothing = smoothing_from_period(period);
        let history: Vec<(Rational128, u32)> = history.into_iter().map(|((n, d), iter)| (Rational128::from(n, d), iter)).collect();
        let rug_ema = high_precision::rug_fast_rational_price_ema(history.clone(), fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = rational::iterated_price_ema(iterations, ema, price, smoothing);
        }

        let relative_tolerance = Rational::from((1, tolerance));
        prop_assert_rational_relative_approx_eq!(
            rug_ema.clone(),
            rational_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

#[test]
fn failing_test(){
    let period = 10000;
    let history = vec![
        (Rational128::from(9161220807430355537988, 7740216577336008507136), 1),
        (Rational128::from(2068448995746894485377, 3197701212309655008641), 1),
        (Rational128::from(9311868072627396204070, 3467366716198208388262), 1),
        (Rational128::from(6076563079069306574963, 238472001247031185107), 103),
    ];
    let tolerance = 2_u128.pow(50_u32);
    let smoothing = smoothing_from_period(period);
    println!("history:");
    for (r, i) in history.iter() {
        println!("{:?}, {}", to_tuple(r), i);
    }
    let rug_ema = high_precision::rug_fast_rational_price_ema(history.clone(), fraction_to_rational(smoothing));

    let mut ema = history[0].0;
    for (price, iterations) in history.into_iter().skip(1) {
        ema = rational::iterated_price_ema(iterations, ema, price, smoothing);
    }

    let relative_tolerance = Rational::from((1, tolerance));
    assert_rational_relative_approx_eq!(
        rug_ema.clone(),
        rational_to_rational(ema),
        relative_tolerance,
        "high precision should be equal to low precision within tolerance"
    );
}

