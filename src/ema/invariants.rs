use crate::ema::*;
use crate::types::{Balance, Price};
use high_precision::fixed_to_rational;
use num_traits::Pow;
use num_traits::{Bounded, CheckedDiv};
use rug::{Float, Integer, Rational};
use std::io::stdout;
use std::io::Write;
use std::ops::Mul;
use std::str::FromStr;

use crate::ema::invariants::fraction::{rug_exp_smoothing, Fraction};
use crate::ema::invariants::numerical::iterated_balance_ema_near_one;
use proptest::prelude::*;
use sp_arithmetic::traits::Saturating;
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

macro_rules! prop_assert_rational_percentage_approx_eq {
    ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x - $y } else { $y - $x };
        prop_assert!(
            diff.clone() / $x <= $z,
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
            // (smoothing_from_period(100), 100),
            // (smoothing_from_period(14_400), 14_400),
            (smoothing_from_period(100), 100),
            (smoothing_from_period(200_000), 200_000),
            (smoothing_from_period(100_800), 100_800),
            (smoothing_from_period(5), 5),
        ][i]
    })
}

fn typical_period() -> impl Strategy<Value = u32> {
    1u32..200_000u32
}

// 'mult' is the multiplier from the period of the EMA to the max exponent
// so if we want to only test updates that are at most twice the period of the EMA, we set
// mult = 2
// the higher mult is set, the more iterations we will need to allow in pow_near_one
// for the Taylor series to converge
fn typical_exp(mult: f32) -> impl Strategy<Value = (FixedU128, u32)> {
    typical_period().prop_flat_map(move |period| {
        let smoothing = smoothing_from_period(period.into());
        (Just(smoothing), 0..(mult * period as f32) as u32)
    })
}

// --- History Strategies
fn ema_price_history() -> impl Strategy<Value = Vec<(Price, u32)>> {
    prop::collection::vec((any_fixed(), 1_u32..500_000), 1..10)
}

fn ema_balance_history() -> impl Strategy<Value = Vec<(Balance, u32)>> {
    prop::collection::vec(((1e12 as Balance)..(1e28 as Balance), 1_u32..200_001), 2..10)
}

fn to_regular_history<T: Copy>(history: Vec<(T, u32)>) -> Vec<T> {
    let expanded: Vec<Vec<_>> = history
        .into_iter()
        .map(|(v, iterations)| vec![v; iterations as usize])
        .collect();
    expanded.concat()
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
        let rug_exp = high_precision::rug_exp_smoothing_fixed(smoothing, iterations);

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
        let rug_exp = high_precision::rug_exp_smoothing_fixed(smoothing, iterations);

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
        let rug_exp = high_precision::rug_exp_smoothing_fixed(smoothing, iterations);

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
        let rug_exp = high_precision::rug_exp_smoothing_fixed(smoothing, iterations);

        let tolerance = Rational::from((20_000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fixed_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

// --- use fixed crate types
// use fixed::types::U1F127;
pub(crate) mod fraction {
    use crate::types::{Balance, Price};
    pub use fixed::types::U1F127 as Fraction;
    use num_traits::One;
    use num_traits::Pow;
    use rug::Rational;
    use sp_arithmetic::helpers_128bit::multiply_by_rational_with_rounding;
    use sp_arithmetic::per_things::Rounding;
    use sp_arithmetic::FixedPointNumber;
    use sp_arithmetic::FixedU128;

    const SMALLEST_NON_ZERO: Fraction = Fraction::from_bits(1);
    pub const DIV: u128 = 1u128 << 127;

    pub fn fraction_to_rational(f: Fraction) -> Rational {
        Rational::from((f.to_bits(), DIV))
    }

    pub fn fraction_to_fixed(f: Fraction) -> FixedU128 {
        FixedU128::saturating_from_rational(f.to_bits(), DIV)
    }

    pub fn fixed_to_fraction(f: FixedU128) -> Fraction {
        (Fraction::from_num(1) / FixedU128::DIV) * f.into_inner()
    }

    pub fn multiply_by_balance(f: Fraction, b: Balance) -> Balance {
        debug_assert!(f <= Fraction::ONE);
        multiply_by_rational_with_rounding(b, f.to_bits(), DIV, Rounding::NearestPrefDown)
            .expect("f.to_bits() <= DIV, therefore the result must fit in u128; qed")
    }

    #[test]
    fn fraction_representation() {
        assert_eq!(Fraction::from_num(0.25), Fraction::ONE / 4);

        let expected_smallest_non_zero = Fraction::ONE / (u128::MAX / 2);
        assert_eq!(SMALLEST_NON_ZERO, expected_smallest_non_zero);

        assert_eq!(Fraction::from_num(0.5), Fraction::from_bits(1 << 126));

        assert_eq!(Fraction::from_num(1), Fraction::from_bits(1 << 127));

        assert_eq!(fraction_to_rational(Fraction::from_num(0.5)), Rational::from((1, 2)));
    }

    #[test]
    fn multiply_by_balance_works() {
        let frac = Fraction::from_num(0.25);
        let balance = 1e16 as Balance;
        let expected = balance / 4;
        assert_eq!(multiply_by_balance(frac, balance), expected);
    }

    pub fn smoothing_from_period(period: u64) -> Fraction {
        (Fraction::ONE / (u128::from(period.max(1)) + 1)) * 2
    }

    pub fn exp_smoothing(smoothing: Fraction, iterations: u32) -> Fraction {
        debug_assert!(smoothing <= Fraction::ONE);
        let complement = Fraction::ONE - smoothing;
        // in order to determine the iterated smoothing factor we exponentiate the complement
        let exp_complement = crate::transcendental::powi_high_precision(complement, iterations).unwrap_or(SMALLEST_NON_ZERO);
        Fraction::ONE - exp_complement
    }

    pub fn rug_exp_smoothing(smoothing: Fraction, iterations: u32) -> Rational {
        debug_assert!(smoothing <= Fraction::ONE);
        let complement = Rational::one() - fraction_to_rational(smoothing);
        // in order to determine the iterated smoothing factor we exponentiate the complement
        let exp_complement = complement.pow(iterations);
        debug_assert!(exp_complement <= Rational::one());
        Rational::one() - exp_complement
    }

    pub fn balance_weighted_average(prev: Balance, incoming: Balance, weight: Fraction) -> Balance {
        debug_assert!(weight <= Fraction::ONE, "weight must be <= 1");
        if incoming >= prev {
            // Safe to use bare `+` because `weight <= 1` and `a + (b - a) <= b`.
            // Safe to use bare `-` because of the conditional.
            prev + multiply_by_balance(weight, incoming - prev)
        } else {
            // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
            prev - multiply_by_balance(weight, prev - incoming)
        }
    }

    pub fn iterated_balance_ema(iterations: u32, prev: Balance, incoming: Balance, smoothing: Fraction) -> Balance {
        balance_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
    }

    pub fn fraction_times_fixed(fraction: Fraction, fixed: FixedU128) -> FixedU128 {
        debug_assert!(fraction <= Fraction::ONE);
        FixedU128::from_inner(
            multiply_by_rational_with_rounding(fixed.into_inner(), fraction.to_bits(), DIV, Rounding::NearestPrefDown)
                .expect("f.to_bits() <= DIV, therefore the result must fit in u128; qed"),
        )
    }

    pub fn price_weighted_average(prev: Price, incoming: Price, weight: Fraction) -> Price {
        debug_assert!(weight <= Fraction::ONE, "weight must be <= 1");
        if incoming >= prev {
            // Safe to use bare `+` because `weight <= 1` and `a + (b - a) <= b`.
            // Safe to use bare `-` because of the conditional.
            prev + fraction_times_fixed(weight, incoming - prev)
        } else {
            // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
            prev - fraction_times_fixed(weight, prev - incoming)
        }
    }

    pub fn iterated_price_ema(iterations: u32, prev: Price, incoming: Price, smoothing: Fraction) -> Price {
        price_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
    }
}

fn period_fraction() -> impl Strategy<Value = fraction::Fraction> {
    (1u64..200_000).prop_map(|period| fraction::smoothing_from_period(period))
}

proptest! {
    #[test]
    fn fraction_times_fixed_precision(
        smoothing in period_fraction(),
        fixed in any_fixed(),
    ) {
        let rational = fixed_to_rational(fixed) / fraction::fraction_to_rational(smoothing);
        let conversion = fixed * fraction::fraction_to_fixed(smoothing);
        let conversion_distance = (rational.clone() - fixed_to_rational(conversion)).abs();
        let multiply = fraction::fraction_times_fixed(smoothing, fixed);
        let multiply_distance = (rational.clone() - fixed_to_rational(multiply)).abs();
        prop_assert!(multiply_distance < conversion_distance);
    }
}

proptest! {
    // #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn exponential_smoothing_precision_arbitrary_smoothing_using_fraction(
        period in 1u64..200_000,
        iterations in 1_u32..5_256_000,
    ) {
        let smoothing = fraction::smoothing_from_period(period);
        let exp = fraction::exp_smoothing(smoothing, iterations);
        let rug_exp = fraction::rug_exp_smoothing(smoothing, iterations);

        let tolerance = Rational::from((1_000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            fraction::fraction_to_rational(exp),
            rug_exp.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

proptest! {
    // #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn iterated_ema_precision_with_fraction(
        period in 1u64..200_000,
        iterations in 1_u32..MAX_ITERATIONS,
        (start_balance, incoming_balance) in
                (1e12 as Balance..(1e24 as Balance))
                    .prop_perturb(|n, mut rng| (n, rng.gen_range(n..(1e26 as Balance))))
    ) {
        let smoothing = fraction::smoothing_from_period(period);

        let expected = high_precision::rug_balance_weighted_average(start_balance, incoming_balance, fraction::rug_exp_smoothing(smoothing, iterations));
        let new_oracle = fraction::iterated_balance_ema(iterations, start_balance, incoming_balance, smoothing);

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
    fn ema_balance_history_precision_with_fraction(
        history in ema_balance_history(),
        period in 1u64..200_000,
    ) {
        let smoothing = fraction::smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_balance_ema(history.clone(), fraction::fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (balance, iterations) in history.into_iter().skip(1) {
            ema = fraction::iterated_balance_ema(iterations, ema, balance, smoothing);
        }
        // for balance in to_regular_history(history).into_iter().skip(1) {
        //     ema = balance_weighted_average(ema, balance, smoothing);
        // }

        let tolerance = 1;
        prop_assert_approx_eq!(
            rug_ema.clone(),
            ema,
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
        // assert!(false);
    }
}

fn saturating_pow_temp(a: FixedU128, exp: usize) -> FixedU128 {
    if exp == 0 {
        return FixedU128::saturating_from_integer(1);
    }

    let exp = exp as u32;
    let msb_pos = 32 - exp.leading_zeros();

    let mut result = FixedU128::saturating_from_integer(1);
    let mut pow_val = a;
    for i in 0..msb_pos {
        if ((1 << i) & exp) > 0 {
            result = result.saturating_mul(pow_val);
        }
        pow_val = pow_val.saturating_mul(pow_val);
        dbg!(pow_val);
        dbg!(result);
    }
    result
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1))]
    #[test]
    fn pow_test_temp(
        period in 1u64..200_000,
    ) {

        let a = FixedU128::from(2);
        let b = 5_u32;

        dbg!(saturating_pow_temp(a, b as usize));
        assert!(false);
    }
}

proptest! {
    #[test]
    fn ema_price_history_precision_with_fraction(
        history in ema_price_history(),
        period in 1u64..200_000,
    ) {
        let smoothing = fraction::smoothing_from_period(period);
        let rug_ema = high_precision::rug_fast_price_ema(history.clone(), fraction::fraction_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = fraction::iterated_price_ema(iterations, ema, price, smoothing);
        }
        // for balance in to_regular_history(history).into_iter().skip(1) {
        //     ema = balance_weighted_average(ema, balance, smoothing);
        // }

        let relative_tolerance = Rational::from((1, 1e24 as u128));
        prop_assert_rational_percentage_approx_eq!(
            rug_ema.clone(),
            fixed_to_rational(ema),
            relative_tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}

fn small_rational_close_to_one() -> impl Strategy<Value = Rational>{
    (1u64..1_000, 5_000u64..200_000)
        .prop_map(|(a, b)| Rational::one() - Rational::from((a, b)))
}

proptest! {
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

pub(crate) mod numerical {
    use crate::ema::balance_weighted_average;
    use crate::ema::invariants::fraction;
    use crate::ema::invariants::fraction::{Fraction, DIV};
    use crate::types::Balance;
    use crate::MathError;
    use fixed::types::extra::U127;
    use fixed::types::{U1F127, U64F64};
    use num_traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, One, Zero};
    use sp_arithmetic::traits::Saturating;
    use sp_arithmetic::{FixedPointNumber, FixedU128};

    // This approach is taylor series expansion of x^n around x = 1
    // It should be efficient and accurate for x close to 1
    // It will be less efficient for x farther from 1, and for sufficiently high n
    pub fn pow_near_one(x: FixedU128, n: u32) -> Option<FixedU128> {
        let mut s_pos = FixedU128::one();
        let mut s_minus = FixedU128::zero();
        let mut t = FixedU128::one();
        // dbg!((x,n));
        if (n == 0_u32) | (x == FixedU128::one()) {
            return Some(FixedU128::one());
        }
        if x == FixedU128::zero() {
            return Some(FixedU128::zero());
        }
        // increasing number of iterations will allow us to return a result for x farther from 1,
        // or for higher values of n
        let iterations = 32_u32;
        for i in 1..iterations {
            // dbg!((n,i));
            let one_minus_x = FixedU128::one().checked_sub(&x)?;
            let pow_minus_i = FixedU128::from_u32(n - i + 1_u32);
            let b = one_minus_x.saturating_mul(pow_minus_i);
            let t_factor = b.checked_div(&FixedU128::from_u32(i))?;
            t = t.checked_mul(&t_factor)?;
            if (i % 2 == 0) | (x > FixedU128::one()) {
                s_pos = s_pos.checked_add(&t)?;
            } else {
                s_minus = s_minus.checked_add(&t)?;
            }

            // if i >= n, all future terms will be zero because kth derivatives of a polynomial
            // of degree n where k > n are zero
            // if t == 0, all future terms will be zero because they will be multiples of t
            if (i >= n) | (t == FixedU128::zero()) {
                return s_pos.checked_sub(&s_minus);
            }
        }
        return None; // if we do not have convergence, we do not risk returning an inaccurate value
    }

    pub fn iterated_balance_ema_near_one(
        iterations: u32,
        prev: Balance,
        incoming: Balance,
        smoothing: FixedU128,
    ) -> Balance {
        dbg!((smoothing, iterations));
        let weight = exp_smoothing_near_one(smoothing, iterations);
        dbg!(weight.clone());
        balance_weighted_average(prev, incoming, weight)
    }

    pub fn iterated_balance_frac_ema_near_one(
        iterations: u32,
        prev: Balance,
        incoming: Balance,
        smoothing: FixedU128,
    ) -> Balance {
        if iterations == 0_u32 {
            return prev;
        } else if smoothing == FixedU128::one() {
            return incoming;
        }
        dbg!((smoothing, iterations));
        let weight = exp_smoothing_frac_near_one(smoothing, iterations);
        dbg!(weight.clone());
        balance_weighted_average(prev, incoming, weight)
    }

    pub fn exp_smoothing_near_one(smoothing: FixedU128, iterations: u32) -> FixedU128 {
        debug_assert!(smoothing <= FixedU128::one());
        let complement = FixedU128::one() - smoothing;
        // in order to determine the iterated smoothing factor we exponentiate the complement
        let mult = complement.saturating_mul_int(iterations as u128);
        if mult < 1_u128 {
            dbg!(mult);
            let exp_complement = pow_near_one(complement, iterations).unwrap();
            debug_assert!(exp_complement <= FixedU128::one());
            dbg!(exp_complement);
            return FixedU128::one() - exp_complement;
        } else {
            let exp_complement = pow_near_one(complement, iterations).unwrap();
            debug_assert!(exp_complement <= FixedU128::one());
            return FixedU128::one() - exp_complement;

            // let exp_complement2 = complement.saturating_pow(iterations as usize);
            // debug_assert!(exp_complement2 <= FixedU128::one());
            // dbg!(exp_complement2);
            // return FixedU128::one() - exp_complement2;
        }
        // debug_assert!(exp_complement <= FixedU128::one());
        // dbg!(exp_complement);
        // FixedU128::one() - exp_complement
        // if smoothing.checked_mul(&FixedU128::from_u32(iterations)).unwrap() > FixedU128::from_float(0.5) {
        //     FixedU128::one() - exp_complement_colin
        // } else {
        //     FixedU128::one() - exp_complement
        // }
    }

    pub fn exp_smoothing_frac_near_one(smoothing: FixedU128, iterations: u32) -> FixedU128 {
        debug_assert!(smoothing <= FixedU128::one());
        let complement = FixedU128::one() - smoothing;
        // in order to determine the iterated smoothing factor we exponentiate the complement
        let exp_complement = frac_power(complement, iterations).unwrap();
        dbg!(exp_complement);
        FixedU128::one() - exp_complement
    }

    pub fn frac_power_near_one(x: Fraction, n: u32) -> Option<Fraction> {
        let zero = Fraction::from_num(0);
        let one = Fraction::from_num(1);
        // let two = Fraction::from_num(2);

        let one_minus_x = one.checked_sub(x)?;

        assert!(one.checked_div_int(n as u128)? > one_minus_x); // prevents overflows

        let mut s_pos = one;
        let mut s_minus = zero;
        let mut t = one;
        dbg!((x, n));
        if (n == 0_u32) | (x == one) {
            dbg!("yes!");
            return Some(one);
        }
        if x == zero {
            return Some(zero);
        }
        // increasing number of iterations will allow us to return a result for x farther from 1,
        // or for higher values of n
        let iterations = 32_u32;
        for i in 1..iterations {
            // dbg!((n,i));

            let pow_minus_i = n - i + 1_u32;
            let b = one_minus_x.checked_mul_int(pow_minus_i as u128)?;
            let t_factor = b.checked_div_int(i as u128)?;
            t = t.checked_mul(t_factor)?;
            if (i % 2 == 0) | (x > one) {
                s_pos = s_pos.checked_add(t)?;
            } else {
                s_minus = s_minus.checked_add(t)?;
            }

            // if i >= n, all future terms will be zero because kth derivatives of a polynomial
            // of degree n where k > n are zero
            // if t == 0, all future terms will be zero because they will be multiples of t
            if (i >= n) | (t == zero) {
                return s_pos.checked_sub(s_minus);
            }
        }
        return None; // if we do not have convergence, we do not risk returning an inaccurate value
    }

    pub fn frac_power(x: FixedU128, n: u32) -> Option<FixedU128> {
        let x_f = fraction::fixed_to_fraction(x);
        let one = Fraction::ONE;
        let one_minux_x = one.checked_sub(x_f)?;

        // this determines when we use the taylor series approximation at 1
        // if boundary = 0, we will never use the taylor series approximation.
        // as boundary -> 1, we will use the taylor series approximation more and more
        // boundary > 1 can cause overflow in the taylor series approximation
        let boundary = Fraction::from_num(0.1);
        if n == 0_u32 {
            if x == FixedU128::zero() {
                return None;
            } else {
                return Some(FixedU128::one());
            }
        }
        if (boundary.checked_div_int(n as u128)? > one_minux_x) {
            return Some(fraction::fraction_to_fixed(frac_power_near_one(x_f, n)?));
        } else {
            // let x_f = (U64F64::from_num(1) / FixedU128::DIV) * x.into_inner();
            // let result: U64F64 = crate::transcendental::powi(x_f, n).unwrap();
            // let result_fixed = FixedU128::saturating_from_rational(result.to_bits(), 1u128 << 64);
            // return Some(result_fixed);
            let result = x.saturating_pow(n as usize);
            return Some(result);
        }
    }
}

#[test]
fn pow_near_one_works() {
    let x = FixedU128::from_rational(1, 2);
    let n = 2_u32;
    let result = numerical::pow_near_one(x, n);
    assert_eq!(result, Some(FixedU128::from_rational(1, 4)));

    let x = FixedU128::from_rational(2, 3);
    let n = 2_u32;
    let result = numerical::pow_near_one(x, n);
    assert_eq!(result, Some(FixedU128::from_rational(4, 9)));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn pow_near_one_is_accurate_for_long_updates(
        (smoothing, period) in typical_exp(1.5 as f32),
    ) {
        let result = numerical::pow_near_one(FixedU128::one() - smoothing, period).unwrap();
        // let period_int = Rational::from((period, 1_u32));
        let complement_rational = fixed_to_rational(FixedU128::one() - smoothing);
        let expected = complement_rational.pow(period);
        let result_rational = fixed_to_rational(result);
        dbg!(&result_rational.to_f64());
        dbg!(&expected.to_f64());
        prop_assert_approx_eq!(expected.clone(), result_rational.clone(), 1_u128, "pow_near_one_is_accurate");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn pow_near_one_is_accurate_or_returns_no_results(
        smoothing in fixed_above_zero_and_less_or_equal_one(),
        period in u32::MIN..u32::MAX,
    ) {
        let result = numerical::pow_near_one(FixedU128::one() - smoothing, period);
        if result.is_some() {
            // let period_int = Rational::from((period, 1_u32));
            let complement_rational = fixed_to_rational(FixedU128::one() - smoothing);
            let expected = complement_rational.pow(period);
            let result_rational = fixed_to_rational(result.unwrap());
            dbg!(&result_rational.to_f64());
            dbg!(&expected.to_f64());
            prop_assert_approx_eq!(expected.clone(), result_rational.clone(), 1_u128, "pow_near_one_is_accurate_or_returns_no_results");
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn test_balance_ema_updates(
        (smoothing, period) in typical_exp(1.5 as f32),
        prev in 1000_u128..1_000_000_000_000_000_000_000_000,
        incoming in 1000_u128..1_000_000_000_000_000_000_000_000,
    ) {
        let result = numerical::iterated_balance_ema_near_one(period, prev, incoming, smoothing);
        let expected = high_precision::rug_iterated_balance_ema(period, prev, incoming, smoothing);
        dbg!(result.clone());
        dbg!(expected.clone());

        let mut diff;
        if expected.clone() < result.clone() {
            diff = result.clone() - expected.clone();
        }
        else {
            diff = expected.clone() - result.clone();
        }

        let abs_diff_max = 10_u128;
        // assert!( diff < abs_diff_max);
        let pct_diff_max = Rational::from((1, 1_000_000_000_000_000_u128));
        if diff > abs_diff_max {
            prop_assert!(Rational::from((diff.clone(), expected.clone())) < pct_diff_max, "test_balance_ema_updates");
        }

        // // current implementation, fails this test
        // let current_result = iterated_balance_ema(period, prev, incoming, smoothing);
        // dbg!(current_result.clone());
        // let mut diff2;
        // if expected.clone() < current_result.clone() {
        //     diff2 = current_result.clone() - expected.clone();
        // }
        // else {
        //     diff2 = expected.clone() - current_result.clone();
        // }
        //
        // let abs_diff_max2 = 10_u128;
        //
        // if diff2 > abs_diff_max {
        //     prop_assert!(Rational::from((diff2, expected.clone())) < pct_diff_max, "test_balance_ema_updates");
        // }

    }
}

#[test]
fn test_frac_power() {
    let x = FixedU128::from_rational(1, 2);
    let n = 2_u32;
    let result = numerical::frac_power(x, n);
    assert_eq!(result, Some(FixedU128::from_rational(1, 4)));
    dbg!(result);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn frac_pow_accurate_for_long_updates(
        (smoothing, period) in typical_exp(1.5 as f32),
    ) {
        let result = numerical::frac_power(FixedU128::one() - smoothing, period).unwrap();
        // let period_int = Rational::from((period, 1_u32));
        let complement_rational = fixed_to_rational(FixedU128::one() - smoothing);
        let expected = complement_rational.pow(period);
        let result_rational = fixed_to_rational(result);
        dbg!(&result_rational.to_f64());
        dbg!(&expected.to_f64());
        prop_assert_approx_eq!(expected.clone(), result_rational.clone(), 1_u128, "frac_pow_accurate_for_long_updates");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn test_frac_balance_ema_updates(
        (smoothing, period) in typical_exp(1.5 as f32),
        prev in 1000_u128..1_000_000_000_000_000_000_000_000,
        incoming in 1000_u128..1_000_000_000_000_000_000_000_000,
    ) {
        let result = numerical::iterated_balance_frac_ema_near_one(period, prev, incoming, smoothing);
        let expected = high_precision::rug_iterated_balance_ema(period, prev, incoming, smoothing);
        dbg!(result.clone());
        dbg!(expected.clone());

        let mut diff;
        if expected.clone() < result.clone() {
            diff = result.clone() - expected.clone();
        }
        else {
            diff = expected.clone() - result.clone();
        }

        let abs_diff_max = 10_u128;
        // assert!( diff < abs_diff_max);
        let pct_diff_max = Rational::from((1, 1_000_000_000_000_000_u128));
        if diff > abs_diff_max {
            prop_assert!(Rational::from((diff.clone(), expected.clone())) < pct_diff_max, "test_balance_ema_updates");
        }

        // // current implementation, fails this test
        // let current_result = iterated_balance_ema(period, prev, incoming, smoothing);
        // dbg!(current_result.clone());
        // let mut diff2;
        // if expected.clone() < current_result.clone() {
        //     diff2 = current_result.clone() - expected.clone();
        // }
        // else {
        //     diff2 = expected.clone() - current_result.clone();
        // }
        //
        // let abs_diff_max2 = 10_u128;
        //
        // if diff2 > abs_diff_max {
        //     prop_assert!(Rational::from((diff2, expected.clone())) < pct_diff_max, "test_balance_ema_updates");
        // }

    }
}

// --- History Tests

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn ema_balance_history_precision(
        history in ema_balance_history(),
        period in 10u64..200_000,
    ) {
        // let smoothing = smoothing_from_period(period);

        let smoothing_set = fraction::Fraction::from_num(0.00006103515625);

        let smoothing = fraction::fraction_to_fixed(smoothing_set);
        let smoothing_rational = fixed_to_rational(smoothing);
        // let smoothing_precise = high_precision::smoothing_from_period(period);
        let smoothing_precise = Rational::from((1, 16384));

        // dbg!(history.clone());
        // let regular_history = to_regular_history(history.clone());
        // dbg!(regular_history.clone());
        // let mut ema_one = regular_history[0];
        // // for val in regular_history[1..].iter() {
        // for val in regular_history.into_iter().skip(1) {
        //     ema_one = balance_weighted_average(ema_one, val, smoothing);
        // }

        let mut ema = history[0].0;
        for (balance, iterations) in history.clone().into_iter().skip(1) {
            ema = iterated_balance_ema(iterations, ema, balance, smoothing);
        }



        // let mut ema_numerical = history[0].0;
        // for (balance, iterations) in history.clone().into_iter().skip(1) {
        //     ema_numerical = numerical::iterated_balance_ema_near_one(iterations, ema_numerical, balance, smoothing);
        // }
        //
        // let smoothing_f = smoothing_set;
        //
        // let mut ema_f = history[0].0;
        // for (balance, iterations) in history.clone().into_iter().skip(1) {
        //     ema_f = fraction::iterated_balance_ema(iterations, ema_f, balance, smoothing_f);
        // }

        // let mut ema_partial = history[0].0;
        // let mut prev = ema_partial;
        // for (balance, iterations) in history.clone().into_iter().skip(1) {
        //     let complement = Rational::one() - smoothing_rational.clone();
        //     let exp_complement = complement.pow(iterations);
        //     dbg!(exp_complement.clone().to_f64());
        //     // let weight = FixedU128::one() - rational_to_fixed(exp_complement.clone());
        //     // ema_partial = balance_weighted_average(prev, balance, weight);
        //     // prev = ema_partial;
        // }

        let rug_ema = high_precision::rug_fast_balance_ema(history.clone(), smoothing_precise.clone());

        // let mut ema2 = history[0].0;
        // let mut ema3 = Rational::from((history[0].0, 1));
        // for (balance, iterations) in history.clone().into_iter().skip(1) {
        //     ema2 = high_precision::rug_iterated_balance_ema(iterations, ema2, balance, smoothing.clone()).to_u128().unwrap();
        //     dbg!(ema2);
        //     let exp_smoothing2 = high_precision::rug_exp_smoothing_rational(smoothing_precise.clone(), iterations);
        //     dbg!(exp_smoothing2.to_f64());
        //     if balance >= ema3 {
        //         // let res = high_precision::into_rounded_integer(exp_smoothing2.mul(balance - ema3.to_u128().unwrap()));
        //         let res = exp_smoothing2.mul(Rational::from((balance, 1)) - ema3.clone());
        //         // dbg!(res.clone());
        //         ema3 = ema3 + res;
        //         dbg!(ema3.clone().to_f64());
        //     } else {
        //         // let res = high_precision::into_rounded_integer(exp_smoothing2.mul(ema3.to_u128().unwrap() - balance));
        //         let res = exp_smoothing2.mul(ema3.clone() - Rational::from((balance, 1)));
        //         // dbg!(res.clone());
        //         ema3 = ema3 - res;
        //         dbg!(ema3.clone().to_f64());
        //     }
        // }



        // let smoothing_rational_f = fraction::fraction_to_rational(smoothing_f);



        let tolerance = 1_000_u128;
        dbg!(ema);
        // dbg!(ema_one);
        // dbg!(ema_numerical);
        // dbg!(ema_partial);
        // dbg!(ema_f);
        dbg!(rug_ema.clone());
        // dbg!(rug_ema_f.clone());
        // dbg!(smoothing.clone());
        // dbg!(smoothing_rational.clone().to_f64());
        // dbg!(smoothing_rational_f.clone().to_f64());
        // dbg!(smoothing_rational_f.clone().to_f64() - smoothing_rational.clone().to_f64());

        let test_ema = ema;

        let mut diff;
        if rug_ema.clone() < test_ema {
            diff = test_ema - rug_ema.clone();
        }
        else {
            diff = rug_ema.clone() - test_ema;
        }
        dbg!(Rational::from((diff.clone(), rug_ema.clone())).to_f64());
        // assert!(Rational::from((diff, rug_ema.clone())) < Rational::from((1, 1_000_000_000_000_u128)));

        // From analysis, we have a relationship between W = smoothing factor and E = error:
        // W >= 1 / (E - 1)
        // This was derived for prices, but it should hold for balances as well.
        // an absolute error of 10^6 in balances would constitute E = 10^{-6} since we are
        // assuming balances have 12 decimal places.

        // Solving this equation, we see that
        // E - 1 >= 1 / W
        // E >= 1 / W + 1
        // E >= 1 / W + 1

        // So given W, we should be able to guarantee that our error is not more than 1 / W + 1
        let max_error = smoothing_precise.recip() + Rational::from((1, 1));
        dbg!(max_error.clone().to_f64());
        assert!(diff < max_error);

        // prop_assert_approx_eq!(
        //     rug_ema.clone(),
        //     ema_colin,
        //     tolerance,
        //     "high precision should be equal to low precision within tolerance"
        // );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn rug_ema_are_similar(
        history in ema_balance_history(),
        period in 1u64..200_000,
    ) {
        let smoothing = smoothing_from_period(period);
        let smoothing_rational = fixed_to_rational(smoothing);
        let rug_ema = high_precision::rug_balance_ema(to_regular_history(history.clone()), smoothing_rational.clone());

        let mut ema = history[0].0;
        dbg!(history.clone());
        let regular_history = to_regular_history(history.clone());
        dbg!(regular_history.clone());

        let smoothing_f = fraction::smoothing_from_period(period);
        let smoothing_rational_f = fraction::fraction_to_rational(smoothing_f);
        let rug_ema_f = high_precision::rug_balance_ema(to_regular_history(history.clone()), smoothing_rational_f.clone());

        let tolerance = 2147483646;
        dbg!(rug_ema.clone());
        dbg!(rug_ema_f.clone());

        prop_assert_approx_eq!(
            smoothing_rational.clone(),
            smoothing_rational_f.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );

    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn rug_pow_are_similar(
        period in 9736_u64..9737,
        iterations in 340_u32..341,
    ) {
        let smoothing = smoothing_from_period(period);
        let complement_rational = Rational::from((1_u8,1_u8)) - fixed_to_rational(smoothing);
        let rug_pow = complement_rational.pow(iterations);

        let smoothing_f = fraction::smoothing_from_period(period);
        let complement_rational_f = Rational::from((1_u8,1_u8)) - fraction::fraction_to_rational(smoothing_f);
        let rug_pow_f = complement_rational_f.pow(iterations);



        let tolerance = 10;
        dbg!(rug_pow.clone().to_f64());
        dbg!(rug_pow_f.clone().to_f64());
        prop_assert_approx_eq!(
            rug_pow.clone(),
            rug_pow_f.clone(),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
        assert!(false);
    }

}


proptest! {
    // #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn ema_price_history_precision(
        history in ema_price_history(),
        period in 1u64..200_000,
    ) {
        let smoothing = smoothing_from_period(period);
        let rug_ema = high_precision::rug_price_ema(to_regular_history(history.clone()), fixed_to_rational(smoothing));

        let mut ema = history[0].0;
        for (price, iterations) in history.into_iter().skip(1) {
            ema = iterated_price_ema(iterations, ema, price, smoothing);
        }
        // for price in to_regular_history(history).into_iter().skip(1) {
        //     ema = price_weighted_average(ema, price, smoothing);
        // }

        let tolerance = Rational::from((1000, FixedU128::DIV));
        prop_assert_rational_approx_eq!(
            rug_ema.clone(),
            fixed_to_rational(ema),
            tolerance,
            "high precision should be equal to low precision within tolerance"
        );
    }
}
