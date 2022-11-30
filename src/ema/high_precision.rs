use crate::types::fraction;
use crate::types::{Balance, Fraction, Price};

use num_traits::One;
use num_traits::Pow;
use rug::ops::PowAssign;
use rug::{Integer, Rational};
use sp_arithmetic::{FixedPointNumber, FixedU128, Rational128};
use std::ops::Mul;
use std::ops::ShrAssign;

/// Round the given `r` to a close number where numerator and denominator have <= 256 bits.
pub(crate) fn round(r: &mut Rational) {
    r.mutate_numer_denom(|n, d| {
        let n_digits = n.significant_digits::<bool>();
        let d_digits = d.significant_digits::<bool>();
        if n_digits > 256 || d_digits > 256 {
            let shift = n_digits.saturating_sub(256).max(d_digits.saturating_sub(256));
            n.shr_assign(shift);
            d.shr_assign(shift);
        }
    });
}

/// Calculate the power of `r` via stepwise squaring and rounding to keep the memory size of `r`
/// within reasonable bounds.
///
/// Much faster for big `i` but less accurate than the built-in `pow` function.
pub(crate) fn stepwise_pow_approx(mut r: Rational, i: u32) -> Rational {
    if i <= 256 {
        return r.pow(i);
    }
    let next_power = i.next_power_of_two();
    let mut iter = if next_power == i { i } else { next_power / 2 };
    let rest = i - iter;
    let mut res_rest = stepwise_pow_approx(r.clone(), rest);
    round(&mut res_rest);
    while iter > 1 {
        iter /= 2;
        r.pow_assign(2);
        round(&mut r);
    }
    r * res_rest
}

pub fn smoothing_from_period(period: u64) -> Rational {
    Rational::from((2u64, period.max(1).saturating_add(1)))
}

/// Convert a fixed point number to an arbitrary precision rational number.
pub fn fixed_to_rational(f: FixedU128) -> Rational {
    Rational::from((f.into_inner(), FixedU128::DIV))
}

/// Convert a fixed point fraction to an arbitrary precision rational number.
pub fn fraction_to_rational(f: Fraction) -> Rational {
    Rational::from((f.to_bits(), fraction::DIV))
}

pub fn rational_to_rational(r: Rational128) -> Rational {
    Rational::from((r.n(), r.d()))
}

/// Convert a `Rational` number into its rounded `Integer` equivalent.
pub(crate) fn into_rounded_integer(r: Rational) -> Integer {
    let (num, den) = r.into_numer_denom();
    num.div_rem_round(den).0
}

/// Determine the final smoothing factor from initial `smoothing` and the number of `iterations`.
///
/// Uses a `pow` approximation with 256 bit precision to reduce execution time.
pub fn rug_exp_smoothing(smoothing: Rational, iterations: u32) -> Rational {
    debug_assert!(smoothing <= Rational::one());
    let complement = Rational::one() - smoothing;
    // in order to determine the iterated smoothing factor we exponentiate the complement
    let exp_complement = stepwise_pow_approx(complement, iterations);
    debug_assert!(exp_complement <= Rational::one());
    Rational::one() - exp_complement
}

/// Calculate the weighted average for the given balances by using arbitrary precision math.
///
/// Note: Rounding is biased very slightly towards `incoming` (on equal distance rounds away from
/// zero).
pub fn rug_balance_weighted_average(prev: Balance, incoming: Balance, weight: Rational) -> Integer {
    if incoming >= prev {
        prev + into_rounded_integer(weight.mul(incoming - prev))
    } else {
        prev - into_rounded_integer(weight.mul(prev - incoming))
    }
}

/// Calculate the weighted average for the given prices by using arbitrary precision math.
pub fn rug_price_weighted_average(prev: Price, incoming: Price, weight: Rational) -> Rational {
    let prev = fixed_to_rational(prev);
    let incoming = fixed_to_rational(incoming);
    if incoming >= prev {
        prev.clone() + weight.mul(incoming - prev)
    } else {
        prev.clone() - weight.mul(prev - incoming)
    }
}

/// Calculate the weighted average for the given values by using arbitrary precision math.
/// Returns a `Rational` of arbitrary precision.
pub fn rug_weighted_average(prev: Rational, incoming: Rational, weight: Rational) -> Rational {
    prev.clone() + weight.mul(incoming - prev)
}

/// Determine the exponential moving average of a history of balance values.
/// Starts the EMA with the first value.
/// Keeps track of arbitrary precision values during calculation but returns an `Integer` (rounded down).
pub fn rug_balance_ema(history: Vec<Balance>, smoothing: Rational) -> Integer {
    assert!(!history.is_empty());
    let mut current = Rational::from(history[0]);
    for balance in history.into_iter().skip(1) {
        current = rug_weighted_average(current.clone(), balance.into(), smoothing.clone());
    }
    // return rounded down integer
    into_rounded_integer(current)
}

pub fn rug_fast_balance_ema(history: Vec<(Balance, u32)>, smoothing: Rational) -> Integer {
    assert!(!history.is_empty());
    let mut current = Rational::from((history[0].0, 1));
    for (balance, iterations) in history.into_iter().skip(1) {
        let smoothing_adj = rug_exp_smoothing(smoothing.clone(), iterations);
        current = rug_weighted_average(current.clone(), balance.into(), smoothing_adj.clone());
    }
    into_rounded_integer(current)
}

/// Determine the exponential moving average of a history of price values.
/// Starts the EMA with the first value.
/// Returns an arbitrary precision `Rational` number.
pub fn rug_price_ema(history: Vec<Price>, smoothing: Rational) -> Rational {
    assert!(!history.is_empty());
    let mut current = fixed_to_rational(history[0]);
    for price in history.into_iter().skip(1) {
        current = rug_weighted_average(current.clone(), fixed_to_rational(price), smoothing.clone());
    }
    current
}

pub fn rug_fast_price_ema(history: Vec<(Price, u32)>, smoothing: Rational) -> Rational {
    assert!(!history.is_empty());
    let mut current = fixed_to_rational(history[0].0);
    for (price, iterations) in history.into_iter().skip(1) {
        let smoothing_adj = rug_exp_smoothing(smoothing.clone(), iterations);
        current = rug_weighted_average(current.clone(), fixed_to_rational(price), smoothing_adj.clone());
    }
    current
}

pub fn rug_fast_rational_price_ema(history: Vec<(Rational128, u32)>, smoothing: Rational) -> Rational {
    assert!(!history.is_empty());
    let mut current = rational_to_rational(history[0].0);
    for (price, iterations) in history.into_iter().skip(1) {
        let smoothing_adj = rug_exp_smoothing(smoothing.clone(), iterations);
        current = rug_weighted_average(current.clone(), rational_to_rational(price), smoothing_adj.clone());
    }
    current
}

// --- Tests
#[test]
fn fixed_to_rational_works() {
    assert_eq!(fixed_to_rational(FixedU128::from_float(0.25)), Rational::from((1, 4)));
}
