use crate::types::Balance;

use num_traits::{One, Zero};
use rust_decimal::prelude::*;

pub type Price = Decimal;
pub type Fraction = Decimal;

/// Calculate the iterated exponential moving average for the given prices.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_price_ema(iterations: u32, prev: Price, incoming: Price, smoothing: Fraction) -> Price {
    price_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
}

/// Calculate the iterated exponential moving average for the given balances.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_balance_ema(iterations: u32, prev: Balance, incoming: Balance, smoothing: Fraction) -> Balance {
    balance_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
}

/// Calculate the iterated exponential moving average for the given volumes.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_volume_ema(
    iterations: u32,
    prev: (Balance, Balance, Balance, Balance),
    incoming: (Balance, Balance, Balance, Balance),
    smoothing: Fraction,
) -> (Balance, Balance, Balance, Balance) {
    volume_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
}

/// Calculate the smoothing factor for a period from a given combination of original smoothing
/// factor and iterations by exponentiating the complement by the iterations.
///
/// Example:
/// `exp_smoothing(0.6, 2) = 1 - (1 - 0.6)^2 = 1 - 0.40^2 = 1 - 0.16 = 0.84`
///
/// ```
/// # use hydra_dx_math::ema::exp_smoothing;
/// # use hydra_dy_math::types::Fraction;
/// assert_eq!(exp_smoothing(Fraction::from_num(0.6), 2), FixedU128::from_num(0.84));
/// ```
pub fn exp_smoothing(smoothing: Fraction, iterations: u32) -> Fraction {
    debug_assert!(smoothing <= Fraction::one());
    let complement = Fraction::one() - smoothing;
    // in order to determine the iterated smoothing factor we exponentiate the complement
    let exp_complement: Fraction = powu_high_precision(complement, iterations);
    debug_assert!(exp_complement <= Fraction::one());
    Fraction::one() - exp_complement
}

/// Calculates smoothing factor alpha for an exponential moving average based on `period`:
/// `alpha = 2 / (period + 1)`. It leads to the "center of mass" of the EMA corresponding to be the
/// "center of mass" of a `period`-length SMA.
///
/// Possible alternatives for `alpha = 2 / (period + 1)`:
/// + `alpha = 1 - 0.5^(1 / period)` for a half-life of `period` or
/// + `alpha = 1 - 0.5^(2 / period)` to have the same median as a `period`-length SMA.
/// See https://en.wikipedia.org/wiki/Moving_average#Relationship_between_SMA_and_EMA
pub fn smoothing_from_period(period: u64) -> Fraction {
    Fraction::from(2) / Fraction::from(period.max(1).saturating_add(1))
}

/// Calculate a weighted average for the given prices.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `weight` is how much weight to give the new value.
///
/// Note: Rounding is slightly biased towards `prev`.
/// (`FixedU128::mul` rounds to the nearest representable value, rounding down on equidistance.
/// See [doc comment here](https://github.com/paritytech/substrate/blob/ce10b9f29353e89fc3e59d447041bb29622def3f/primitives/arithmetic/src/fixed_point.rs#L670-L671).)
pub fn price_weighted_average(prev: Price, incoming: Price, weight: Fraction) -> Price {
    debug_assert!(weight <= Fraction::one(), "weight must be <= 1");
    if incoming >= prev {
        // Safe to use bare `+` because `weight <= 1` and `a + (b - a) <= b`.
        // Safe to use bare `-` because of the conditional.
        prev + weight * (incoming - prev)
    } else {
        // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
        prev - weight * (prev - incoming)
    }
}

/// Calculate a weighted average for the given balances.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `weight` is how much weight to give the new value.
///
/// Note: Rounding is biased towards `prev`.
pub fn balance_weighted_average(prev: Balance, incoming: Balance, weight: Fraction) -> Balance {
    debug_assert!(weight <= Fraction::one(), "weight must be <= 1");
    if incoming >= prev {
        // Safe to use bare `+` because `weight <= 1` and `a + (b - a) <= b`.
        // Safe to use bare `-` because of the conditional.
        prev + (weight * Fraction::from(incoming - prev))
            .try_into()
            .unwrap_or(incoming - prev) // TODO: check for sanity
    } else {
        // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
        prev - (weight * Fraction::from(prev - incoming))
            .try_into()
            .unwrap_or(prev - incoming)
    }
}

/// Calculate a weighted average for the given volumes.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `weight` is how much weight to give the new value.
///
/// Note: Just delegates to `balance_weighted_average` under the hood.
/// Note: Rounding is biased towards `prev`.
pub fn volume_weighted_average(
    prev: (Balance, Balance, Balance, Balance),
    incoming: (Balance, Balance, Balance, Balance),
    weight: Fraction,
) -> (Balance, Balance, Balance, Balance) {
    debug_assert!(weight <= Fraction::one(), "weight must be <= 1");
    let (prev_a_in, prev_b_out, prev_a_out, prev_b_in) = prev;
    let (a_in, b_out, a_out, b_in) = incoming;
    (
        balance_weighted_average(prev_a_in, a_in, weight),
        balance_weighted_average(prev_b_out, b_out, weight),
        balance_weighted_average(prev_a_out, a_out, weight),
        balance_weighted_average(prev_b_in, b_in, weight),
    )
}

pub fn powu_high_precision(operand: Decimal, n: u32) -> Decimal {
    if operand == Decimal::zero() {
        return Decimal::zero();
    } else if n == 0 {
        return Decimal::one();
    } else if n == 1 {
        return operand;
    }

    // this determines when we use the taylor series approximation at 1
    // if boundary = 0, we will never use the taylor series approximation.
    // as boundary -> 1, we will use the taylor series approximation more and more
    // boundary > 1 can cause overflow in the taylor series approximation
    let boundary = Decimal::one()
        .checked_div(Decimal::from(10))
        .expect("1 / 10 does not fail; qed");
    match (
        boundary.checked_div(Decimal::from(n)),
        Decimal::one().checked_sub(operand),
    ) {
        (Some(b), Some(one_minus_operand)) if b > one_minus_operand => {
            powu_near_one(operand, n).unwrap_or_else(|| operand.powu(n.into()))
        }
        _ => operand.powu(n.into()),
    }
}

/// Determine `operand^n` for `operand` values close to but less than 1.
fn powu_near_one(operand: Decimal, n: u32) -> Option<Decimal> {
    if n == 0 {
        return Some(Decimal::one());
    } else if n == 1 {
        return Some(operand);
    }
    let one_minus_operand = Decimal::one().checked_sub(operand)?;

    // prevents overflows
    debug_assert!(Decimal::one().checked_div(Decimal::from(n))? > one_minus_operand);
    if Decimal::one().checked_div(Decimal::from(n))? <= one_minus_operand {
        return None;
    }

    let mut s_pos = Decimal::one();
    let mut s_minus = Decimal::zero();
    let mut t = Decimal::one();
    // increasing number of iterations will allow us to return a result for operands farther from 1,
    // or for higher values of n
    let iterations = 32_u32;
    for i in 1..iterations {
        // bare math fine because n > 1 and return condition below
        let b = one_minus_operand.checked_mul(Decimal::from(n - i + 1))?;
        let t_factor = b.checked_div(Decimal::from(i))?;
        t = t.checked_mul(t_factor)?;
        if i % 2 == 0 || operand > Decimal::one() {
            s_pos = s_pos.checked_add(t)?;
        } else {
            s_minus = s_minus.checked_add(t)?;
        }

        // if i >= b, all future terms will be zero because kth derivatives of a polynomial
        // of degree n where k > n are zero
        // if t == 0, all future terms will be zero because they will be multiples of t
        if i >= n || t == Decimal::zero() {
            return s_pos.checked_sub(s_minus);
        }
    }
    None // if we do not have convergence, we do not risk returning an inaccurate value
}
