use crate::transcendental::saturating_powi_high_precision;
use crate::types::fraction;
use crate::types::{Balance, Fraction, Price};

use sp_arithmetic::traits::One;

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
    let exp_complement: Fraction = saturating_powi_high_precision(complement, iterations);
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
    fraction::frac(2, u128::from(period.max(1)).saturating_add(1))
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
        prev + fraction::multiply_by_fixed(weight, incoming - prev)
    } else {
        // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
        prev - fraction::multiply_by_fixed(weight, prev - incoming)
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
        prev + fraction::multiply_by_balance(weight, incoming - prev)
    } else {
        // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
        prev - fraction::multiply_by_balance(weight, prev - incoming)
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
