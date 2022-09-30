use crate::types::{Balance, Price};

use num_traits::CheckedMul;
use sp_arithmetic::traits::One;
use sp_arithmetic::traits::Saturating;
use sp_arithmetic::FixedPointNumber;
use sp_arithmetic::FixedU128;

/// Calculate the iterated exponential moving average for the given prices.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_price_ema(iterations: u32, prev: Price, incoming: Price, smoothing: FixedU128) -> Option<Price> {
    let (exp_smoothing, exp_complement) = exp_smoothing_and_complement(smoothing, iterations);
    price_ema(prev, exp_complement, incoming, exp_smoothing)
}

/// Calculate the iterated exponential moving average for the given balances.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_balance_ema(
    iterations: u32,
    prev: Balance,
    incoming: Balance,
    smoothing: FixedU128,
) -> Option<Balance> {
    let (exp_smoothing, exp_complement) = exp_smoothing_and_complement(smoothing, iterations);
    balance_ema(prev, exp_complement, incoming, exp_smoothing)
}

/// Calculate the iterated exponential moving average for the given volumes.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_volume_ema(
    iterations: u32,
    prev: (Balance, Balance, Balance, Balance),
    incoming: (Balance, Balance, Balance, Balance),
    smoothing: FixedU128,
) -> Option<(Balance, Balance, Balance, Balance)> {
    let (exp_smoothing, exp_complement) = exp_smoothing_and_complement(smoothing, iterations);
    volume_ema(prev, exp_complement, incoming, exp_smoothing)
}

/// Calculate the smoothing factor and its complement for a given combination of period and
/// iterations.
pub fn exp_smoothing_and_complement(smoothing: FixedU128, iterations: u32) -> (FixedU128, FixedU128) {
    debug_assert!(smoothing <= Price::one());
    let complement = Price::one() - smoothing;
    // in order to determine the iterated smoothing factor we exponentiate the complement
    let exp_complement = complement.saturating_pow(iterations as usize);
    debug_assert!(exp_complement <= Price::one());
    let exp_smoothing = Price::one() - exp_complement;
    (exp_smoothing, exp_complement)
}

/// Calculates smoothing factor alpha for an exponential moving average based on `period`:
/// `alpha = 2 / (period + 1)`. It leads to the "center of mass" of the EMA corresponding to be the
/// "center of mass" of a `period`-length SMA.
///
/// Possible alternatives for `alpha = 2 / (period + 1)`:
/// + `alpha = 1 - 0.5^(1 / period)` for a half-life of `period` or
/// + `alpha = 1 - 0.5^(2 / period)` to have the same median as a `period`-length SMA. See
/// https://en.wikipedia.org/wiki/Moving_average#Relationship_between_SMA_and_EMA (N = period).
pub fn smoothing_from_period(period: u64) -> FixedU128 {
    FixedU128::saturating_from_rational(2u64, period.max(1).saturating_add(1))
}

/// Calculate the next exponential moving average for the given prices.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
pub fn price_ema(prev: Price, prev_weight: FixedU128, incoming: Price, weight: FixedU128) -> Option<Price> {
    debug_assert!(prev_weight + weight == Price::one());
    // Safe to use bare `+` because `prev_weight + weight == 1`.
    // `prev_value * prev_weight + incoming_value * weight`
    let price = prev.checked_mul(&prev_weight)? + incoming.checked_mul(&weight)?;
    Some(price)
}

/// Calculate the next exponential moving average for the given balances.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `weight` is the weight of the new value, `prev_weight` is the weight of the previous value.
pub fn balance_ema(prev: Balance, prev_weight: FixedU128, incoming: Balance, weight: FixedU128) -> Option<Balance> {
    debug_assert!(prev_weight + weight == Price::one());
    // Safe to use bare `+` because `prev_weight + apha == 1`.
    // `prev_value * prev_weight + incoming_value * weight`
    let new_value = if prev < Balance::from(u64::MAX) && incoming < Balance::from(u64::MAX) {
        // We use `checked_mul` in combination with `Price::from` to avoid rounding errors induced
        // by using `checked_mul_int` with small values.
        (prev_weight.checked_mul(&Price::from(prev))? + weight.checked_mul(&Price::from(incoming))?)
            .saturating_mul_int(Balance::one())
    } else {
        // We use `checked_mul_int` to avoid saturating the fixed point type for big balance values.
        // Note: Incurs rounding errors for small balance values, but the relative error is small
        // because the other value is greater than `u64::MAX`.
        prev_weight.checked_mul_int(prev)? + weight.checked_mul_int(incoming)?
    };
    Some(new_value)
}

/// Calculate the next exponential moving average for the given volumes.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `weight` is the weight of the new value, `prev_weight` is the weight of the previous value.
///
/// Note: Just delegates to `balance_ema` under the hood.
pub fn volume_ema(
    prev: (Balance, Balance, Balance, Balance),
    prev_weight: FixedU128,
    incoming: (Balance, Balance, Balance, Balance),
    weight: FixedU128,
) -> Option<(Balance, Balance, Balance, Balance)> {
    debug_assert!(prev_weight + weight == Price::one());
    let (prev_a_in, prev_b_out, prev_a_out, prev_b_in) = prev;
    let (a_in, b_out, a_out, b_in) = incoming;
    let volume = (
        balance_ema(prev_a_in, prev_weight, a_in, weight)?,
        balance_ema(prev_b_out, prev_weight, b_out, weight)?,
        balance_ema(prev_a_out, prev_weight, a_out, weight)?,
        balance_ema(prev_b_in, prev_weight, b_in, weight)?,
    );
    Some(volume)
}
