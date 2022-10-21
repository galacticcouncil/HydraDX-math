use crate::types::{Balance, Price};

use sp_arithmetic::{
    traits::{One, Saturating},
    FixedPointNumber, FixedU128,
};

/// Calculate the iterated exponential moving average for the given prices.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_price_ema(iterations: u32, prev: Price, incoming: Price, smoothing: FixedU128) -> Price {
    price_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
}

/// Calculate the iterated exponential moving average for the given balances.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_balance_ema(iterations: u32, prev: Balance, incoming: Balance, smoothing: FixedU128) -> Balance {
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
    smoothing: FixedU128,
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
/// # use sp_arithmetic::FixedU128;
/// assert_eq!(exp_smoothing(FixedU128::from_float(0.6), 2), FixedU128::from_float(0.84));
/// ```
pub fn exp_smoothing(smoothing: FixedU128, iterations: u32) -> FixedU128 {
    debug_assert!(smoothing <= FixedU128::one());
    let complement = FixedU128::one() - smoothing;
    // in order to determine the iterated smoothing factor we exponentiate the complement
    let exp_complement = complement.saturating_pow(iterations as usize);
    debug_assert!(exp_complement <= FixedU128::one());
    FixedU128::one() - exp_complement
}

/// Calculates smoothing factor alpha for an exponential moving average based on `period`:
/// `alpha = 2 / (period + 1)`. It leads to the "center of mass" of the EMA corresponding to be the
/// "center of mass" of a `period`-length SMA.
///
/// Possible alternatives for `alpha = 2 / (period + 1)`:
/// + `alpha = 1 - 0.5^(1 / period)` for a half-life of `period` or
/// + `alpha = 1 - 0.5^(2 / period)` to have the same median as a `period`-length SMA.
/// See https://en.wikipedia.org/wiki/Moving_average#Relationship_between_SMA_and_EMA
pub fn smoothing_from_period(period: u64) -> FixedU128 {
    FixedU128::saturating_from_rational(2u64, period.max(1).saturating_add(1))
}

/// Calculate a weighted average for the given prices.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `weight` is how much weight to give the new value.
///
/// Note: Rounding is slightly biased towards `prev`.
/// (`FixedU128::mul` rounds to the nearest representable value, rounding down on equidistance.
/// See [doc comment here](https://github.com/paritytech/substrate/blob/ce10b9f29353e89fc3e59d447041bb29622def3f/primitives/arithmetic/src/fixed_point.rs#L670-L671).)
pub fn price_weighted_average(prev: Price, incoming: Price, weight: FixedU128) -> Price {
    debug_assert!(weight <= FixedU128::one(), "weight must be <= 1");
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
pub fn balance_weighted_average(prev: Balance, incoming: Balance, weight: FixedU128) -> Balance {
    debug_assert!(weight <= FixedU128::one(), "weight must be <= 1");
    if incoming >= prev {
        // Safe to use bare `+` because `weight <= 1` and `a + (b - a) <= b`.
        // Safe to use bare `-` because of the conditional.
        prev + weight.saturating_mul_int(incoming - prev)
    } else {
        // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
        prev - weight.saturating_mul_int(prev - incoming)
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
    weight: FixedU128,
) -> (Balance, Balance, Balance, Balance) {
    debug_assert!(weight <= FixedU128::one(), "weight must be <= 1");
    let (prev_a_in, prev_b_out, prev_a_out, prev_b_in) = prev;
    let (a_in, b_out, a_out, b_in) = incoming;
    (
        balance_weighted_average(prev_a_in, a_in, weight),
        balance_weighted_average(prev_b_out, b_out, weight),
        balance_weighted_average(prev_a_out, a_out, weight),
        balance_weighted_average(prev_b_in, b_in, weight),
    )
}

#[cfg(test)]
pub(crate) mod high_precision {
    use super::*;

    use num_traits::Pow;
    use rug::ops::DivRounding;
    use rug::{Integer, Rational};
    use std::ops::Mul;

    /// Convert a fixed point number to an arbitrary precision rational number.
    pub fn fixed_to_rational(f: FixedU128) -> Rational {
        Rational::from((f.into_inner(), FixedU128::DIV))
    }

    /// Convert a `Rational` number into its rounded down `Integer` equivalent.
    pub fn into_rounded_integer(r: Rational) -> Integer {
        let (num, den) = r.into_numer_denom();
        num.div_floor(den)
    }

    pub fn rug_exp_smoothing(smoothing: FixedU128, iterations: u32) -> Rational {
        debug_assert!(smoothing <= FixedU128::one());
        let complement = Rational::one() - fixed_to_rational(smoothing);
        // in order to determine the iterated smoothing factor we exponentiate the complement
        let exp_complement = complement.pow(iterations);
        debug_assert!(exp_complement <= Rational::one());
        Rational::one() - exp_complement
    }

    /// Calculate the weighted average for the given balances by using arbitrary precision math.
    ///
    /// Note: Rounding is biased towards `prev`.
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
    pub fn rug_balance_ema(history: Vec<Balance>, smoothing: FixedU128) -> Integer {
        assert!(!history.is_empty());
        let smoothing = fixed_to_rational(smoothing);
        let mut current = Rational::from(history[0]);
        for balance in history.into_iter().skip(1) {
            current = rug_weighted_average(current.clone(), balance.into(), smoothing.clone());
        }
        // return rounded down integer
        into_rounded_integer(current)
    }

    /// Determine the exponential moving average of a history of price values.
    /// Starts the EMA with the first value.
    /// Returns an arbitrary precision `Rational` number.
    pub fn rug_price_ema(history: Vec<Price>, smoothing: FixedU128) -> Rational {
        assert!(!history.is_empty());
        let smoothing = fixed_to_rational(smoothing);
        let mut current = fixed_to_rational(history[0]);
        for price in history.into_iter().skip(1) {
            current = rug_weighted_average(current.clone(), fixed_to_rational(price), smoothing.clone());
        }
        current
    }
}
