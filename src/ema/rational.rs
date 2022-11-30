use crate::transcendental::saturating_powi_high_precision;
use crate::types::fraction;
use crate::types::{Balance, Fraction};

use sp_arithmetic::{Rational128, traits::One};

pub type Price = Rational128;

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

pub use super::math::smoothing_from_period;

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
        rounding_add(prev, fraction::multiply_by_rational(weight, rounding_sub(incoming, prev)))
    } else {
        // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
        rounding_sub(prev, fraction::multiply_by_rational(weight, rounding_sub(prev, incoming)))
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

use crate::to_u256;
use primitive_types::U256;
// use crate::types::fraction::simplify;

fn euclid_gcd(mut a: U256, mut b: U256) -> U256{
    let delta = U256::from(((a.bits().min(b.bits()) * 4) as u32).next_power_of_two()).min(a).min(b);
    // let delta = U256::from(((a.bits().min(b.bits())) as u32)).min(a).min(b);
    // dbg!(delta);
    let mut temp = a;
    while a.div_mod(b).1 > delta {
      temp = a.div_mod(b).1;
      a = b;
      b = temp;
    }
    return b;
  }

fn gcd(a: U256, b: U256) -> U256 {
    use core::cmp::{min, max};
	match ((a, b), (a & U256::one(), b & U256::one())) {
		((x, y), _) if x == y => y,
		((a, x), _) | ((x, a), _) if a == U256::zero() => x,
		((x, y), t) if t == (U256::zero(), U256::one()) => gcd(x >> U256::one(), y),
        ((y, x), t) if t == (U256::one(), U256::zero()) => gcd(x >> U256::one(), y),
		((x, y), t) if t == (U256::zero(), U256::zero()) => gcd(x >> U256::one(), y >> U256::one()) << U256::one(),
		((x, y), t) if t == (U256::one(), U256::one()) => {
			let (x, y) = (min(x, y), max(x, y));
			gcd((y - x) >> U256::one(), x)
		},
		_ => unreachable!(),
	}
}

pub fn rounding_add(l: Rational128, r: Rational128) -> Rational128 {
    // let (l, r) = (simplify(l), simplify(r));
    let (l_n, l_d, r_n, r_d) = to_u256!(l.n(), l.d(), r.n(), r.d());
    let d = l_d * r_d;
    let n = (l_n * r_d).saturating_add(r_n * l_d);
    let g = euclid_gcd(n, d);
    if g < 1_000_u32.into() { println!("gcd: {}", g); }
    let n = n / g;
    let d = d / g;
    let shift = n.bits().max(d.bits()).saturating_sub(128);
    if shift > 0 { println!("shift: {}", shift); }
    Rational128::from((n >> shift).low_u128(), (d >> shift).low_u128())
}

pub fn rounding_sub(l: Rational128, r: Rational128) -> Rational128 {
    // let (l, r) = (simplify(l), simplify(r));
    let (l_n, l_d, r_n, r_d) = to_u256!(l.n(), l.d(), r.n(), r.d());
    let d = l_d * r_d;
    let n = (l_n * r_d).saturating_sub(r_n * l_d);
    let g = euclid_gcd(n, d);
    if g < 1_000_u32.into() { println!("gcd: {}", g); }
    let n = n / g;
    let d = d / g;
    let shift = n.bits().max(d.bits()).saturating_sub(128);
    if shift > 0 { println!("shift: {}", shift); }
    Rational128::from((n >> shift).low_u128(), (d >> shift).low_u128())
}


