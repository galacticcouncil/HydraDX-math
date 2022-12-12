use crate::to_u128_wrapper;

use primitive_types::{U128, U256};
use sp_arithmetic::Rational128;

/// Rounds a rational number of `(U256, U256)` to a `Rational128`.
/// The rounding is done by shifting which implicitly rounds down.
/// Specifying `min_n` and `min_d` greater than zero will ensure that neither go to zero
/// (compensating for rounding down).
pub fn round_to_rational((n, d): (U256, U256), (min_n, min_d): (u128, u128)) -> Rational128 {
    let shift = n.bits().max(d.bits()).saturating_sub(128);
    let n = (n >> shift).low_u128().max(min_n);
    let d = (d >> shift).low_u128().max(min_d);
    Rational128::from(n, d)
}

/// Adds two rational numbers, rounding the result to make sure it fits in a `Rational128`.
/// Ensures the resulting numerator and denominator are greater than zero.
pub fn rounding_add(l: Rational128, r: Rational128) -> Rational128 {
    let (l_n, l_d, r_n, r_d) = to_u128_wrapper!(l.n(), l.d(), r.n(), r.d());
    // n = l.n * r.d + r.n * l.d
    let n = l_n.full_mul(r_d).saturating_add(r_n.full_mul(l_d));
    // d = l.d * r.d
    let d = U128::from(l_d).full_mul(r_d);
    round_to_rational((n, d), (1, 1))
}

/// Subtracts `r` from `l`, rounding the result to make sure it fits in a `Rational128`.
/// Ensures the resulting denominator is greater than zero and that the denominator is greater than
/// zero if the subtraction did not saturate.
pub fn rounding_sub(l: Rational128, r: Rational128) -> Rational128 {
    let (l_n, l_d, r_n, r_d) = to_u128_wrapper!(l.n(), l.d(), r.n(), r.d());
    // n = l.n * r.d + r.n * l.d
    let n = l_n.full_mul(r_d).saturating_sub(r_n.full_mul(l_d));
    // d = l.d * r.d
    let d = U128::from(l.d()).full_mul(r.d().into());
    // only round up the numerator if it was not zero
    let min_n = if n.is_zero() { 0 } else { 1 };
    round_to_rational((n, d), (min_n, 1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::bigger_and_smaller_rational;
    use crate::test_utils::rational_to_arbitrary_precision;
    use crate::test_utils::{MAX_BALANCE, MIN_BALANCE};

    use proptest::prelude::*;
    use rug::Rational;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn rational_rounding_add(
            (a, b) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
            (c, d) in (MIN_BALANCE..MAX_BALANCE, MIN_BALANCE..MAX_BALANCE),
        ) {
            let price1 = Rational128::from(a, b);
            let price2 = Rational128::from(c, d);

            let res = rounding_add(price1, price2);
            let expected = Rational::from((a, b)) + Rational::from((c, d));

            let res = rational_to_arbitrary_precision(res);
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

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn rational_rounding_sub(
            ((a, b), (c, d)) in bigger_and_smaller_rational()
        ) {
            let res = rounding_sub(Rational128::from(a, b), Rational128::from(c, d));
            let expected = Rational::from((a, b)) - Rational::from((c, d));

            let res = rational_to_arbitrary_precision(res);
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
}
