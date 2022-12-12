use crate::rational::round_to_rational;
use crate::types::{Balance, Fraction};

use num_traits::One;
use primitive_types::U128;
use sp_arithmetic::helpers_128bit::multiply_by_rational_with_rounding;
use sp_arithmetic::per_things::Rounding;
use sp_arithmetic::{FixedPointNumber, FixedU128, Rational128};

/// Smallest representable value via `Fraction`.
pub const SMALLEST_NON_ZERO: Fraction = Fraction::from_bits(1);
/// Implicit numerator for numbers represented via `Fraction`.
/// Examples:
/// + `Fraction::from_num(1) == Fraction::from_bits(DIV)`
/// + `Fraction::from_num(0.1) == Fraction::from_bits(DIV / 10)`
pub const DIV: u128 = 1u128 << 127;

/// Create a fraction based on a `n`umerator and `d`enominator.
pub fn frac(n: u128, d: u128) -> Fraction {
    debug_assert!(
        d >= n,
        "fraction should be less than or equal to 1 -> denominator should be greater equal the numerator"
    );
    Fraction::from_bits(
        multiply_by_rational_with_rounding(n, DIV, d, Rounding::NearestPrefDown)
            .expect("d >= n, therefore the result must fit in u128; qed"),
    )
}

/// Convert a `Fraction` to a `FixedU128`.
///
/// Note: Loss of precision possible because `FixedU128` uses fewer bits for the fractional part.
/// Warning: Panics if `f` > 1 in debug mode, but saturates in release.
pub fn to_fixed(f: Fraction) -> FixedU128 {
    debug_assert!(f <= Fraction::ONE);
    FixedU128::from_inner(
        multiply_by_rational_with_rounding(FixedU128::DIV, f.to_bits(), DIV, Rounding::NearestPrefDown).unwrap_or(DIV),
    )
}

/// Convert a `FixedU128` <= 1 to a `Fraction`.
///
/// Warning: Panics if `f` > 1 in debug mode, but saturates in release.
pub fn from_fixed(f: FixedU128) -> Fraction {
    debug_assert!(f <= FixedU128::one(), "fraction should be less than or equal to 1");
    Fraction::from_bits(
        multiply_by_rational_with_rounding(f.into_inner(), DIV, FixedU128::DIV, Rounding::NearestPrefDown)
            .unwrap_or(DIV),
    )
}

/// Convert a `Fraction` to a `Rational128`.
pub fn to_rational(f: Fraction) -> Rational128 {
    Rational128::from(f.to_bits(), DIV)
}

/// Multiply a `Balance` by a `Fraction`.
///
/// Warning: Panics if `f` > 1 in debug mode, but saturates in release.
pub fn multiply_by_balance(f: Fraction, b: Balance) -> Balance {
    debug_assert!(f <= Fraction::ONE);
    multiply_by_rational_with_rounding(b, f.to_bits(), DIV, Rounding::NearestPrefDown).unwrap_or(DIV)
}

/// Multiply a `FixedU128` by a `Fraction`.
///
/// Warning: Panics if `f` > 1 in debug mode, but saturates in release.
pub fn multiply_by_fixed(fraction: Fraction, fixed: FixedU128) -> FixedU128 {
    debug_assert!(fraction <= Fraction::ONE);
    FixedU128::from_inner(
        multiply_by_rational_with_rounding(fixed.into_inner(), fraction.to_bits(), DIV, Rounding::NearestPrefDown)
            .unwrap_or(DIV),
    )
}

/// Multiply a `Rational128` by a `Fraction`.
/// Rounds the result to fit in a `Rational128`, ensuring denominator is greater 0 and the numerator
/// is greater 0 if the U256 representation is greater 0.
pub fn multiply_by_rational(f: Fraction, r: Rational128) -> Rational128 {
    debug_assert!(f <= Fraction::ONE);
    // n / d = l.n * f.to_bits / (l.d * DIV)
    let n = U128::from(r.n()).full_mul(f.to_bits().into());
    let d = U128::from(r.d()).full_mul(DIV.into());
    // only round up the numerator if it was not zero
    let min_n = if n.is_zero() { 0 } else { 1 };
    round_to_rational((n, d), (min_n, 1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::{any_fixed, assert_rational_approx_eq, fixed_to_arbitrary_precision, fraction_to_arbitrary_precision, prop_assert_rational_relative_approx_eq};
    use crate::test_utils::MIN_BALANCE;

    use num_traits::One;
    use proptest::prelude::*;
    use rug::Rational;
    use sp_arithmetic::{FixedPointNumber, Rational128};

    fn to_tuple(r: Rational128) -> (u128, u128) {
        (r.n(), r.d())
    }

    fn rat(n: u128, d: u128) -> Rational128 {
        Rational128::from(n, d)
    }

    #[test]
    fn fraction_representation() {
        assert_eq!(Fraction::from_num(0.25), Fraction::ONE / 4);

        let expected_smallest_non_zero = Fraction::ONE / (u128::MAX / 2);
        assert_eq!(SMALLEST_NON_ZERO, expected_smallest_non_zero);

        assert_eq!(Fraction::from_num(0.5), Fraction::from_bits(DIV / 2));

        assert_eq!(Fraction::from_num(1), Fraction::from_bits(DIV));
    }

    #[test]
    fn fraction_works() {
        let f = frac(1, 2);
        let expected = Fraction::from_bits(DIV / 2);
        assert_eq!(f, expected);

        let f = frac(1e16 as u128, 2e16 as u128);
        let expected = Fraction::from_bits(DIV / 2);
        assert_eq!(f, expected);
    }

    #[test]
    fn to_fixed_works() {
        let fraction = Fraction::one() / 100;
        let expected = FixedU128::from((1, 100));
        assert_eq!(to_fixed(fraction), expected);
    }

    #[test]
    fn from_fixed_works() {
        let fixed = FixedU128::from((1, 100));
        let expected = Fraction::one() / 100;
        assert_eq!(from_fixed(fixed), expected);
    }

    #[test]
    fn multiply_by_balance_works() {
        let frac = Fraction::from_num(0.25);
        let balance = 1e16 as Balance;
        let expected = balance / 4;
        assert_eq!(multiply_by_balance(frac, balance), expected);
    }

    #[test]
    fn multiply_by_fixed_works() {
        let frac = Fraction::from_num(0.25);
        let fixed = FixedU128::saturating_from_integer(1e16 as u64);
        let expected = fixed / FixedU128::from(4);
        assert_eq!(multiply_by_fixed(frac, fixed), expected);

        let fixed = FixedU128::from((1, 100));
        let expected = FixedU128::from((1, 400));
        assert_eq!(multiply_by_fixed(frac, fixed), expected);
    }

    #[test]
    fn multply_by_rational_works() {
        let f = Fraction::from_num(0.25);
        let r = rat(5, 100);
        let expected = rat(1, 80);
        let res = multiply_by_rational(f, r);
        assert_eq!(
            res,
            expected,
            "actual: {:?}, expected: {:?}",
            to_tuple(res),
            to_tuple(expected)
        );

        let f = frac(1, 9 << 124);
        let r = rat(9, 10);
        let expected = Rational::from((1, (1_u128 << 124) * 10));
        let res = multiply_by_rational(f, r);
        assert_rational_approx_eq!(
            Rational::from((res.n(), res.d())),
            expected.clone(),
            Rational::from((1, DIV)),
            "not approximately equal!"
        );
    }

    // ----- Property Tests

    /// Strategy to generate a typical `Fraction` value.
    fn typical_fraction() -> impl Strategy<Value = Fraction> {
        (1u128..110_000).prop_map(|n| frac(2, n.max(1).saturating_add(1)))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1_000))]
        #[test]
        fn fraction_times_fixed_precision(
            fraction in typical_fraction(),
            fixed in any_fixed(),
        ) {
            let rational = fixed_to_arbitrary_precision(fixed) * fraction_to_arbitrary_precision(fraction);
            let conversion = fixed * to_fixed(fraction);
            let conversion_distance = (rational.clone() - fixed_to_arbitrary_precision(conversion)).abs();
            let multiply = multiply_by_fixed(fraction, fixed);
            let multiply_distance = (rational.clone() - fixed_to_arbitrary_precision(multiply)).abs();
            prop_assert!(multiply_distance <= conversion_distance);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn fraction_times_rational(
            fraction in typical_fraction(),
            price in (MIN_BALANCE..u128::MAX, MIN_BALANCE..u128::MAX),
        ) {
            let price = Rational128::from(price.0, price.1);
    
            let res = multiply_by_rational(fraction, price);
            let expected = fraction_to_arbitrary_precision(fraction) * Rational::from((price.n(), price.d()));
    
            let res = Rational::from((res.n(), res.d()));
            let tolerance = Rational::from((1, 1u128 << 85));
    
            prop_assert_rational_relative_approx_eq!(res, expected, tolerance);
        }
    }
}
