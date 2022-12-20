use crate::to_u128_wrapper;

use primitive_types::{U128, U256};
use sp_arithmetic::Rational128;

/// Enum to specify how to round a rational number.
/// `Minimal` rounds both numerator and denominator down.
/// `Down` ensures the output is less than or equal to the input.
/// `Up` ensures the output is greater than or equal to the input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rounding {
    Minimal,
    Down,
    Up,
}

impl Rounding {
    pub fn to_bias(self, magnitude: u128) -> (u128, u128) {
        match self {
            Rounding::Minimal => (0, 0),
            Rounding::Down => (0, magnitude),
            Rounding::Up => (magnitude, 0),
        }
    }
}

/// Rounds a rational number of `(U256, U256)` to a `Rational128`.
/// The rounding is done by shifting which implicitly rounds down both numerator and denominator.
/// Specify `rounding` other than `Minimal` to round the whole number up or down.
/// Specifying `min_n` and `min_d` greater than zero will ensure that neither go to zero
/// (compensating for rounding down).
pub fn round_to_rational((n, d): (U256, U256), (min_n, min_d): (u128, u128), rounding: Rounding) -> Rational128 {
    let shift = n.bits().max(d.bits()).saturating_sub(128);
    let (n, d) = if shift > 0 {
        let (bias_n, bias_d) = rounding.to_bias(1);
        let shifted_n = (n >> shift).low_u128();
        let shifted_d = (d >> shift).low_u128();
        (
            shifted_n.saturating_add(bias_n).max(min_n),
            shifted_d.saturating_add(bias_d).max(min_d),
        )
    } else {
        (n.low_u128(), d.low_u128())
    };
    Rational128::from(n, d)
}

/// Adds two rational numbers, rounding the result to make sure it fits in a `Rational128`.
/// Ensures the resulting numerator and denominator are greater than zero.
pub fn rounding_add(l: Rational128, r: Rational128, rounding: Rounding) -> Rational128 {
    dbg!("rounding_add");
    if l.n() == 0 {
        return r;
    } else if r.n() == 0 {
        return l;
    }
    dbg!(l.n(), l.d(), r.n(), r.d());
    let (l_n, l_d, r_n, r_d) = to_u128_wrapper!(l.n(), l.d(), r.n(), r.d());
    // n = l.n * r.d + r.n * l.d
    let n = l_n.full_mul(r_d).saturating_add(r_n.full_mul(l_d));
    // d = l.d * r.d
    let d = U128::from(l_d).full_mul(r_d);
    dbg!(n, d);
    let res = round_to_rational((n, d), (1, 1), rounding);
    dbg!(res.n(), res.d());
    res
}

/// Subtracts `r` from `l`, rounding the result to make sure it fits in a `Rational128`.
/// Ensures the resulting denominator is greater than zero and that the denominator is greater than
/// zero if the subtraction did not saturate.
pub fn rounding_sub(l: Rational128, r: Rational128, rounding: Rounding) -> Rational128 {
    dbg!("rounding_sub");
    if l.n() == 0 || r.n() == 0 {
        return l;
    }
    dbg!(l.n(), l.d(), r.n(), r.d());
    let (l_n, l_d, r_n, r_d) = to_u128_wrapper!(l.n(), l.d(), r.n(), r.d());
    // n = l.n * r.d - r.n * l.d
    let n = l_n.full_mul(r_d).saturating_sub(r_n.full_mul(l_d));
    // d = l.d * r.d
    let d = U128::from(l.d()).full_mul(r.d().into());
    dbg!(n, d);
    // only round up the numerator if it was not zero
    let min_n = if n.is_zero() { 0 } else { 1 };
    let res = round_to_rational((n, d), (min_n, 1), rounding);
    dbg!(res.n(), res.d());
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::{any_rational, bigger_and_smaller_rational};
    use crate::test_utils::{prop_assert_rational_relative_approx_eq, rational_to_high_precision, rational_to_tuple};
    use crate::test_utils::{MAX_BALANCE, MIN_BALANCE};
    use Rounding::*;

    use proptest::prelude::*;
    use rug::Rational;

    #[test]
    fn round_to_rational_should_work() {
        let res = round_to_rational((U256::from(1), U256::from(1)), (1, 1), Minimal);
        let expected = Rational128::from(1, 1);
        assert_eq!(
            res,
            expected,
            "actual: {:?}, expected: {:?}",
            rational_to_tuple(res),
            rational_to_tuple(expected)
        );

        let res = round_to_rational((U256::MAX, U256::MAX), (1, 1), Minimal);
        let expected = Rational128::from(u128::MAX, u128::MAX);
        assert_eq!(
            res,
            expected,
            "actual: {:?}, expected: {:?}",
            rational_to_tuple(res),
            rational_to_tuple(expected)
        );

        let res = round_to_rational((U256::MAX, U256::from(1)), (1, 1), Minimal);
        let expected = Rational128::from(u128::MAX, 1);
        assert_eq!(
            res,
            expected,
            "actual: {:?}, expected: {:?}",
            rational_to_tuple(res),
            rational_to_tuple(expected)
        );

        let res = round_to_rational((U256::from(1), U256::MAX), (1, 1), Minimal);
        let expected = Rational128::from(1, u128::MAX);
        assert_eq!(
            res,
            expected,
            "actual: {:?}, expected: {:?}",
            rational_to_tuple(res),
            rational_to_tuple(expected)
        );

        let d = 323853616005226055489000679651893043332_u128;
        let res = round_to_rational(
            (
                U256::from_dec_str("34599284998074995708396179719034205723253966454380752564716172454912477882716")
                    .unwrap(),
                U256::from(d),
            ),
            (1, 1),
            Down,
        );
        let boundary = Rational::from_str_radix(
            "34599284998074995708396179719034205723253966454380752564716172454912477882716",
            10,
        )
        .unwrap()
            / d;
        assert!(rational_to_high_precision(res) <= boundary);
    }

    /// The maximum balance value for the precision tests.
    const MAX_VAL: u128 = MAX_BALANCE * 1000;

    fn typical_balance() -> impl Strategy<Value = u128> {
        MIN_BALANCE..MAX_VAL
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn rational_rounding_add_should_have_high_enough_precision(
            (a, b) in (typical_balance(), typical_balance()),
            (c, d) in (typical_balance(), typical_balance()),
        ) {
            let res = rounding_add(Rational128::from(a, b), Rational128::from(c, d), Minimal);
            let expected = Rational::from((a, b)) + Rational::from((c, d));

            let res = rational_to_high_precision(res);
            // make sure the result has a precision of 100 bits
            let tolerance = Rational::from((1, 1u128 << 100));
            prop_assert_rational_relative_approx_eq!(res, expected, tolerance);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn rational_rounding_sub_should_have_high_enough_precision(
            ((a, b), (c, d)) in bigger_and_smaller_rational(MIN_BALANCE, MAX_VAL),
        ) {
            let res = rounding_sub(Rational128::from(a, b), Rational128::from(c, d), Down);
            let expected = Rational::from((a, b)) - Rational::from((c, d));

            let res = rational_to_high_precision(res);
            // make sure the result has a precision of 77 bits
            let tolerance = Rational::from((1, 1u128 << 77));
            prop_assert_rational_relative_approx_eq!(res, expected, tolerance);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn rational_rounding_sub_result_should_be_smaller_or_equal_to_input(
            (a, b) in any_rational().prop_map(|r| (r.n(), r.d())),
            (c, d) in any_rational().prop_map(|r| (r.n(), r.d())),
        ) {
            let res = rounding_sub(Rational128::from(a, b), Rational128::from(c, d), Down);
            prop_assert!(res <= Rational128::from(a, b));
        }
    }
}
