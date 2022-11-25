use fixed::types::U89F39 as F;
use sp_arithmetic::FixedU128;

pub type Balance = u128;
pub type Price = FixedU128;
pub type Fraction = fixed::types::U1F127;
pub type FixedBalance = F;
pub type LBPWeight = u32;
pub const HYDRA_ONE: u128 = 1_000_000_000_000u128;
pub const BASILISK_ONE: u128 = 1_000_000_000_000u128;

pub mod fraction {
    use super::{Balance, FixedU128, Fraction};
    use num_traits::One;
    use sp_arithmetic::helpers_128bit::{gcd, multiply_by_rational_with_rounding};
    use sp_arithmetic::per_things::Rounding;
    use sp_arithmetic::{FixedPointNumber, Rational128};

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
    pub fn to_fixed(f: Fraction) -> FixedU128 {
        FixedU128::from_inner(
            multiply_by_rational_with_rounding(FixedU128::DIV, f.to_bits(), DIV, Rounding::NearestPrefDown)
                .expect("f.to_bits() <= DIV, therefore the result must fit in u128; qed"),
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

    pub fn to_rational(f: Fraction) -> Rational128 {
        Rational128::from(f.to_bits(), DIV)
    }

    pub fn multiply_by_balance(f: Fraction, b: Balance) -> Balance {
        debug_assert!(f <= Fraction::ONE);
        multiply_by_rational_with_rounding(b, f.to_bits(), DIV, Rounding::NearestPrefDown)
            .expect("f.to_bits() <= DIV, therefore the result must fit in u128; qed")
    }

    pub fn multiply_by_fixed(fraction: Fraction, fixed: FixedU128) -> FixedU128 {
        debug_assert!(fraction <= Fraction::ONE);
        FixedU128::from_inner(
            multiply_by_rational_with_rounding(fixed.into_inner(), fraction.to_bits(), DIV, Rounding::NearestPrefDown)
                .expect("f.to_bits() <= DIV, therefore the result must fit in u128; qed"),
        )
    }

    fn simplify(r: Rational128) -> Rational128 {
        let g = gcd(r.n(), r.d());
        Rational128::from(r.n() / g, r.d() / g)
    }

    pub fn multiply_by_rational(f: Fraction, r: Rational128) -> Rational128 {
        debug_assert!(f <= Fraction::ONE);
        // amplify both numerator and denominator of the rational number to make multiplication more
        // accurate
        let amplifier = (u128::MAX / r.d()).min(u128::MAX / r.n());
        let n = multiply_by_rational_with_rounding(r.n() * amplifier, f.to_bits(), DIV, Rounding::NearestPrefDown)
            .expect("f.to_bits() <= DIV, therefore the result must fit in u128; qed");
        simplify(Rational128::from(n, r.d() * amplifier))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fraction::*;

    use num_traits::One;
    use sp_arithmetic::{FixedPointNumber, Rational128};

    use rug::Rational;

    macro_rules! assert_rational_approx_eq {
        ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
            let diff = if $x >= $y { $x - $y } else { $y - $x };
            assert!(
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

    fn to_tuple(r: Rational128) -> (u128, u128) {
        (r.n(), r.d())
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

        let f = fraction::frac(1, 9 << 124);
        let r = rat(9, 10);
        let expected = Rational::from((1, (1_u128 << 124) * 10));
        let res = multiply_by_rational(f, r);
        assert_rational_approx_eq!(
            Rational::from((res.n(), res.d())),
            expected.clone(),
            Rational::from((1, fraction::DIV)),
            "not approximately equal!"
        );
    }
}
