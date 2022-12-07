use crate::transcendental::saturating_powi_high_precision;
use crate::types::fraction;
use crate::types::{Balance, Fraction};

use sp_arithmetic::traits::One;

use sp_arithmetic::FixedU128;
use sp_arithmetic::helpers_128bit::multiply_by_rational_with_rounding;
use sp_arithmetic::per_things::Rounding;
use primitive_types::{U128, U256};

use core::cmp::{Ord, Ordering, PartialOrd};

/// Floating point number implementation with 128 bit mantissa and 8 bit scale.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Float128 {
    pub scale: i8,
    pub mantissa: u128,
}

impl Ord for Float128 {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.scale.cmp(&other.scale) {
            Ordering::Equal => self.mantissa.cmp(&other.mantissa),
            _ => {
                let point = self.determine_u256_point(&other);
                self.to_fixed_u256(point).cmp(
                    &other.to_fixed_u256(point))
            }
        }
    }
}

impl PartialOrd for Float128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn bits(n: u128) -> u32 {
    u128::BITS - n.leading_zeros()
}

fn into_neg_i8(n: u32) -> i8 {
    debug_assert!(n <= 128);
    // i8 cannot represent 128 so we take the route via i16
    (-((n).min(128) as i16)) as i8
}

use core::ops::{Shl, Shr};

fn shift<N, S>(n: N, s: S) -> N
where N: Shl<i16, Output = N> + Shr<i16, Output = N>,
      S: Into<i16> + Copy,
{
    let s: i16 = s.into();
    match s {
        0..=i16::MAX => n << s,
        i16::MIN..=-1 => n >> -s,
    }
}

impl Float128 {
    pub fn new(scale: i8, mantissa: u128) -> Self {
        Self { scale, mantissa }
    }

    pub fn zero() -> Self {
        Self::new(0, 0)
    }

    pub fn is_zero(&self) -> bool {
        self.mantissa == 0
    }

    pub fn one() -> Self {
        Self::new(0, 1)
    }

    pub fn is_one(&self) -> bool {
        match self.scale {
            1..=i8::MAX => false,
            0 => self.mantissa == 1,
            i8::MIN..=-1 => {
                let shift = u128::BITS as i16 + self.scale as i16;
                let fractional_part = (self.mantissa << shift) >> shift;
                self.to_int() == 1 && fractional_part == 0
            }
        }
    }

    pub fn from_int(n: u128) -> Self {
        Self::new(0, n)
    }

    pub fn to_int(&self) -> u128 {
        shift(self.mantissa, self.scale)
    }

    pub fn to_f64(&self) -> f64 {
        let fractional_part = if self.scale < 0 {
            let scale = self.scale as i16;
            let shift = u128::BITS as i16 + scale;
            let fractional_part = (self.mantissa << shift) >> shift; // mask the non-fractional bits
            fractional_part as f64 / (1u128 << -(scale)) as f64
        } else {
            0.0
        };
        self.to_int() as f64 + fractional_part
    }

    pub(crate) fn determine_u256_point(&self, other: &Self) -> i16 {
        let zeros = self.mantissa.leading_zeros().min(other.mantissa.leading_zeros()) as i16;
        (128_i16 + zeros - self.scale.max(other.scale) as i16).min(255)
    }

    pub(crate) fn to_fixed_u256(&self, point: i16) -> U256 {
        let to_shift = self.scale as i16 + point;
        // debug_assert!(to_shift >= 0);
        let mantissa = U256::from(self.mantissa);
        debug_assert!(to_shift <= mantissa.leading_zeros() as i16);
        shift(mantissa, to_shift)
    }

    pub(crate) fn from_fixed_u256(mut f: U256, mut scale: i16, offset: i16) -> Self {
        f = shift(f, -offset);
        if scale > 127 {
            // adjust the mantissa in case the scale would overflow
            f = f.saturating_mul((1_u128 << scale.saturating_sub(127)).into());
            scale = 127;
        } else if scale < -128 {
            // adjust the mantissa in case the scale would underflow
            f /= 1_u128 << -scale.saturating_add(128);
            scale = -128;
        };
        debug_assert!(scale <= (i8::MAX as i16) && scale >= (i8::MIN as i16), "scale must fit in i8");
        // convert scale to the final type
        let mut scale = scale as i8;
        // we want to convert the number back to u128, so let's make sure it fits
        let shift = 128_u32.saturating_sub(f.leading_zeros());
        f >>= shift;
        // here is where we saturate if we cannot fit the extra scale
        scale = scale.saturating_add(shift.min(i8::MAX as u32) as i8);
        Self {
            scale, mantissa: f.as_u128(),
        }
    }

    pub fn from_fraction(f: Fraction) -> Self {
        Self {
            scale: -127_i8,
            mantissa: f.to_bits(),
        }
    }

    pub fn from_fixed(f: FixedU128) -> Self {
        Self {
            scale: -64_i8,
            mantissa: f.into_inner(),
        }
    }

    pub fn from_rational(n: u128, d: u128) -> Self {
        debug_assert!(d > 0, "denominator must be greater than zero");
        let next_power = d.checked_next_power_of_two().unwrap_or(u128::MAX);
        if d == next_power {
            return Self {
                scale: into_neg_i8(bits(d).saturating_sub(1)),
                mantissa: n,
            }
        }
        // in order to get higher resolution for fractions like `1/3` we amplify the mantissa so that
        // it contains more bits
        let amp = n.leading_zeros().min(d.leading_zeros());
        let scale = bits(next_power / 2).saturating_sub(1);
        debug_assert!((1 << scale) <= d);
        let mantissa = multiply_by_rational_with_rounding(n << amp, 1 << scale, d, Rounding::Up)
            .expect("(1 << scale) <= d, therefore the result must fit in u128; qed");
        Self {
            // we adjust the scale according to the amplification
            scale: into_neg_i8(scale + amp),
            mantissa,
        }
    }

    pub fn saturating_mul(self, other: Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        } else if self.is_one() {
            return other;
        } else if other.is_one() {
            return self;
        }
        // multiplication of the mantissas is straight forward, we just make sure to have enough
        // bits to actually represent the result
        let mut mantissa = U128::from(self.mantissa).full_mul(other.mantissa.into());
        // same for the scale: let's make sure there are enough bits
        let mut scale = self.scale as i16 + (other.scale as i16);
        Self::from_fixed_u256(mantissa, scale, 0)
    }

    pub fn saturating_sub(self, other: Self) -> Self {
        if self.is_zero() {
            Self::zero()
        } else if other.is_zero() {
            self
        } else if self.scale == other.scale {
            Self {
                scale: self.scale,
                mantissa: self.mantissa.saturating_sub(other.mantissa),
            }
        } else {
            let point = self.determine_u256_point(&other);
            let scale: i16 = self.scale.min(other.scale).into();
            Self::from_fixed_u256(
                self.to_fixed_u256(point).saturating_sub(other.to_fixed_u256(point)),
                scale,
                point + scale,
            )
        }
    }

    pub fn saturating_add(self, other: Self) -> Self {
        const HALF_MAX: u128 = u128::MAX / 2;
        if self.is_zero() {
            other
        } else if other.is_zero() {
            self
        } else if self.scale == other.scale && self.mantissa <= HALF_MAX && other.mantissa <= HALF_MAX {
            Self {
                scale: self.scale,
                mantissa: self.mantissa.saturating_add(other.mantissa),
            }
        } else {
            let point = self.determine_u256_point(&other);
            let scale: i16 = self.scale.min(other.scale).into();
            Self::from_fixed_u256(
                self.to_fixed_u256(point).saturating_add(other.to_fixed_u256(point)),
                scale,
                point + scale,
            )
        }
    }
}

// EMA math functions
pub type Price = Float128;

pub use super::math::{exp_smoothing, smoothing_from_period};

/// Calculate the iterated exponential moving average for the given prices.
/// `iterations` is the number of iterations of the EMA to calculate.
/// `prev` is the previous oracle value, `incoming` is the new value to integrate.
/// `smoothing` is the smoothing factor of the EMA.
pub fn iterated_price_ema(iterations: u32, prev: Price, incoming: Price, smoothing: Fraction) -> Price {
    price_weighted_average(prev, incoming, exp_smoothing(smoothing, iterations))
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
        prev.saturating_add(Float128::from_fraction(weight).saturating_mul(incoming.saturating_sub(prev)))
    } else {
        prev.saturating_sub(Float128::from_fraction(weight).saturating_mul(prev.saturating_sub(incoming)))
    }
}

// pub fn price_weighted_average(prev: Price, incoming: Price, weight: Fraction) -> Price {
//     debug_assert!(weight <= Fraction::one(), "weight must be <= 1");
//     let weight = Float128::from_fraction(weight);
//     if incoming >= prev {
//         // Safe to use bare `+` because `weight <= 1` and `a + (b - a) <= b`.
//         // Safe to use bare `-` because of the conditional.
//         rounding_add(prev, fraction::multiply_by_rational(weight, rounding_sub(incoming, prev)))
//     } else {
//         // Safe to use bare `-` because `weight <= 1` and `a - (a - b) >= 0` and the conditional.
//         rounding_sub(prev, fraction::multiply_by_rational(weight, rounding_sub(prev, incoming)))
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bits_works() {
        assert_eq!(bits(0), 0);
        assert_eq!(bits(1), 1);
        assert_eq!(bits(8), 4);
        assert_eq!(bits(u128::MAX), 128);
    }

    #[test]
    fn into_neg_i8_works() {
        assert_eq!(into_neg_i8(0), 0);
        assert_eq!(into_neg_i8(1), -1);
        assert_eq!(into_neg_i8(17), -17);
        assert_eq!(into_neg_i8(128), -128);
    }

    #[test]
    fn shift_works() {
        assert_eq!(shift(1, 1_i16), 2);
        assert_eq!(shift(8, 2_i16), 32);
        assert_eq!(shift(8, -2_i16), 2);
        assert_eq!(shift(8, -3_i16), 1);
        assert_eq!(shift(8, -4_i16), 0);
    }

    #[test]
    fn to_int_works() {
        assert_eq!(Float128::new(0, 1).to_int(), 1);

        assert_eq!(Float128::new(3, 1).to_int(), 8);

        assert_eq!(Float128::new(-1, 1).to_int(), 0);
    }

    #[test]
    fn to_f64_works() {
        assert_eq!(Float128::zero().to_f64(), 0.0);
        assert_eq!(Float128::one().to_f64(), 1.0);
        assert_eq!(Float128::new(-1, 1).to_f64(), 0.5);
        assert_eq!(Float128::from_rational(1, 3).to_f64(), 1_f64 / 3_f64);
        assert_eq!(Float128::from_rational(1, 5).to_f64(), 1_f64 / 5_f64);
        assert_eq!(Float128::from_rational(1, 8).to_f64(), 1_f64 / 8_f64);
        assert_eq!(Float128::from_rational(5, 16).to_f64(), 5_f64 / 16_f64);
        assert_eq!(Float128::new(16, u128::MAX).to_f64(), u128::MAX as f64);
    }

    #[test]
    fn to_fixed_u256_works() {
        assert_eq!(Float128::zero().to_fixed_u256(0), U256::zero());
        assert_eq!(Float128::one().to_fixed_u256(0), U256::one());
        assert_eq!(Float128::new(-1, 1).to_fixed_u256(1), U256::one());
        assert_eq!(Float128::new(-3, 1).to_fixed_u256(127), U256::from(1_u128 << 124));
        assert_eq!(Float128::new(3, 1).to_fixed_u256(127), U256::from(1_u128 << 127) * U256::from(1_u128 << 3));
        assert_eq!(Float128::from_rational(5, 16).to_fixed_u256(127), U256::from(5_u128 << 123));
        assert_eq!(Float128::new(127, u128::MAX).to_fixed_u256(0), U256::from(u128::MAX) << 127);
    }

    #[test]
    fn from_rational_works() {
        assert_eq!(Float128::from_rational(1, 8), Float128::new(-3, 1));
    }

    #[test]
    fn saturating_mul_works() {
        assert_eq!(Float128::one().saturating_mul(Float128::one()), Float128::one());

        assert!(Float128::from_rational(1, 8).saturating_mul(Float128::from_int(8)).is_one());

        assert_eq!(Float128::from_rational(1, 8).saturating_mul(Float128::from_int(8)).to_int(), 1);

        // TODO: how to make this work? numbers are equilavent but not the same in representation.
        // normalize after each computation? offer normalization function?
        // assert_eq!(Float128::from_rational(1, 8).saturating_mul(Float128::from_int(2)), Float128::from_rational(1, 4));
    }

    #[test]
    fn saturating_sub_works() {
        assert_eq!(Float128::one().saturating_sub(Float128::one()), Float128::zero());

        assert_eq!(Float128::from_int(5).saturating_sub(Float128::one()), Float128::from_int(4));

        assert_eq!(Float128::from_rational(1, 4).saturating_sub(Float128::from_rational(1, 8)), Float128::from_rational(1, 8));

        assert_eq!(Float128::one().saturating_sub(Float128::from_rational(1, 8)), Float128::from_rational(7, 8));

        assert_eq!(Float128::from_int(4).saturating_sub(Float128::from_rational(1, 4)), Float128::from_rational(15, 4));

        assert!(Float128::new(10, 1).saturating_sub(Float128::new(10, 1)).is_zero());

        assert_eq!(Float128::new(10, 1).saturating_sub(Float128::new(9, 1)), Float128::new(9, 1));

        assert_eq!(Float128::new(10, 5).saturating_sub(Float128::new(9, 5)), Float128::new(9, 5));
    }

    #[test]
    fn saturating_add_works() {
        assert_eq!(Float128::one().saturating_add(Float128::one()), Float128::from_int(2));

        assert_eq!(Float128::from_int(5).saturating_add(Float128::one()), Float128::from_int(6));

        assert_eq!(Float128::from_rational(1, 4).saturating_add(Float128::from_rational(1, 8)), Float128::from_rational(3, 8));

        assert_eq!(Float128::one().saturating_add(Float128::from_rational(1, 8)), Float128::from_rational(9, 8));

        assert_eq!(Float128::from_int(4).saturating_add(Float128::from_rational(1, 4)), Float128::from_rational(17, 4));

        assert_eq!(Float128::new(9, 5).saturating_add(Float128::new(9, 5)), Float128::new(9, 10));
    }

    #[test]
    fn test_mul_and_add_equality() {
        let num = Float128::new(10, 5);

        assert_eq!(num.saturating_add(num), num.saturating_mul(Float128::from_int(2)));
    }

}

#[cfg(test)]
mod invariants {
    use super::*;
    use proptest::prelude::*;
    
    use rug::Rational;
    use num_traits::Pow;

    fn to_rational(f: Float128) -> Rational {
        match f.scale {
            0..=i8::MAX => dbg!(Rational::from(f.mantissa)) * dbg!(Rational::from(1_u128 << f.scale)),
            i8::MIN..=-1 => Rational::from(f.mantissa) / Rational::from(2).pow(-(f.scale as i32)),
        }
    }

    #[test]
    fn to_rational_works() {
        assert_eq!(to_rational(Float128::zero()), Rational::from(0));
        assert_eq!(to_rational(Float128::one()), Rational::from(1));
        assert_eq!(to_rational(Float128::new(-1, 1)), Rational::from((1, 2)));
        assert_eq!(to_rational(Float128::from_rational(1, 8)), Rational::from((1, 8)));
        assert_eq!(to_rational(Float128::from_int(u128::MAX)), Rational::from(u128::MAX));
    }

    macro_rules! prop_assert_rational_relative_approx_eq {
        ($x:expr, $y:expr, $z:expr, $r:expr) => {{
            let diff = if $x >= $y { $x.clone() - $y.clone() } else { $y.clone() - $x.clone() };
            prop_assert!(
                diff.clone() / $y.clone() <= $z.clone(),
                "\n{}\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
                $r,
                $x,
                $y.clone(),
                diff,
                ($y * $z)
            );
        }};
    }

    macro_rules! assert_rational_relative_approx_eq {
        ($x:expr, $y:expr, $z:expr) => {{
            let diff = if $x >= $y { $x.clone() - $y.clone() } else { $y.clone() - $x.clone() };
            assert!(
                diff.clone() / $y.clone() <= $z.clone(),
                "numbers not approximately equal!\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
                $x,
                $y.clone(),
                diff,
                ($y * $z)
            );
        }};
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(100))]
        #[test]
        fn multiplication_is_reciprocative_for_powers_of_two(
            num in (1..128).prop_map(|i| 2_u128.pow(i as u32)),
        ) {
            prop_assert!(Float128::from_rational(1, num).saturating_mul(Float128::from_int(num)).is_one())
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn multiplication_invariants(
            (n, d) in (1..u128::MAX, 1..u128::MAX),
        ) {
            let f = Float128::from_rational(n, d);
            prop_assert_eq!(f.saturating_mul(Float128::one()), f);
            prop_assert_eq!(Float128::one().saturating_mul(f), f);
            prop_assert_eq!(Float128::zero().saturating_mul(f), Float128::zero());
            prop_assert_eq!(f.saturating_mul(Float128::zero()), Float128::zero());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn from_rational_has_high_enough_precision(
            (n, d) in (1..u128::MAX, 1..u128::MAX),
        ) {
            let tolerance = Rational::from((1, (1_u128 << 106)));
            prop_assert_rational_relative_approx_eq!(
                to_rational(Float128::from_rational(n, d)),
                Rational::from((n, d)),
                tolerance,
                "float precision should be high enough"
            )
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn saturating_mul_has_high_enough_precision(
            (a, b) in (1..u128::MAX, 1..u128::MAX),
            (c, d) in (1..u128::MAX, 1..u128::MAX),
        ) {
            let res = Float128::from_rational(a, b).saturating_mul(Float128::from_rational(c, d));
            let expected = Rational::from((a, b)) * Rational::from((c, d));
            let tolerance = Rational::from((1, (1_u128 << 100)));
            prop_assert_rational_relative_approx_eq!(
                to_rational(res),
                expected,
                tolerance,
                "float precision should be high enough"
            )
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn saturating_add_has_high_enough_precision(
            (a, b) in (1..u128::MAX, 1..u128::MAX),
            (c, d) in (1..u128::MAX, 1..u128::MAX),
        ) {
            let res = Float128::from_rational(a, b).saturating_add(Float128::from_rational(c, d));
            let expected = Rational::from((a, b)) + Rational::from((c, d));
            let tolerance = Rational::from((1, (1_u128 << 100)));
            prop_assert_rational_relative_approx_eq!(
                to_rational(res),
                expected,
                tolerance,
                "float precision should be high enough"
            )
        }
    }

    fn bigger_and_smaller_rational() -> impl Strategy<Value = ((u128, u128), (u128, u128))> {
        (2..u128::MAX, 1..(u128::MAX - 1)).prop_perturb(
            |(a, b), mut rng| ((a, b), (rng.gen_range(1..a), rng.gen_range(b..u128::MAX)))
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5_000))]
        #[test]
        fn saturating_sub_has_high_enough_precision(
            ((a, b), (c, d)) in bigger_and_smaller_rational()
        ) {
            let res = Float128::from_rational(a, b).saturating_sub(Float128::from_rational(c, d));
            let expected = Rational::from((a, b)) - Rational::from((c, d));
            let tolerance = Rational::from((1, (1_u128 << 100)));
            prop_assert_rational_relative_approx_eq!(
                to_rational(res),
                expected,
                tolerance,
                "float precision should be high enough"
            )
        }
    }

    proptest! {
        #[test]
        fn subtracting_number_from_itself_is_zero(
            (n, d) in (1..u128::MAX, 1..u128::MAX),
        ) {
            let f = Float128::from_rational(n, d);
            prop_assert!(f.saturating_sub(f).is_zero());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10_000))]
        #[test]
        fn ord_works_correctly(
            (a, b) in (any::<i8>(), any::<u128>()),
            (c, d) in (any::<i8>(), any::<u128>()),
        ) {
            let f1 = Float128::new(a, b);
            let f2 = Float128::new(c, d);
            let r1 = to_rational(f1);
            let r2 = to_rational(f2);
            prop_assert_eq!(f1.cmp(&f2), r1.cmp(&r2));
        }
    }
}
