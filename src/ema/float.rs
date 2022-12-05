use crate::transcendental::saturating_powi_high_precision;
use crate::types::fraction;
use crate::types::{Balance, Fraction};

use sp_arithmetic::traits::One;

use sp_arithmetic::FixedU128;
use sp_arithmetic::helpers_128bit::multiply_by_rational_with_rounding;
use sp_arithmetic::per_things::Rounding;
use primitive_types::{U128, U256};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Float128 {
    pub scale: i8,
    pub mantissa: u128,
}

fn bits(n: u128) -> u32 {
    u128::BITS - n.leading_zeros()
}

fn into_neg_i8(n: u32) -> i8 {
    debug_assert!(n <= i8::MAX as u32);
    // i8 cannot represent 128 so we take the route via i16
    (-((n).min(128) as i16)) as i8
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
        match self.scale {
            0..=i8::MAX => self.mantissa << self.scale,
            i8::MIN..=-1 => self.mantissa >> -(self.scale as i16),
        }
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
        dbg!(next_power);
        if d == next_power {
            return Self {
                scale: into_neg_i8(bits(d) - 1),
                mantissa: n,
            }
        }
        // in order to get higher resolution for fractions like `1/3` we amplify the mantissa so that
        // it contains more bits
        let amp = n.leading_zeros().min(d.leading_zeros());
        let scale = bits(next_power / 2).saturating_sub(1);
        debug_assert!((1 << scale) <= d);
        let mantissa = multiply_by_rational_with_rounding(n << amp, 1 << scale, d, Rounding::NearestPrefDown)
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
        dbg!(self, other);
        // multiplication of the mantissas is straight forward, we just make sure to have enough
        // bits to actually represent the result
        let mut mantissa = U128::from(self.mantissa).full_mul(other.mantissa.into());
        // same for the scale: let's make sure there are enough bits
        let mut scale = self.scale as i16 + (other.scale as i16);
        dbg!(scale);
        if scale > 127 {
            // adjust the mantissa in case the scale overflows
            mantissa = mantissa.saturating_mul((1_u128 << scale.saturating_sub(127)).into());
            scale = 127;
        } else if scale < -128 {
            // adjust the mantissa in case the scale underflows
            mantissa = mantissa / (1 << -(scale.saturating_add(128)));
            scale = -128;
        }
        debug_assert!(scale <= (i8::MAX as i16) && scale >= (i8::MIN as i16), "scale must fit in i8");
        // convert scale to the final type
        let mut scale = scale as i8;
        // we want to convert the mantissa back to u128, so let's make sure it fits
        let shift = 128_u32.saturating_sub(mantissa.leading_zeros());
        mantissa >>= shift;
        // here is where we saturate if we cannot fit the extra scale
        scale = scale.saturating_add(shift.min(127) as i8);
        let mantissa = mantissa.as_u128();
        Self {
            scale, mantissa,
        }
    }

    // pub fn saturating_sub(self, other: Self) -> Self {
    //     let mantissa = match (self.scale, other.scale) {
    //         (s, o) if s == o => self.mantissa.saturating_sub(other.mantissa),
    //         (s, o) if s > o => self.mantissa.saturating_sub(other.mantissa << self.scale - other.scale)
    //     }
    //     let mantissa = self.mantissa.checked_sub(other.mantissa).unwrap_or(0);
    //     Self {
    //         scale,
    //         mantissa,
    //     }
    // }
}

// pub type Price = Float128;

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
    fn from_rational_works() {
        assert_eq!(Float128::from_rational(1, 8), Float128::new(-3, 1));
    }

    #[test]
    fn mul_works() {
        assert_eq!(Float128::one().saturating_mul(Float128::one()), Float128::one());

        assert!(Float128::from_rational(1, 8).saturating_mul(Float128::from_int(8)).is_one());

        assert_eq!(Float128::from_rational(1, 8).saturating_mul(Float128::from_int(8)).to_int(), 1);
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
            0..=i8::MAX => Rational::from(f.mantissa) * Rational::from(1 << f.scale),
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
            let diff = if $x >= $y { $x - $y } else { $y - $x };
            prop_assert!(
                diff.clone() / $x.clone() <= $z.clone(),
                "\n{}\n    left: {:?}\n   right: {:?}\n    diff: {:?}\nmax_diff: {:?}\n",
                $r,
                $x.to_f64(),
                $y.to_f64(),
                diff.to_f64(),
                ($x * $z).to_f64()
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
        #![proptest_config(ProptestConfig::with_cases(10000))]
        #[test]
        fn has_high_enough_precision(
            (n, d) in (1..u128::MAX, 1..u128::MAX),
        ) {
            let tolerance = Rational::from((1, u128::MAX)); //1e28 as u128));
            prop_assert_rational_relative_approx_eq!(
                to_rational(Float128::from_rational(n.into(), d.into())),
                Rational::from((n, d)),
                tolerance,
                "float precision should be high enough"
            )
        }
    }
}
