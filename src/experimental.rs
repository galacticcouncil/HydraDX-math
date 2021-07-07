/// Implementation of division, multiplication and pow functionality using only integer
/// arithmetic and respecting Hydra's token precision of 12 decimals.
pub mod experimental {

    use core::convert::From;
    use fixed::traits::*;
    use fixed::types::extra::U12;
    use fixed::types::{U64F64, U75F53 as F};
    use fixed::FixedU128;
    use std::ops::{AddAssign, BitOrAssign, ShlAssign};

    const PRECISION: u128 = 1_000_000_000_000u128;

    /// power with integer exponent
    pub fn powi<S, D>(operand: S, exponent: u32) -> Result<D, ()>
    where
        S: Fixed,
        D: Fixed + From<S>,
    {
        if operand == S::from_num(0) {
            return Ok(D::from_num(0));
        };
        if exponent == 0 {
            return Ok(D::from_num(1));
        };
        if exponent == 1 {
            return Ok(D::from(operand));
        };
        let operand = D::from(operand);
        let mut r = operand;

        for _idx in 1..exponent {
            r = if let Some(r) = r.checked_mul(operand) {
                r
            } else {
                return Err(());
            };
        }
        Ok(r)
    }

    /// power with integer exponent
    pub fn pow<S, D>(operand: S, exponent: S) -> Result<D, ()>
    where
        S: Fixed,
        D: Fixed + From<S>,
    {
        let whole = exponent.int();
        let frac = exponent.frac();

        let r = powi::<S, D>(operand, whole.to_num())?;

        if frac.is_zero() {
            return Ok(r);
        }
        let partial_result = pow_approx::<S, D>(operand, frac)?;

        r.checked_mul(partial_result).ok_or(())
    }

    fn sub_sign<S>(a: S, b: S) -> (S, bool)
    where
        S: Fixed,
    {
        if a >= b {
            (a - b, false)
        } else {
            (b - a, true)
        }
    }

    fn pow_approx<S, D>(operand: S, exponent: S) -> Result<D, ()>
    where
        S: Fixed,
        D: Fixed + From<S>,
    {
        let precision = S::from_fixed(S::from_num(100_000_000_u128) / S::from_num(1_000_000_000_000_u128));
        let zero = S::from_num(0);
        let one = S::from_num(1);

        let ONE = one;

        let a = exponent;
        let (x, xneg) = sub_sign(operand, ONE);
        let mut term = ONE;
        let mut sum = term;
        let mut negative = false;

        let mut idx: S = one;

        while term >= precision {
            let big_k: S = idx * ONE;
            let (c, cneg) = sub_sign(a, big_k.checked_sub(ONE).ok_or(())?);

            term = term.checked_mul(c.checked_mul(x).ok_or(())?).ok_or(())?;
            term = term.checked_div(big_k).ok_or(())?;

            if term == zero {
                break;
            }
            if xneg {
                negative = !negative;
            }
            if cneg {
                negative = !negative;
            }

            if negative {
                sum = sum.checked_sub(term).ok_or(())?;
            } else {
                sum = sum.checked_add(term).ok_or(())?;
            }
            idx = idx.checked_add(one).ok_or(())?;
        }

        Ok(D::from(sum))
    }

    #[test]
    fn powi_works() {
        type S = U64F64;
        type D = U64F64;

        assert_eq!(powi(S::from_num(2), 2), Ok(D::from_num(4)));
    }

    #[test]
    fn pow_works() {
        type S = U64F64;
        type D = U64F64;

        assert_eq!(pow(S::from_num(22.1234), S::from_num(2.1)), Ok(D::from_num(4)));
    }
}
