/// Implementation of division, multiplication and pow functionality using only integer
/// arithmetic and respecting Hydra's token precision of 12 decimals.
pub mod p12 {
    use crate::types::Balance256;

    type Inner = Balance256;

    lazy_static! {
        static ref HYDRA_PRECISION: Inner = Inner::from(1_000_000_000_000u128);
        pub static ref ONE: Inner = *HYDRA_PRECISION;
    }

    pub fn div(num: Inner, denom: Inner) -> Option<Inner> {
        num.checked_mul(*ONE)?.checked_add(denom / 2)?.checked_div(denom)
    }

    pub fn mul(a: Inner, b: Inner) -> Option<Inner> {
        a.checked_mul(b)?.checked_add(*ONE / 2)?.checked_div(*ONE)
    }

    pub fn pow(operand: Inner, exp: Inner) -> Option<Inner> {
        const POW_PRECISION: u128 = 100_000_000_u128;
        let zero = Inner::zero();

        let whole = floor(exp);
        let remain = exp.checked_sub(whole)?;

        let whole_pow = powi(operand, toi(whole))?;

        if remain == zero {
            return Some(whole_pow);
        }

        let partial_result = pow_approx(operand, remain, Inner::from(POW_PRECISION))?;

        mul(whole_pow, partial_result)
    }

    fn toi(n: Inner) -> Inner {
        n / *ONE
    }

    fn floor(n: Inner) -> Inner {
        toi(n) * *ONE
    }

    fn powi(operand: Inner, exponent: Inner) -> Option<Inner> {
        let zero = Inner::zero();
        let two = Inner::from(2);

        let mut z = if exponent % two != zero { operand } else { *ONE };

        let mut cond = exponent / two;

        let mut a = operand;

        while cond > zero {
            a = mul(a, a)?;

            if cond % 2 != zero {
                z = mul(z, a)?;
            }

            cond = cond.checked_div(two)?;
        }

        Some(z)
    }
    fn sub_sign(a: Inner, b: Inner) -> (Inner, bool) {
        if a >= b {
            (a - b, false)
        } else {
            (b - a, true)
        }
    }

    fn pow_approx(operand: Inner, exp: Inner, precision: Inner) -> Option<Inner> {
        let zero = Inner::zero();
        let one = Inner::from(1);

        let a = exp;
        let (x, xneg) = sub_sign(operand, *ONE);
        let mut term = *ONE;
        let mut sum = term;
        let mut negative = false;

        let mut idx: Balance256 = one;

        while term >= precision {
            let big_k: Balance256 = idx * *ONE;
            let (c, cneg) = sub_sign(a, big_k.checked_sub(*ONE)?);

            term = mul(term, mul(c, x)?)?;
            term = div(term, big_k)?;

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
                sum = sum.checked_sub(term)?;
            } else {
                sum = sum.checked_add(term)?;
            }
            idx = idx.checked_add(one)?;
        }

        Some(sum)
    }

    #[test]
    fn p12_div_works() {
        let cases = vec![
            (Inner::from(100) * *ONE, Inner::from(100) * *ONE, Some(*ONE)),
            (*ONE, Inner::from(2) * *ONE, Some(*ONE / 2)),
            (
                Inner::from(200) * *ONE,
                Inner::from(400) * *ONE,
                Some(500000000000u128.into()),
            ),
            (Inner::from(200) * *ONE, Inner::from(0) * *ONE, None),
        ];

        for case in cases {
            assert_eq!(div(case.0, case.1), case.2);
        }
    }

    #[test]
    fn p12_mul_works() {
        let cases = vec![
            (
                Inner::from(100) * *ONE,
                Inner::from(100) * *ONE,
                Some(Inner::from(10000u128) * *ONE),
            ),
            (Inner::from(200) * *ONE, Inner::from(0) * *ONE, Some(0.into())),
        ];

        for case in cases {
            assert_eq!(mul(case.0, case.1), case.2);
        }
    }
    #[test]
    fn p12_pow_works() {
        let cases = vec![
            (
                Inner::from(100) * *ONE,
                Inner::from(2) * *ONE,
                Some(Inner::from(10000u128) * *ONE),
            ),
            (
                Inner::from(2) * *ONE,
                Inner::from(2) * *ONE,
                Some(Inner::from(4000000000000u128)),
            ),
            (Inner::from(200) * *ONE, Inner::from(0) * *ONE, Some(*ONE)),
            //(Inner::from(100) * *ONE, Inner::from(1) * *ONE + Inner::from(200_000_000_000u128) , Some(Inner::from(213221000000000000u128))),
            //(Inner::from(100) * *ONE, *ONE / 2, Some(Inner::from(213221000000000000u128))),
        ];

        for case in cases {
            assert_eq!(pow(case.0, case.1), case.2);
        }
    }
}
