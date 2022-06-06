use crate::types::Balance;

/// Calculating amount to be received from the pool given the amount to be sent to the pool and both reserves.
pub fn calculate_out_given_in(
    reserve_in: Balance,
    reserve_out: Balance,
    amount_in: Balance,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = two_asset_pool_math::calculate_ann(amplification)?;
    let new_reserve_out =
        two_asset_pool_math::calculate_y_given_in(amount_in, reserve_in, reserve_out, ann, precision)?;
    reserve_out.checked_sub(new_reserve_out)
}

/// Calculating amount to be sent to the pool given the amount to be received from the pool and both reserves.
pub fn calculate_in_given_out(
    reserve_in: Balance,
    reserve_out: Balance,
    amount_out: Balance,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = two_asset_pool_math::calculate_ann(amplification)?;
    let new_reserve_in =
        two_asset_pool_math::calculate_y_given_out(amount_out, reserve_in, reserve_out, ann, precision)?;
    new_reserve_in.checked_sub(reserve_in)
}

pub(crate) mod two_asset_pool_math {
    use super::Balance;
    use crate::to_u256;
    use num_traits::Zero;
    use primitive_types::U256;

    pub(crate) fn calculate_ann(amplification: Balance) -> Option<Balance> {
        (0..2).try_fold(amplification, |acc, _| acc.checked_mul(2u128))
    }

    /// Calculate `d` so the Stableswap invariant does not change.
    ///
    /// Note: this works for two asset pools only!
    ///
    /// This is solved using newtons formula by iterating the following equation until convergence.
    ///
    /// dn+1 = (ann * S + n * Dp) * dn) / ( (ann -1) * dn + (n+1) * dp)
    ///
    /// where
    ///
    /// S = sum(xp)
    /// dp = d^n+1 / prod(sp)
    ///
    /// if (dn+1 - dn) <= precision - converged successfully.
    ///
    /// Parameters:
    /// - `xp`: reserves of asset a and b.
    /// - `ann`: amplification coefficient multiplied by `2^2` ( number of assets in pool)
    /// - `precision`:  convergence precision
    pub(crate) fn calculate_d(xp: &[Balance; 2], ann: Balance, precision: Balance) -> Option<Balance> {
        let two_u256 = to_u256!(2_u128);
        let n_coins = two_u256;

        let mut xp_hp: [U256; 2] = [to_u256!(xp[0]), to_u256!(xp[1])];
        xp_hp.sort();

        let s_hp = xp_hp.iter().try_fold(U256::zero(), |acc, v| acc.checked_add(*v))?;

        if s_hp == U256::zero() {
            return Some(Balance::zero());
        }

        let mut d = s_hp;

        let (ann_hp, precision_hp) = to_u256!(ann, precision);

        for _ in 0..255 {
            let d_p = xp_hp
                .iter()
                .try_fold(d, |acc, v| acc.checked_mul(d)?.checked_div(v.checked_mul(n_coins)?))?;
            let d_prev = d;

            d = ann_hp
                .checked_mul(s_hp)?
                .checked_add(d_p.checked_mul(n_coins)?)?
                .checked_mul(d)?
                .checked_div(
                    ann_hp
                        .checked_sub(U256::one())?
                        .checked_mul(d)?
                        .checked_add(n_coins.checked_add(U256::one())?.checked_mul(d_p)?)?,
                )?
                .checked_add(two_u256)?; // adding two here is sufficient to account for rounding
                                         // errors, AS LONG AS the minimum reserves are 2 for each
                                         // asset. I.e., as long as xp_hp[0] >= 2 and xp_hp[1] >= 2

            // adding two guarantees that this function will return
            // a value larger than or equal to the correct D invariant

            if d > d_prev {
                if d.checked_sub(d_prev)? <= precision_hp {
                    return Balance::try_from(d).ok();
                }
            } else if d_prev.checked_sub(d)? <= precision_hp {
                return Balance::try_from(d).ok();
            }
        }
        None
    }

    /// Calculate new amount of reserve OUT given amount to be added to the pool
    pub(crate) fn calculate_y_given_in(
        amount: Balance,
        reserve_in: Balance,
        reserve_out: Balance,
        ann: Balance,
        precision: Balance,
    ) -> Option<Balance> {
        let new_reserve_in = reserve_in.checked_add(amount)?;

        let d = calculate_d(&[reserve_in, reserve_out], ann, precision)?;

        calculate_y(new_reserve_in, d, ann, precision)
    }

    /// Calculate new amount of reserve IN given amount to be withdrawn from the pool
    pub(crate) fn calculate_y_given_out(
        amount: Balance,
        reserve_in: Balance,
        reserve_out: Balance,
        ann: Balance,
        precision: Balance,
    ) -> Option<Balance> {
        let new_reserve_out = reserve_out.checked_sub(amount)?;

        let d = calculate_d(&[reserve_in, reserve_out], ann, precision)?;

        calculate_y(new_reserve_out, d, ann, precision)
    }

    /// Calculate new reserve amount of an asset given updated reserve of secondary asset and initial `d`
    ///
    /// This is solved using Newton's method by iterating the following until convergence:
    ///
    /// yn+1 = (yn^2 + c) / ( 2 * yn + b - d )
    ///
    /// where
    /// c = d^n+1 / n^n * P * ann
    /// b = s + d/ann
    ///
    /// note: thw s and P are sum or prod of all reserves except the one we are calculating but since we are in 2 asset pool - it is just one
    /// s = reserve
    /// P = reserve
    ///
    /// Note: this implementation works only for 2 assets pool!
    fn calculate_y(reserve: Balance, d: Balance, ann: Balance, precision: Balance) -> Option<Balance> {
        let (d_hp, two_hp, ann_hp, new_reserve_hp, precision_hp) = to_u256!(d, 2u128, ann, reserve, precision);

        let n_coins_hp = two_hp;
        let s = new_reserve_hp;
        let mut c = d_hp;

        c = c.checked_mul(d_hp)?.checked_div(new_reserve_hp.checked_mul(two_hp)?)?;

        c = c.checked_mul(d_hp)?.checked_div(ann_hp.checked_mul(n_coins_hp)?)?;

        let b = s.checked_add(d_hp.checked_div(ann_hp)?)?;
        let mut y = d_hp;

        for _ in 0..255 {
            let y_prev = y;
            y = y
                .checked_mul(y)?
                .checked_add(c)?
                .checked_div(two_hp.checked_mul(y)?.checked_add(b)?.checked_sub(d_hp)?)?
                .checked_add(two_hp)?;
            // Adding 2 guarantees that at each iteration, we are rounding so as to *overestimate* compared
            // to exact division.
            // Note that while this should guarantee convergence when y is decreasing, it may cause
            // issues when y is increasing.

            if y > y_prev {
                if y.checked_sub(y_prev)? <= precision_hp {
                    return Balance::try_from(y).ok();
                }
            } else if y_prev.checked_sub(y)? <= precision_hp {
                return Balance::try_from(y).ok();
            }
        }

        None
    }

    #[test]
    fn test_ann() {
        assert_eq!(calculate_ann(1u128), Some(4u128));
        assert_eq!(calculate_ann(10u128), Some(40u128));
        assert_eq!(calculate_ann(100u128), Some(400u128));
    }

    #[test]
    fn test_d() {
        let precision = 1_u128;

        let reserves = [1000u128, 1000u128];
        let ann = 4u128;
        assert_eq!(calculate_d(&reserves, ann, precision), Some(2000u128 + 2u128));

        let reserves = [1_000_000_000_000_000_000_000u128, 1_000_000_000_000_000_000_000u128];
        let ann = 4u128;
        assert_eq!(
            calculate_d(&reserves, ann, precision),
            Some(2_000_000_000_000_000_000_000u128 + 2u128)
        );
    }

    #[test]
    fn test_d_with_zero_reserves() {
        let precision = 1_u128;
        let reserves = [0u128, 0u128];
        let ann = 4u128;
        assert_eq!(calculate_d(&reserves, ann, precision), Some(0u128));
    }

    #[test]
    fn test_y_given_in() {
        let precision = 1_u128;
        let reserves = [1000u128, 2000u128];
        let ann = 4u128;

        let amount_in = 100u128;
        assert_eq!(calculate_d(&reserves, ann, precision), Some(2942u128));
        assert_eq!(
            calculate_y_given_in(amount_in, reserves[0], reserves[1], ann, precision),
            Some(2000u128 - 121u128)
        );
        assert_eq!(
            calculate_d(&[1100u128, 2000u128 - 125u128], ann, precision),
            Some(2942u128)
        );
    }

    #[test]
    fn test_y_given_out() {
        let precision = 1_u128;
        let reserves = [1000u128, 2000u128];
        let ann = 4u128;

        let amount_out = 100u128;

        let expected_in = 83u128;

        assert_eq!(calculate_d(&reserves, ann, precision), Some(2942u128));

        assert_eq!(
            calculate_y_given_out(amount_out, reserves[0], reserves[1], ann, precision),
            Some(1000u128 + expected_in)
        );
        assert_eq!(
            calculate_d(&[1000u128 + expected_in, 2000u128 - amount_out], ann, precision),
            Some(2946u128)
        );
    }

    #[test]
    fn test_d_case() {
        let amp = 400u128;
        let ann = amp * 4u128;

        let precision = 1u128;

        let result = calculate_d(&[500000000000008580273458u128, 10u128], ann, precision);

        assert!(result.is_some());
    }

    #[test]
    fn test_d_case2() {
        let amp = 168u128;
        let ann = amp * 4u128;

        let precision = 1u128;

        let result = calculate_d(&[500000000000000000000010u128, 11u128], ann, precision);

        assert!(result.is_some());
    }
}

#[cfg(test)]
mod invariants {
    use super::two_asset_pool_math::*;
    use super::Balance;
    use super::{calculate_in_given_out, calculate_out_given_in};
    use proptest::prelude::*;
    use proptest::proptest;

    pub const ONE: Balance = 1_000_000_000_000;

    const RESERVE_RANGE: (Balance, Balance) = (100_000 * ONE, 100_000_000 * ONE);
    const LOW_RESERVE_RANGE: (Balance, Balance) = (10_u128, 11_u128);
    const HIGH_RESERVE_RANGE: (Balance, Balance) = (500_000_000_000 * ONE, 500_000_000_001 * ONE);

    fn trade_amount() -> impl Strategy<Value = Balance> {
        1000..10000 * ONE
    }

    fn high_trade_amount() -> impl Strategy<Value = Balance> {
        500_000_000_000 * ONE..500_000_000_001 * ONE
    }

    fn asset_reserve() -> impl Strategy<Value = Balance> {
        RESERVE_RANGE.0..RESERVE_RANGE.1
    }
    fn low_asset_reserve() -> impl Strategy<Value = Balance> {
        LOW_RESERVE_RANGE.0..LOW_RESERVE_RANGE.1
    }
    fn high_asset_reserve() -> impl Strategy<Value = Balance> {
        HIGH_RESERVE_RANGE.0..HIGH_RESERVE_RANGE.1
    }

    fn amplification() -> impl Strategy<Value = Balance> {
        2..10000u128
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_d_extreme(reserve_in in  low_asset_reserve(),
            reserve_out in  high_asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d = calculate_d(&[reserve_in, reserve_out], ann, precision);

            assert!(d.is_some());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in_extreme(amount_in in high_trade_amount(),
            reserve_in in  low_asset_reserve(),
            reserve_out in  high_asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_out_given_in(reserve_in, reserve_out, amount_in, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d(&[reserve_in + amount_in, reserve_out - result.unwrap() ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in(amount_in in trade_amount(),
            reserve_in in  asset_reserve(),
            reserve_out in  asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_out_given_in(reserve_in, reserve_out, amount_in, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d(&[reserve_in + amount_in, reserve_out - result.unwrap() ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_in_given_out(amount_out in trade_amount(),
            reserve_in in  asset_reserve(),
            reserve_out in  asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp*4u128;

            let precision = 1u128;

            let d1 = calculate_d(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_in_given_out(reserve_in, reserve_out, amount_out, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d(&[reserve_in + result.unwrap(), reserve_out - amount_out ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }
}
