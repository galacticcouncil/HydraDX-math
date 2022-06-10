use crate::to_u256;
use crate::types::Balance;
use num_traits::Zero;
use primitive_types::U256;

/// Calculating amount to be received from the pool given the amount to be sent to the pool and both reserves.
/// N - number of iterations to use for Newton's formula to calculate parameter D ( it should be >=1 otherwise it wont converge at all and will always fail
/// N_Y - number of iterations to use for Newton's formula to calculate reserve Y ( it should be >=1 otherwise it wont converge at all and will always fail
pub fn calculate_out_given_in<const N: u8, const N_Y: u8>(
    reserve_in: Balance,
    reserve_out: Balance,
    amount_in: Balance,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = two_asset_pool_math::calculate_ann(amplification)?;
    let new_reserve_out =
        two_asset_pool_math::calculate_y_given_in::<N, N_Y>(amount_in, reserve_in, reserve_out, ann, precision)?;
    reserve_out.checked_sub(new_reserve_out)
}

/// Calculating amount to be sent to the pool given the amount to be received from the pool and both reserves.
/// N - number of iterations to use for Newton's formula ( it should be >=1 otherwise it wont converge at all and will always fail
/// N_Y - number of iterations to use for Newton's formula to calculate reserve Y ( it should be >=1 otherwise it wont converge at all and will always fail
pub fn calculate_in_given_out<const N: u8, const N_Y: u8>(
    reserve_in: Balance,
    reserve_out: Balance,
    amount_out: Balance,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = two_asset_pool_math::calculate_ann(amplification)?;
    let new_reserve_in =
        two_asset_pool_math::calculate_y_given_out::<N, N_Y>(amount_out, reserve_in, reserve_out, ann, precision)?;
    new_reserve_in.checked_sub(reserve_in)
}

/// Calculate shares amount after liquidity is added to the pool.
///
/// No fee applied. Currently is expected that liquidity of both assets are added to the pool.
///
/// share_amount = share_supply * ( d1 - d0 ) / d0
///
/// Returns `Some(shares)` when successful.
pub fn calculate_add_liquidity_shares<const N: u8>(
    initial_reserves: &[Balance; 2],
    updated_reserves: &[Balance; 2],
    amplification: Balance,
    precision: Balance,
    share_issuance: Balance,
) -> Option<Balance> {
    let ann = two_asset_pool_math::calculate_ann(amplification)?;

    let initial_d = two_asset_pool_math::calculate_d::<N>(initial_reserves, ann, precision)?;

    // We must make sure the updated_d is rounded *down* so that we are not giving the new position too many shares.
    // calculate_d can return a D value that is above the correct D value by up to 2, so we subtract 2.
    let updated_d = two_asset_pool_math::calculate_d::<N>(updated_reserves, ann, precision)?.checked_sub(2_u128)?;

    if updated_d < initial_d {
        return None;
    }

    if share_issuance == 0 {
        // if first liquidity added
        Some(updated_d)
    } else {
        let (issuance_hp, d_diff, d0) = to_u256!(share_issuance, updated_d - initial_d, initial_d);
        let share_amount = issuance_hp.checked_mul(d_diff)?.checked_div(d0)?;
        Balance::try_from(share_amount).ok()
    }
}

/// Given amount of shares and asset reserves, calculate corresponding amounts of each asset to be withdrawn.
pub fn calculate_remove_liquidity_amounts(
    reserves: &[Balance; 2],
    shares: Balance,
    share_asset_issuance: Balance,
) -> Option<(Balance, Balance)> {
    if share_asset_issuance.is_zero() {
        return None;
    }

    let (shares_hp, issuance_hp) = to_u256!(shares, share_asset_issuance);

    let calculate_amount = |asset_reserve: Balance| {
        Balance::try_from(
            to_u256!(asset_reserve)
                .checked_mul(shares_hp)?
                .checked_div(issuance_hp)?,
        )
        .ok()
    };

    let amount_a = calculate_amount(reserves[0])?;
    let amount_b = calculate_amount(reserves[1])?;

    Some((amount_a, amount_b))
}

/// Stableswap/curve math reduced to two assets.
pub(crate) mod two_asset_pool_math {
    use super::Balance;
    use crate::to_u256;
    use num_traits::Zero;
    use primitive_types::U256;

    pub(crate) fn calculate_ann(amplification: Balance) -> Option<Balance> {
        (0..2).try_fold(amplification, |acc, _| acc.checked_mul(2u128))
    }

    #[inline]
    fn abs_diff(d0: U256, d1: U256) -> Option<U256> {
        if d1 > d0 {
            d1.checked_sub(d0)
        } else {
            d0.checked_sub(d1)
        }
    }

    #[inline]
    fn has_converged( v0: U256, v1: U256, precision: U256) -> Option<bool>{
        let diff = abs_diff(v0, v1)?;

        if v1 <= v0 && diff < precision{
            return Some(true);
        }else if v1 > v0 && diff <= precision{
            return Some(true);
        }

        Some(false)
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
    pub(crate) fn calculate_d<const N: u8>(xp: &[Balance; 2], ann: Balance, precision: Balance) -> Option<Balance> {
        let two_u256 = to_u256!(2_u128);
        let n_coins = two_u256;

        let mut xp_hp: [U256; 2] = [to_u256!(xp[0]), to_u256!(xp[1])];
        xp_hp.sort();

        let s_hp = xp_hp[0].checked_add(xp_hp[1])?;

        if s_hp == U256::zero() {
            return Some(Balance::zero());
        }

        let mut d = s_hp;

        let (ann_hp, precision_hp) = to_u256!(ann, precision);

        for _ in 0..N {
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
                // adding two here is sufficient to account for rounding
                // errors, AS LONG AS the minimum reserves are 2 for each
                // asset. I.e., as long as xp_hp[0] >= 2 and xp_hp[1] >= 2
                // adding two guarantees that this function will return
                // a value larger than or equal to the correct D invariant
                .checked_add(two_u256)?;

            if matches!(has_converged(d_prev, d, precision_hp), Some(true)){
                // If runtime-benchmarks - dont return and force max iterations
                #[cfg(not(feature = "runtime-benchmarks"))]
                return Balance::try_from(d).ok();
            }
        }

        Balance::try_from(d).ok()
    }

    /// Calculate new amount of reserve OUT given amount to be added to the pool
    pub(crate) fn calculate_y_given_in<const N: u8, const N_Y: u8>(
        amount: Balance,
        reserve_in: Balance,
        reserve_out: Balance,
        ann: Balance,
        precision: Balance,
    ) -> Option<Balance> {
        let new_reserve_in = reserve_in.checked_add(amount)?;

        let d = calculate_d::<N>(&[reserve_in, reserve_out], ann, precision)?;

        calculate_y::<N_Y>(new_reserve_in, d, ann, precision)
    }

    /// Calculate new amount of reserve IN given amount to be withdrawn from the pool
    pub(crate) fn calculate_y_given_out<const N: u8, const N_Y: u8>(
        amount: Balance,
        reserve_in: Balance,
        reserve_out: Balance,
        ann: Balance,
        precision: Balance,
    ) -> Option<Balance> {
        let new_reserve_out = reserve_out.checked_sub(amount)?;

        let d = calculate_d::<N>(&[reserve_in, reserve_out], ann, precision)?;

        calculate_y::<N_Y>(new_reserve_out, d, ann, precision)
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
    fn calculate_y<const N: u8>(reserve: Balance, d: Balance, ann: Balance, precision: Balance) -> Option<Balance> {
        let (d_hp, two_hp, ann_hp, new_reserve_hp, precision_hp) = to_u256!(d, 2u128, ann, reserve, precision);

        let n_coins_hp = two_hp;
        let s = new_reserve_hp;
        let mut c = d_hp;

        c = c.checked_mul(d_hp)?.checked_div(new_reserve_hp.checked_mul(two_hp)?)?;

        c = c.checked_mul(d_hp)?.checked_div(ann_hp.checked_mul(n_coins_hp)?)?;

        let b = s.checked_add(d_hp.checked_div(ann_hp)?)?;
        let mut y = d_hp;

        for _ in 0..N {
            let y_prev = y;
            y = y
                .checked_mul(y)?
                .checked_add(c)?
                .checked_div(two_hp.checked_mul(y)?.checked_add(b)?.checked_sub(d_hp)?)?
                // Adding 2 guarantees that at each iteration, we are rounding so as to *overestimate* compared
                // to exact division.
                // Note that while this should guarantee convergence when y is decreasing, it may cause
                // issues when y is increasing.
                .checked_add(two_hp)?;

            if matches!(has_converged(y_prev, y, precision_hp), Some(true)) {
                // If runtime-benchmarks - dont return and force max iterations
                #[cfg(not(feature = "runtime-benchmarks"))]
                return Balance::try_from(y).ok();
            }
        }

        Balance::try_from(y).ok()
    }
}

#[cfg(test)]
mod test_two_assets_math {
    const D_ITERATIONS: u8 = 128;
    const Y_ITERATIONS: u8 = 64;

    use super::two_asset_pool_math::*;
    use crate::types::Balance;

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
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&reserves, ann, precision),
            Some(2000u128 + 2u128)
        );

        let reserves = [1_000_000_000_000_000_000_000u128, 1_000_000_000_000_000_000_000u128];
        let ann = 4u128;
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&reserves, ann, precision),
            Some(2_000_000_000_000_000_000_000u128 + 2u128)
        );
    }

    #[test]
    fn test_d_with_zero_reserves() {
        let precision = 1_u128;
        let reserves = [0u128, 0u128];
        let ann = 4u128;
        assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, ann, precision), Some(0u128));
    }

    #[test]
    fn test_y_given_in() {
        let precision = 1_u128;
        let reserves = [1000u128, 2000u128];
        let ann = 4u128;

        let amount_in = 100u128;
        assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, ann, precision), Some(2942u128));
        assert_eq!(
            calculate_y_given_in::<D_ITERATIONS, Y_ITERATIONS>(amount_in, reserves[0], reserves[1], ann, precision),
            Some(2000u128 - 121u128)
        );
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&[1100u128, 2000u128 - 125u128], ann, precision),
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

        assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, ann, precision), Some(2942u128));

        assert_eq!(
            calculate_y_given_out::<D_ITERATIONS, Y_ITERATIONS>(amount_out, reserves[0], reserves[1], ann, precision),
            Some(1000u128 + expected_in)
        );
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&[1000u128 + expected_in, 2000u128 - amount_out], ann, precision),
            Some(2946u128)
        );
    }

    #[test]
    fn test_d_case() {
        let amp = 400u128;
        let ann = amp * 4u128;

        let precision = 1u128;

        let result = calculate_d::<D_ITERATIONS>(&[500000000000008580273458u128, 10u128], ann, precision);

        assert!(result.is_some());
    }

    #[test]
    fn test_d_case2() {
        let amp = 168u128;
        let ann = amp * 4u128;

        let precision = 1u128;

        let result = calculate_d::<D_ITERATIONS>(&[500000000000000000000010u128, 11u128], ann, precision);

        assert!(result.is_some());
    }

    #[test]
    fn test_case_03() {
        let reserve_in: Balance = 95329220803912837655;
        let reserve_out: Balance = 57374284583541134907;
        let amp: u128 = 310;

        let ann = amp * 4u128;

        let precision = 1u128;

        let d = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision);

        assert!(d.is_some());
    }
}

#[cfg(test)]
mod invariants {
    use super::two_asset_pool_math::*;
    use super::Balance;
    use super::{calculate_add_liquidity_shares, calculate_in_given_out, calculate_out_given_in};
    use proptest::prelude::*;
    use proptest::proptest;

    pub const ONE: Balance = 1_000_000_000_000;

    const D_ITERATIONS: u8 = 255;
    const Y_ITERATIONS: u8 = 64;

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
        fn test_d_extreme(reserve_in in low_asset_reserve(),
            reserve_out in high_asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision);

            assert!(d.is_some());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in_extreme(amount_in in high_trade_amount(),
            reserve_in in low_asset_reserve(),
            reserve_out in high_asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_out_given_in::<D_ITERATIONS, Y_ITERATIONS>(reserve_in, reserve_out, amount_in, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in + amount_in, reserve_out - result.unwrap() ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in(amount_in in trade_amount(),
            reserve_in in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_out_given_in::<D_ITERATIONS, Y_ITERATIONS>(reserve_in, reserve_out, amount_in, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in + amount_in, reserve_out - result.unwrap() ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_in_given_out(amount_out in trade_amount(),
            reserve_in in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp*4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_in_given_out::<D_ITERATIONS,Y_ITERATIONS>(reserve_in, reserve_out, amount_out, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in + result.unwrap(), reserve_out - amount_out ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_add_liquidity(
            amount_a in trade_amount(),
            amount_b in trade_amount(),
            reserve_a in asset_reserve(),
            reserve_b in asset_reserve(),
            amp in amplification(),
            issuance in asset_reserve(),
        ) {
            let precision = 1u128;

            let initial_reserves = &[reserve_a, reserve_b];
            let updated_reserves = &[reserve_a.checked_add(amount_a).unwrap(), reserve_b.checked_add(amount_b).unwrap()];

            let result = calculate_add_liquidity_shares::<D_ITERATIONS>(initial_reserves, updated_reserves, amp, precision, issuance);

            assert!(result.is_some());
        }
    }
}
