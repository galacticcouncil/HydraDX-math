use crate::to_u256;
use crate::types::Balance;
use num_traits::Zero;
use primitive_types::U256;
use crate::stableswap::math::two_asset_pool_math::{calculate_y, calculate_d, calculate_ann};
use crate::xyk::calculate_out_given_in as xyk_out_given_in;

pub(crate) fn calculate_stable_out_given_in<const N: u8, const N_Y: u8>(
    reserve_in: Balance,
    reserve_out: &[Balance; 2],
    amount_in: Balance,
    asset_out: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = calculate_ann(amplification).unwrap();
    let d = calculate_d::<N>(reserve_out, ann, precision).unwrap();
    let d_out = xyk_out_given_in(reserve_in, d, amount_in).unwrap();
    let d_new = d.checked_sub(d_out).unwrap();

    let mut reserve = 0_u128;
    if asset_out == 0 {
        reserve = reserve_out[1];
    } else if asset_out == 1 {
        reserve = reserve_out[0];
    } else {
        return Option::None;
    }
    reserve_out[asset_out].checked_sub(calculate_y::<N_Y>(reserve, d_new, ann, precision)?)
}

#[cfg(test)]
mod invariants {
    // use super::two_asset_pool_math::*;
    use super::Balance;
    use super::calculate_stable_out_given_in;
    use proptest::prelude::*;
    use proptest::proptest;
    use crate::stableswap::math::two_asset_pool_math::calculate_d;
    use std::dbg;
    use primitive_types::U256;
    use super::to_u256;

    pub const ONE: Balance = 1_000_000_000_000;

    const D_ITERATIONS: u8 = 127;
    const Y_ITERATIONS: u8 = 63;

    const RESERVE_RANGE: (Balance, Balance) = (100_000 * ONE, 100_000_000 * ONE);
    const LOW_RESERVE_RANGE: (Balance, Balance) = (1000_u128, 1001_u128);
    const HIGH_RESERVE_RANGE: (Balance, Balance) = (500_000_000_000 * ONE, 500_000_000_001 * ONE);

    fn trade_amount() -> impl Strategy<Value = Balance> {
        1000..10000 * ONE
    }

    // fn high_trade_amount() -> impl Strategy<Value = Balance> {
    //     500_000_000_000 * ONE..500_000_000_001 * ONE
    // }

    fn asset_reserve() -> impl Strategy<Value = Balance> {
        RESERVE_RANGE.0..RESERVE_RANGE.1
    }
    // fn low_asset_reserve() -> impl Strategy<Value = Balance> {
    //     LOW_RESERVE_RANGE.0..LOW_RESERVE_RANGE.1
    // }
    // fn high_asset_reserve() -> impl Strategy<Value = Balance> {
    //     HIGH_RESERVE_RANGE.0..HIGH_RESERVE_RANGE.1
    // }

    fn amplification() -> impl Strategy<Value = Balance> {
        2..10000u128
    }


    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in(amount_in in trade_amount(),
            reserve_in in asset_reserve(),
            reserve_stable in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_out, reserve_stable], ann, precision).unwrap();
            let result = calculate_stable_out_given_in::<D_ITERATIONS, Y_ITERATIONS>(reserve_in, &[reserve_out, reserve_stable], amount_in, 0, amp, precision);
            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_out.checked_sub(result.unwrap()).unwrap(), reserve_stable], ann, precision).unwrap();

            assert!(d2 <= d1);

            let (d1_hp, d2_hp, amt_in_hp, rsv_in_hp) = to_u256!(d1, d2, amount_in, reserve_in);

            let invar_before = d1_hp.checked_mul(rsv_in_hp).unwrap();

            let invar_after = d2_hp.checked_mul(rsv_in_hp.checked_add(amt_in_hp).unwrap()).unwrap();

            assert!(invar_after > invar_before);
            let precision = to_u256!(100_000_000_000_u128);
            dbg!(invar_after);
            dbg!(invar_before);
            dbg!(invar_after.checked_sub(invar_before).unwrap().checked_mul(precision).unwrap().checked_div(invar_before).unwrap());
            assert!(invar_after.checked_sub(invar_before).unwrap().checked_mul(precision).unwrap().checked_div(invar_before).unwrap() == U256::zero());
        }
    }


}