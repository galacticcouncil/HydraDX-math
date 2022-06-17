use crate::to_u256;
use crate::types::Balance;
use num_traits::Zero;
use primitive_types::U256;
use crate::stableswap::math::two_asset_pool_math::{calculate_y, calculate_d, calculate_ann};
use crate::xyk::calculate_out_given_in as xyk_out_given_in;

pub(crate) fn calculate_stable_out_given_lrna_in<const N: u8, const N_Y: u8>(
    reserve_lrna: Balance,
    reserve_out: &[Balance; 2],
    amount_in: Balance,
    asset_out: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = calculate_ann(amplification).unwrap();
    let d = calculate_d::<N>(reserve_out, ann, precision).unwrap();
    let d_out = xyk_out_given_in(reserve_lrna, d, amount_in).unwrap();
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

pub(crate) fn calculate_lrna_out_given_stable_in<const N: u8, const N_Y: u8>(
    reserve_lrna: Balance,
    reserve_in: &[Balance; 2],
    amount_in: Balance,
    asset_in: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = calculate_ann(amplification).unwrap();
    let mut new_reserve_in = [reserve_in[0], reserve_in[1]];
    new_reserve_in[asset_in] += amount_in;
    let d = calculate_d::<N>(reserve_in, ann, precision).unwrap();
    let d_new = calculate_d::<N>(&new_reserve_in, ann, precision).unwrap();
    let d_in = d_new.checked_sub(d).unwrap();
    let amount_out = xyk_out_given_in(d, reserve_lrna, d_in).unwrap();
    Some(amount_out)

}

pub(crate) fn calculate_stable_out_given_risk_in<const N: u8, const N_Y: u8>(
    risk_lrna: Balance,
    reserve_risk: Balance,
    stable_lrna: Balance,
    reserve_stable: &[Balance; 2],
    amount_in: Balance,
    asset_out: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let lrna_out = xyk_out_given_in(reserve_risk, risk_lrna, amount_in).unwrap();
    let stable_out = calculate_stable_out_given_lrna_in::<N,N_Y>(stable_lrna, reserve_stable, lrna_out, asset_out, amplification, precision).unwrap();
    Some(stable_out)
}

pub(crate) fn calculate_risk_out_given_stable_in<const N: u8, const N_Y: u8>(
    risk_lrna: Balance,
    reserve_risk: Balance,
    stable_lrna: Balance,
    reserve_stable: &[Balance; 2],
    amount_in: Balance,
    asset_in: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let lrna_out = calculate_lrna_out_given_stable_in::<N,N_Y>(stable_lrna, reserve_stable, amount_in, asset_in, amplification, precision).unwrap();
    let risk_out = xyk_out_given_in(risk_lrna, reserve_risk, lrna_out).unwrap();
    Some(risk_out)
}

pub(crate) fn calculate_stable_out_given_stable_in<const N: u8, const N_Y: u8>(
    lrna_in: Balance,
    reserve_in: &[Balance; 2],
    lrna_out: Balance,
    reserve_out: &[Balance; 2],
    amount_in: Balance,
    asset_in: usize,
    asset_out: usize,
    amplification_in: Balance,
    amplification_out: Balance,
    precision: Balance,
) -> Option<Balance> {
    let lrna_amt = calculate_lrna_out_given_stable_in::<N,N_Y>(lrna_in, reserve_in, amount_in, asset_in, amplification_in, precision).unwrap();
    let stable_out = calculate_stable_out_given_lrna_in::<N,N_Y>(lrna_out, reserve_out, lrna_amt, asset_out, amplification_out, precision).unwrap();
    Some(stable_out)
}


#[cfg(test)]
mod invariants {
    // use super::two_asset_pool_math::*;
    use super::Balance;
    use super::{calculate_stable_out_given_lrna_in, calculate_lrna_out_given_stable_in,
                calculate_risk_out_given_stable_in, calculate_stable_out_given_risk_in,
                calculate_stable_out_given_stable_in};
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
        fn test_stable_out_given_lrna_in(amount_in in trade_amount(),
            lrna_in in asset_reserve(),
            reserve_stable in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let reserves_before = [reserve_out, reserve_stable];

            let d1 = calculate_d::<D_ITERATIONS>(&reserves_before, ann, precision).unwrap();
            let result = calculate_stable_out_given_lrna_in::<D_ITERATIONS, Y_ITERATIONS>(lrna_in, &reserves_before, amount_in, 0, amp, precision);
            assert!(result.is_some());
            let reserves_after = [reserve_out.checked_sub(result.unwrap()).unwrap(), reserve_stable];

            let d2 = calculate_d::<D_ITERATIONS>(&reserves_after, ann, precision).unwrap();


            assert!(d2 <= d1);

            let (d1_hp, d2_hp, amt_in_hp, rsv_in_hp) = to_u256!(d1, d2, amount_in, lrna_in);

            let invar_before = d1_hp.checked_mul(rsv_in_hp).unwrap();

            let invar_after = d2_hp.checked_mul(rsv_in_hp.checked_add(amt_in_hp).unwrap()).unwrap();

            assert!(invar_after > invar_before);
            let precision = to_u256!(100_000_000_000_u128);

            assert!(invar_after.checked_sub(invar_before).unwrap().checked_mul(precision).unwrap().checked_div(invar_before).unwrap() == U256::zero());
        }
    }

    // fn does_stableswap_invariant_decrease<const N: u8>(
    //     reserve1: &[Balance; 2],
    //     reserve2: &[Balance; 2],
    //     ann: Balance,
    //     precision: Balance,
    // ) -> bool {
    //     let d1 = calculate_d::<N>(reserve1, ann, precision).unwrap();
    //     let d2 = calculate_d::<N>(reserve2, ann, precision).unwrap();
    //     return d2 < d1
    // }


    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_lrna_out_given_stable_in(amount_in in trade_amount(),
            reserve_lrna in asset_reserve(),
            reserve_stable in asset_reserve(),
            reserve_in in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_stable], ann, precision).unwrap();
            let result = calculate_lrna_out_given_stable_in::<D_ITERATIONS, Y_ITERATIONS>(reserve_lrna, &[reserve_in, reserve_stable], amount_in, 0, amp, precision);
            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in.checked_add(amount_in).unwrap(), reserve_stable], ann, precision).unwrap();

            dbg!(d1);
            dbg!(d2);

            assert!(d2 >= d1);

            let (d1_hp, d2_hp, amt_out_hp, rsv_lrna) = to_u256!(d1, d2, result.unwrap(), reserve_lrna);

            let invar_before = d1_hp.checked_mul(rsv_lrna).unwrap();

            let invar_after = d2_hp.checked_mul(rsv_lrna.checked_sub(amt_out_hp).unwrap()).unwrap();

            assert!(invar_after > invar_before);
            let precision = to_u256!(100_000_000_000_u128);

            assert!(invar_after.checked_sub(invar_before).unwrap().checked_mul(precision).unwrap().checked_div(invar_before).unwrap() == U256::zero());
        }
    }


    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_stable_out_given_risk_in(amount_in in trade_amount(),
            risk_lrna in asset_reserve(),
            reserve_risk in asset_reserve(),
            lrna_stable in asset_reserve(),
            reserve_stable in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let reserves_before = [reserve_out, reserve_stable];

            let d1 = calculate_d::<D_ITERATIONS>(&reserves_before, ann, precision).unwrap();
            let result = calculate_stable_out_given_risk_in::<D_ITERATIONS, Y_ITERATIONS>(risk_lrna, reserve_risk, lrna_stable, &reserves_before, amount_in, 0, amp, precision);
            assert!(result.is_some());
            let reserves_after = [reserve_out.checked_sub(result.unwrap()).unwrap(), reserve_stable];

            let d2 = calculate_d::<D_ITERATIONS>(&reserves_after, ann, precision).unwrap();

            assert!(d2 <= d1);

            // TODO: check both xyk pools
        }
    }


    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_risk_out_given_stable_in(amount_in in trade_amount(),
            risk_lrna in asset_reserve(),
            reserve_risk in asset_reserve(),
            lrna_stable in asset_reserve(),
            reserve_stable in asset_reserve(),
            reserve_in in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_stable], ann, precision).unwrap();
            let result = calculate_risk_out_given_stable_in::<D_ITERATIONS, Y_ITERATIONS>(risk_lrna, reserve_risk, lrna_stable, &[reserve_in, reserve_stable], amount_in, 0, amp, precision);
            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in.checked_add(amount_in).unwrap(), reserve_stable], ann, precision).unwrap();

            dbg!(d1);
            dbg!(d2);

            assert!(d2 >= d1);

            // TODO: check both xyk pools

        }
    }


    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_stable_out_given_stable_in(amount_in in trade_amount(),
            lrna0 in asset_reserve(),
            lrna1 in asset_reserve(),
            stable00 in asset_reserve(),
            stable01 in asset_reserve(),
            stable10 in asset_reserve(),
            stable11 in asset_reserve(),
            amp0 in amplification(),
            amp1 in amplification(),
        ) {
            let ann0 = amp0 * 4u128;
            let ann1 = amp1 * 4u128;

            let precision = 1u128;

            //let d00 = calculate_d::<D_ITERATIONS>(&[stable00, stable01], ann0, precision).unwrap();
            // let d01 = calculate_d::<D_ITERATIONS>(&[stable10, stable11], ann1, precision).unwrap();
            let result = calculate_stable_out_given_stable_in::<D_ITERATIONS, Y_ITERATIONS>(lrna0, &[stable00, stable01], lrna1, &[stable10, stable11], amount_in, 0, 0, amp0, amp1, precision);
            assert!(result.is_some());

            // let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in.checked_add(amount_in).unwrap(), reserve_stable], ann, precision).unwrap();


            // TODO: check both xyk pools

        }
    }


}