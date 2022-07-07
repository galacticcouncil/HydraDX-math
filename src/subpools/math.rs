use crate::to_u256;
use crate::types::Balance;
use num_traits::Zero;
use primitive_types::U256;
use crate::stableswap::math::two_asset_pool_math::{calculate_y, calculate_d, calculate_ann};
use crate::xyk::calculate_out_given_in as xyk_out_given_in;

pub(crate) struct TokenTransfer {
    transfer_1: Balance,
    transfer_2: Balance,
    transfer_3: Balance,
    amt_out: Balance
}

pub(crate) fn calculate_stable_out_given_lrna_in<const N: u8, const N_Y: u8>(
    reserve_lrna: Balance,
    reserve_out: &[Balance; 2],
    amount_in: Balance,
    asset_out: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<TokenTransfer> {
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
    let amt_out = reserve_out[asset_out].checked_sub(calculate_y::<N_Y>(reserve, d_new, ann, precision)?).unwrap();

    let transfer = TokenTransfer {
        amt_out: amt_out,
        transfer_1: d_out,
        transfer_2: 0_u128,
        transfer_3: 0_u128
    };

    Some(transfer)
}

pub(crate) fn calculate_lrna_out_given_stable_in<const N: u8, const N_Y: u8>(
    reserve_lrna: Balance,
    reserve_in: &[Balance; 2],
    amount_in: Balance,
    asset_in: usize,
    amplification: Balance,
    precision: Balance,
) -> Option<TokenTransfer> {
    let ann = calculate_ann(amplification).unwrap();
    let mut new_reserve_in = [reserve_in[0], reserve_in[1]];
    new_reserve_in[asset_in] += amount_in;
    let d = calculate_d::<N>(reserve_in, ann, precision).unwrap();
    let d_new = calculate_d::<N>(&new_reserve_in, ann, precision).unwrap();
    let d_in = d_new.checked_sub(d).unwrap();
    let amount_out = xyk_out_given_in(d, reserve_lrna, d_in).unwrap();

    let transfer = TokenTransfer {
        amt_out: amount_out,
        transfer_1: d_in,
        transfer_2: 0_u128,
        transfer_3: 0_u128
    };

    Some(transfer)

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
) -> Option<TokenTransfer> {
    let lrna_out = xyk_out_given_in(reserve_risk, risk_lrna, amount_in).unwrap();
    let stable_out = calculate_stable_out_given_lrna_in::<N,N_Y>(stable_lrna, reserve_stable, lrna_out, asset_out, amplification, precision).unwrap();

    let transfer = TokenTransfer {
        amt_out: stable_out.amt_out,
        transfer_1: lrna_out,
        transfer_2: stable_out.transfer_1,
        transfer_3: 0_u128
    };

    Some(transfer)
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
) -> Option<TokenTransfer> {
    let lrna_out = calculate_lrna_out_given_stable_in::<N,N_Y>(stable_lrna, reserve_stable, amount_in, asset_in, amplification, precision).unwrap();
    let risk_out = xyk_out_given_in(risk_lrna, reserve_risk, lrna_out.amt_out).unwrap();

    let transfer = TokenTransfer {
        amt_out: risk_out,
        transfer_1: lrna_out.transfer_1,
        transfer_2: lrna_out.amt_out,
        transfer_3: 0_u128
    };

    Some(transfer)
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
) -> Option<TokenTransfer> {
    let lrna_amt = calculate_lrna_out_given_stable_in::<N,N_Y>(lrna_in, reserve_in, amount_in, asset_in, amplification_in, precision).unwrap();
    let stable_out = calculate_stable_out_given_lrna_in::<N,N_Y>(lrna_out, reserve_out, lrna_amt.amt_out, asset_out, amplification_out, precision).unwrap();

    let transfer = TokenTransfer {
        amt_out: stable_out.amt_out,
        transfer_1: lrna_amt.transfer_1,
        transfer_2: lrna_amt.amt_out,
        transfer_3: stable_out.transfer_1
    };

    Some(transfer)
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
    use crate::to_balance;
    use primitive_types::Error::Overflow;

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


    fn approx_equal(
        x1: U256,
        x2: U256,
        precision: U256
    ) -> bool {
        let mut x_diff = U256::zero();
        if x1 >= x2 {
            x_diff = x1.checked_sub(x2).unwrap();
        } else {
            x_diff = x2.checked_sub(x1).unwrap();
        }

        x_diff.checked_mul(precision).unwrap().checked_div(x1).unwrap() == U256::zero()
    }

    fn check_xyk(
        reserves_before: &[Balance; 2],
        reserves_after: &[Balance; 2],
        precision_rounding: Balance,
    ) -> bool {
        let (x1_hp, y1_hp, x2_hp, y2_hp) = to_u256!(reserves_before[0], reserves_before[1], reserves_after[0], reserves_after[1]);
        let precision_rounding_hp = to_u256!(precision_rounding);

        let invar_before = x1_hp.checked_mul(y1_hp).unwrap();

        let invar_after = x2_hp.checked_mul(y2_hp).unwrap();

        let rounding_ok = invar_after > invar_before;

        // test xyk pool calculation
        let invar_ok = approx_equal(invar_before, invar_after, precision_rounding_hp);

        rounding_ok & invar_ok
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
            let precision_rounding = 100_000_000_000_u128;

            let stable_reserves_before = [reserve_out, reserve_stable];

            let d1 = calculate_d::<D_ITERATIONS>(&stable_reserves_before, ann, precision).unwrap();
            let result = calculate_stable_out_given_lrna_in::<D_ITERATIONS, Y_ITERATIONS>(lrna_in, &stable_reserves_before, amount_in, 0, amp, precision);
            let transfer = result.unwrap();
            let stable_reserves_after = [reserve_out.checked_sub(transfer.amt_out).unwrap(), reserve_stable];

            let d2 = calculate_d::<D_ITERATIONS>(&stable_reserves_after, ann, precision).unwrap();
            let d_transfer = transfer.transfer_1;

            let d2_actual = d1.checked_sub(d_transfer).unwrap();

            assert!(d2 <= d1);  // test that D went correct direction

            let (d2_hp, d2_actual_hp, precision_rounding_hp) = to_u256!(d2, d2_actual, precision_rounding);

            assert!(approx_equal(d2_hp, d2_actual_hp, precision_rounding_hp));

            let xyk_reserves_before = [d1, lrna_in];
            let xyk_reserves_after = [d1.checked_sub(transfer.transfer_1).unwrap(), lrna_in.checked_add(amount_in).unwrap()];
            assert!(check_xyk(&xyk_reserves_before, &xyk_reserves_after, precision_rounding))

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
            let precision_rounding = 100_000_000_000_u128;

            let stable_reserves_before = [reserve_in, reserve_stable];

            let d1 = calculate_d::<D_ITERATIONS>(&stable_reserves_before, ann, precision).unwrap();
            let result = calculate_lrna_out_given_stable_in::<D_ITERATIONS, Y_ITERATIONS>(reserve_lrna, &stable_reserves_before, amount_in, 0, amp, precision);
            let transfer = result.unwrap();
            let stable_reserves_after = [reserve_in.checked_add(amount_in).unwrap(), reserve_stable];

            let d2 = calculate_d::<D_ITERATIONS>(&stable_reserves_after, ann, precision).unwrap();
            let d_transfer = transfer.transfer_1;

            let d2_actual = d1.checked_add(d_transfer).unwrap();

            assert!(d2 >= d1);

            let (d2_hp, d2_actual_hp, precision_rounding_hp) = to_u256!(d2, d2_actual, precision_rounding);

            assert!(approx_equal(d2_hp, d2_actual_hp, precision_rounding_hp));

            let xyk_reserves_before = [d1, reserve_lrna];
            let xyk_reserves_after = [d2, reserve_lrna.checked_sub(transfer.amt_out).unwrap()];

            assert!(check_xyk(&xyk_reserves_before, &xyk_reserves_after, precision_rounding))

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
            let precision_rounding = 100_000_000_000_u128;

            let reserves_before = [reserve_out, reserve_stable];

            let d1 = calculate_d::<D_ITERATIONS>(&reserves_before, ann, precision).unwrap();
            let result = calculate_stable_out_given_risk_in::<D_ITERATIONS, Y_ITERATIONS>(risk_lrna, reserve_risk, lrna_stable, &reserves_before, amount_in, 0, amp, precision);
            let transfer = result.unwrap();
            let stable_reserves_after = [reserve_out.checked_sub(transfer.amt_out).unwrap(), reserve_stable];

            let d2 = calculate_d::<D_ITERATIONS>(&stable_reserves_after, ann, precision).unwrap();
            let d_transfer = transfer.transfer_2;

            let d2_actual = d1.checked_sub(d_transfer).unwrap();

            assert!(d2 <= d1);  // test that D went correct direction

            let (d2_hp, d2_actual_hp, precision_rounding_hp) = to_u256!(d2, d2_actual, precision_rounding);

            assert!(approx_equal(d2_hp, d2_actual_hp, precision_rounding_hp));

            let lrna_transfer = transfer.transfer_1;
            let xyk_stable_reserves_before = [d1, lrna_stable];
            let xyk_stable_reserves_after = [d1.checked_sub(d_transfer).unwrap(), lrna_stable.checked_add(lrna_transfer).unwrap()];
            assert!(check_xyk(&xyk_stable_reserves_before, &xyk_stable_reserves_after, precision_rounding));

            let xyk_risk_reserves_before = [reserve_risk, risk_lrna];
            let xyk_risk_reserves_after = [reserve_risk.checked_add(amount_in).unwrap(), risk_lrna.checked_sub(lrna_transfer).unwrap()];
            assert!(check_xyk(&xyk_risk_reserves_before, &xyk_risk_reserves_after, precision_rounding));

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
            let precision_rounding = 100_000_000_000_u128;

            let stable_reserves_before = [reserve_in, reserve_stable];

            let d1 = calculate_d::<D_ITERATIONS>(&stable_reserves_before, ann, precision).unwrap();
            let result = calculate_risk_out_given_stable_in::<D_ITERATIONS, Y_ITERATIONS>(risk_lrna, reserve_risk, lrna_stable, &stable_reserves_before, amount_in, 0, amp, precision);
            let transfer = result.unwrap();
            let stable_reserves_after = [reserve_in.checked_add(amount_in).unwrap(), reserve_stable];

            let d2 = calculate_d::<D_ITERATIONS>(&stable_reserves_after, ann, precision).unwrap();
            let d_transfer = transfer.transfer_1;

            let d2_actual = d1.checked_add(d_transfer).unwrap();

            assert!(d2 >= d1);

            let (d2_hp, d2_actual_hp, precision_rounding_hp) = to_u256!(d2, d2_actual, precision_rounding);

            assert!(approx_equal(d2_hp, d2_actual_hp, precision_rounding_hp));

            let lrna_transfer = transfer.transfer_2;
            let xyk_stable_reserves_before = [d1, lrna_stable];
            let xyk_stable_reserves_after = [d2, lrna_stable.checked_sub(lrna_transfer).unwrap()];
            assert!(check_xyk(&xyk_stable_reserves_before, &xyk_stable_reserves_after, precision_rounding));

            let xyk_risk_reserves_before = [reserve_risk, risk_lrna];
            let xyk_risk_reserves_after = [reserve_risk.checked_sub(transfer.amt_out).unwrap(), risk_lrna.checked_add(lrna_transfer).unwrap()];
            assert!(check_xyk(&xyk_risk_reserves_before, &xyk_risk_reserves_after, precision_rounding));

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
            let precision_rounding = 100_000_000_000_u128;

            let stable_reserves_before0 = [stable00, stable01];
            let stable_reserves_before1 = [stable10, stable11];


            let d01 = calculate_d::<D_ITERATIONS>(&stable_reserves_before0, ann0, precision).unwrap();
            let d11 = calculate_d::<D_ITERATIONS>(&stable_reserves_before1, ann1, precision).unwrap();
            let result = calculate_stable_out_given_stable_in::<D_ITERATIONS, Y_ITERATIONS>(lrna0, &stable_reserves_before0, lrna1, &stable_reserves_before1, amount_in, 0, 0, amp0, amp1, precision);

            let transfer = result.unwrap();
            let stable_reserves_after0 = [stable00.checked_add(amount_in).unwrap(), stable01];
            let stable_reserves_after1 = [stable10.checked_sub(transfer.amt_out).unwrap(), stable11];

            let d02 = calculate_d::<D_ITERATIONS>(&stable_reserves_after0, ann0, precision).unwrap();
            let d12 = calculate_d::<D_ITERATIONS>(&stable_reserves_after1, ann1, precision).unwrap();
            let d0_transfer = transfer.transfer_1;
            let lrna_transfer = transfer.transfer_2;
            let d1_transfer = transfer.transfer_3;

            let d02_actual = d01.checked_add(d0_transfer).unwrap();
            let d12_actual = d11.checked_sub(d1_transfer).unwrap();

            assert!(d02 >= d01);
            assert!(d12 <= d11);

            let (d02_hp, d02_actual_hp, precision_rounding_hp) = to_u256!(d02, d02_actual, precision_rounding);
            let (d12_hp, d12_actual_hp, precision_rounding_hp) = to_u256!(d12, d12_actual, precision_rounding);

            assert!(approx_equal(d02_hp, d02_actual_hp, precision_rounding_hp));
            assert!(approx_equal(d12_hp, d12_actual_hp, precision_rounding_hp));

            let xyk_stable0_reserves_before = [d01, lrna0];
            let xyk_stable0_reserves_after = [d02, lrna0.checked_sub(lrna_transfer).unwrap()];
            assert!(check_xyk(&xyk_stable0_reserves_before, &xyk_stable0_reserves_after, precision_rounding));

            let xyk_stable1_reserves_before = [d11, lrna1];
            let xyk_stable1_reserves_after = [d12, lrna1.checked_add(lrna_transfer).unwrap()];
            assert!(check_xyk(&xyk_stable1_reserves_before, &xyk_stable1_reserves_after, precision_rounding));

        }
    }


}