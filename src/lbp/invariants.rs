use proptest::prelude::*;
use crate::lbp::lbp;
use crate::types::{Balance, FixedBalance};
use super::super::test_utils::assert_eq_approx;
use sp_arithmetic::FixedU128;
use primitive_types::U256;
use crate::transcendental::pow;
use crate::MathError::Overflow;

use fixed::types::U4F124 as FixedRatio;
use crate::to_balance;

pub const ONE: Balance = 1_000_000_000_000;
const TOLERANCE: Balance = 1_000;

fn start_blocks() -> impl Strategy<Value = u32> {
	0..100u32
}

fn end_blocks() -> impl Strategy<Value = u32> {
	200..300u32
}

fn initial_weight() -> impl Strategy<Value = u32> {
	1000..1500u32
}

fn get_weight() -> impl Strategy<Value = u32> {
    1000..2000u32
}

fn final_weight() -> impl Strategy<Value = u32> {
	1500..2000u32
}

fn block_number() -> impl Strategy<Value = u32> {
	100..200u32
}

fn asset_reserve() -> impl Strategy<Value = Balance> {
    1000 * ONE..10_000_000 * ONE
}

fn trade_amount() -> impl Strategy<Value = Balance> {
    ONE..100 * ONE
}

fn assert_asset_invariant(
    old_state: (Balance, Balance),
    new_state: (Balance, Balance),
    weights: (u32, u32),
    tolerance: FixedU128,
    desc: &str,
) {
    let new_pool_balance_a = lbp::convert_to_fixed(new_state.0);
    let new_pool_balance_b = lbp::convert_to_fixed(new_state.1);

    let old_pool_balance_a = lbp::convert_to_fixed(old_state.0);
    let old_pool_balance_b = lbp::convert_to_fixed(old_state.1);

    let weight_a = lbp::convert_to_fixed(weights.0 as Balance);
    let weight_b = lbp::convert_to_fixed(weights.1 as Balance);
    let weight_ratio = weight_a.checked_div(weight_b).unwrap();



    let reserve_ratio = old_pool_balance_a.checked_div(new_pool_balance_a).unwrap();
    let reserve_ratio_pow = pow(reserve_ratio, weight_ratio).map_err(|_| Overflow).unwrap();

    let new_pool_balance_b_calc = old_pool_balance_b.checked_mul(reserve_ratio_pow).unwrap();
    assert!(new_pool_balance_b >= new_pool_balance_b_calc, "Invariant decreased for {}", desc);

    // let new_weighted_reserve_for_asset_a: FixedBalance  = pow(new_pool_balance_a, weight_a).unwrap();
    // let new_weighted_reserve_for_asset_b: FixedBalance  = pow(new_pool_balance_b, weight_b).unwrap();
    //
    // let old_weighted_reserve_for_asset_a: FixedBalance  = pow(old_pool_balance_a, weight_a).unwrap();
    // let old_weighted_reserve_for_asset_b: FixedBalance  = pow(old_pool_balance_b, weight_b).unwrap();
    //
    // let s_new = lbp::convert_from_fixed(new_weighted_reserve_for_asset_a).unwrap().checked_mul(lbp::convert_from_fixed(new_weighted_reserve_for_asset_b).unwrap()).unwrap();
    // let s_old = lbp::convert_from_fixed(old_weighted_reserve_for_asset_a).unwrap().checked_mul(lbp::convert_from_fixed(old_weighted_reserve_for_asset_b).unwrap()).unwrap();
    //
    // dbg!(s_new);
    // dbg!(s_old);
    //
    // assert!(s_new >= s_old, "Invariant decreased for {}", desc);
    //
    // let s1_u128 = Balance::try_from(s_new).unwrap();
    // let s2_u128 = Balance::try_from(s_old).unwrap();
    //
    // let invariant = FixedU128::from((s1_u128, ONE)) / FixedU128::from((s2_u128, ONE));
    // assert_eq_approx!(invariant, FixedU128::from(1u128), tolerance, desc);
}

//Spec: https://www.notion.so/Property-Tests-7b506add39ea48fc8f68ecd18391e30a#9bbed73541c84e45a9855360aeee1f9b
proptest! {
	#![proptest_config(ProptestConfig::with_cases(1000))]
	#[test]
	fn calculate_linear_weights(
		start_x in start_blocks(),
		end_x in end_blocks(),
		start_y in initial_weight(),
		end_y in final_weight(),
		at in block_number()
	) {
		//Arrange
		let weight  = lbp::calculate_linear_weights(start_x,end_x,start_y,end_y,at).unwrap();

		let a1 = at - start_x;
		let a2 = end_y - start_y;

		let b1 = weight - start_y;
		let b2 = end_x - start_x;

		//Act and Assert
		assert_eq_approx!(a1*a2, b1*b2, 500, "The invariant does not hold")
	}
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn sell_invariants( asset_in_reserve in asset_reserve(),
        asset_out_reserve in asset_reserve(),
        amount in  trade_amount(),
        weight_a in get_weight(),
        weight_b in get_weight()
    ) {
        let amount_out = crate::lbp::calculate_out_given_in(asset_in_reserve, asset_out_reserve, weight_a, weight_b, amount).unwrap();

        assert_asset_invariant((asset_in_reserve, asset_out_reserve),
            (asset_in_reserve + amount, asset_out_reserve - amount_out),
            (weight_a, weight_b),
            FixedU128::from((TOLERANCE,ONE)),
            "out given in"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]
    #[test]
    fn out_given_in_nonexploitable( reserve_a in asset_reserve(),
        reserve_b in asset_reserve(),
        weight_a in get_weight(),
        weight_b in get_weight(),
        amount in trade_amount(),
    ) {

        let amount_b_out = crate::lbp::calculate_out_given_in(reserve_a, reserve_b, weight_a, weight_b, amount).unwrap();
        let amount_a_out = crate::lbp::calculate_out_given_in(reserve_b - amount_b_out, reserve_a + amount, weight_b, weight_a, amount_b_out).unwrap();
        dbg!(amount);
        dbg!(amount_a_out);
        assert!(amount_a_out <= amount, "Trading is exploitable");
        assert_eq_approx!(amount_a_out, amount, 500, "out_given_in_nonexploitable")
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]
    #[test]
    fn in_given_out_nonexploitable( reserve_a in asset_reserve(),
        reserve_b in asset_reserve(),
        weight_a in get_weight(),
        weight_b in get_weight(),
        amount_b_out in trade_amount(),
    ) {

        let amount_a_in = crate::lbp::calculate_in_given_out(reserve_a, reserve_b, weight_a, weight_b, amount_b_out).unwrap();
        let amount_a_out = crate::lbp::calculate_out_given_in(reserve_b - amount_b_out, reserve_a + amount_a_in, weight_b, weight_a, amount_b_out).unwrap();
        dbg!(amount_a_in);
        dbg!(amount_a_out);
        assert!(amount_a_out <= amount_a_in, "Trading is exploitable");
        assert_eq_approx!(amount_a_out, amount_a_in, 500, "in_given_out_nonexploitable")
    }
}

// proptest! {
//     #![proptest_config(ProptestConfig::with_cases(1000))]
//     #[test]
//     fn buy_invariants( asset_in_reserve in asset_reserve(),
//         asset_out_reserve in asset_reserve(),
//         amount in  trade_amount()
//     ) {
//         let amount_in = crate::lbp::calculate_in_given_out(asset_out_reserve, asset_in_reserve, amount).unwrap();
//
//         assert_asset_invariant((asset_in_reserve, asset_out_reserve),
//             (asset_in_reserve + amount_in, asset_out_reserve - amount),
//             FixedU128::from((TOLERANCE,ONE)),
//             "in given out"
//         );
//     }
// }