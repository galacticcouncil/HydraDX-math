use crate::omnipool::types::{AssetReserveState, BalanceUpdate, Position, I129};
use crate::omnipool::{
    calculate_add_liquidity_state_changes, calculate_buy_for_hub_asset_state_changes, calculate_buy_state_changes,
    calculate_delta_imbalance, calculate_remove_liquidity_state_changes, calculate_sell_hub_state_changes,
    calculate_sell_state_changes,
};
use crate::types::Balance;
use sp_arithmetic::{FixedU128, Permill};

const UNIT: Balance = 1_000_000_000_000;

#[test]
fn calculate_sell_should_work_when_correct_input_provided() {
    let asset_in_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_sell = 4 * UNIT;
    let asset_fee = Permill::from_percent(0);
    let protocol_fee = Permill::from_percent(0);
    let imbalance = 2 * UNIT;

    let state_changes = calculate_sell_state_changes(
        &asset_in_state,
        &asset_out_state,
        amount_to_sell,
        asset_fee,
        protocol_fee,
        imbalance,
    );

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset_in.delta_reserve,
        BalanceUpdate::Increase(4000000000000u128)
    );
    assert_eq!(
        state_changes.asset_in.delta_hub_reserve,
        BalanceUpdate::Decrease(5714285714285u128)
    );

    assert_eq!(
        state_changes.asset_out.delta_reserve,
        BalanceUpdate::Decrease(2666666666666u128)
    );
    assert_eq!(
        state_changes.asset_out.delta_hub_reserve,
        BalanceUpdate::Increase(5714285714285u128)
    );
    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Decrease(0u128));
    assert_eq!(state_changes.hdx_hub_amount, 0u128);
}

#[test]
fn calculate_sell_with_fees_should_work_when_correct_input_provided() {
    let asset_in_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_sell = 4 * UNIT;
    let asset_fee = Permill::from_percent(1);
    let protocol_fee = Permill::from_percent(1);
    let imbalance = 2 * UNIT;

    let state_changes = calculate_sell_state_changes(
        &asset_in_state,
        &asset_out_state,
        amount_to_sell,
        asset_fee,
        protocol_fee,
        imbalance,
    );

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset_in.delta_reserve,
        BalanceUpdate::Increase(4000000000000u128)
    );
    assert_eq!(
        state_changes.asset_in.delta_hub_reserve,
        BalanceUpdate::Decrease(5714285714285u128)
    );

    assert_eq!(
        state_changes.asset_out.delta_reserve,
        BalanceUpdate::Decrease(2627613941018u128)
    );
    assert_eq!(
        state_changes.asset_out.delta_hub_reserve,
        BalanceUpdate::Increase(5657142857143u128)
    );
    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Decrease(57142857142u128));
    assert_eq!(state_changes.hdx_hub_amount, 0u128);

    // Verify if fee + delta amount == delta with fee
    let f = 57142857142u128 + 5657142857143u128;
    let no_fees_amount: Balance = *state_changes.asset_in.delta_hub_reserve;
    assert_eq!(f, no_fees_amount);
}

#[test]
fn calculate_sell_hub_asset_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_sell = 4 * UNIT;
    let asset_fee = Permill::from_percent(0);
    let imbalance = I129 {
        value: 2 * UNIT,
        negative: true,
    };
    let total_hub_reserve = 40 * UNIT;

    let state_changes =
        calculate_sell_hub_state_changes(&asset_state, amount_to_sell, asset_fee, imbalance, total_hub_reserve);

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Decrease(1666666666666u128)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Increase(amount_to_sell)
    );

    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Decrease(12972222222221u128)
    );
}

#[test]
fn calculate_sell_hub_asset_with_fee_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_sell = 4 * UNIT;
    let asset_fee = Permill::from_percent(1);
    let imbalance = I129 {
        value: 2 * UNIT,
        negative: true,
    };
    let total_hub_reserve = 40 * UNIT;

    let state_changes =
        calculate_sell_hub_state_changes(&asset_state, amount_to_sell, asset_fee, imbalance, total_hub_reserve);

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Decrease(1649999999999u128)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Increase(amount_to_sell)
    );

    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Decrease(12914166666664u128)
    );
}

#[test]
fn calculate_buy_should_work_when_correct_input_provided() {
    let asset_in_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_buy = UNIT;
    let asset_fee = Permill::from_percent(0);
    let protocol_fee = Permill::from_percent(0);
    let imbalance = 2 * UNIT;

    let state_changes = calculate_buy_state_changes(
        &asset_in_state,
        &asset_out_state,
        amount_to_buy,
        asset_fee,
        protocol_fee,
        imbalance,
    );

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset_in.delta_reserve,
        BalanceUpdate::Increase(666666666668u128)
    );
    assert_eq!(
        state_changes.asset_in.delta_hub_reserve,
        BalanceUpdate::Decrease(1250000000001u128)
    );

    assert_eq!(
        state_changes.asset_out.delta_reserve,
        BalanceUpdate::Decrease(amount_to_buy)
    );
    assert_eq!(
        state_changes.asset_out.delta_hub_reserve,
        BalanceUpdate::Increase(1250000000001u128)
    );
    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Decrease(0u128));
    assert_eq!(state_changes.hdx_hub_amount, 0u128);
}

#[test]
fn calculate_buy_with_fees_should_work_when_correct_input_provided() {
    let asset_in_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_buy = UNIT;
    let asset_fee = Permill::from_percent(1);
    let protocol_fee = Permill::from_percent(1);
    let imbalance = 2 * UNIT;

    let state_changes = calculate_buy_state_changes(
        &asset_in_state,
        &asset_out_state,
        amount_to_buy,
        asset_fee,
        protocol_fee,
        imbalance,
    );

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset_in.delta_reserve,
        BalanceUpdate::Increase(682966807814u128)
    );
    assert_eq!(
        state_changes.asset_in.delta_hub_reserve,
        BalanceUpdate::Decrease(1278608873546)
    );

    assert_eq!(
        state_changes.asset_out.delta_reserve,
        BalanceUpdate::Decrease(amount_to_buy)
    );
    assert_eq!(
        state_changes.asset_out.delta_hub_reserve,
        BalanceUpdate::Increase(1265822784811u128)
    );
    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Decrease(12786088735u128));
    assert_eq!(state_changes.hdx_hub_amount, 0u128);

    // Verify if fee + delta amount == delta with fee
    let f = 1265822784811u128 + 12786088735u128;
    let no_fees_amount: Balance = *state_changes.asset_in.delta_hub_reserve;
    assert_eq!(f, no_fees_amount);
}

#[test]
fn calculate_buy_for_hub_asset_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_buy = 2 * UNIT;
    let asset_fee = Permill::from_percent(0);
    let imbalance = I129 {
        value: 2 * UNIT,
        negative: true,
    };
    let total_hub_reserve = 40 * UNIT;

    let state_changes =
        calculate_buy_for_hub_asset_state_changes(&asset_state, amount_to_buy, asset_fee, imbalance, total_hub_reserve);

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Decrease(amount_to_buy)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Increase(5000000000001u128)
    );

    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Decrease(15640000000002u128)
    );
}

#[test]
fn calculate_buy_for_hub_asset_with_fee_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_buy = 2 * UNIT;
    let asset_fee = Permill::from_percent(1);
    let imbalance = I129 {
        value: 2 * UNIT,
        negative: true,
    };
    let total_hub_reserve = 40 * UNIT;

    let state_changes =
        calculate_buy_for_hub_asset_state_changes(&asset_state, amount_to_buy, asset_fee, imbalance, total_hub_reserve);

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Decrease(amount_to_buy)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Increase(5063291139241u128)
    );

    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Decrease(15733998209949u128)
    );
}

#[test]
fn calculate_add_liquidity_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_add = 2 * UNIT;
    let imbalance = I129 {
        value: UNIT,
        negative: true,
    };
    let total_hub_reserve = 22 * UNIT;

    let state_changes =
        calculate_add_liquidity_state_changes(&asset_state, amount_to_add, imbalance, total_hub_reserve);

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Increase(amount_to_add)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Increase(4000000000000u128)
    );
    assert_eq!(state_changes.asset.delta_shares, BalanceUpdate::Increase(amount_to_add));

    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Decrease(181818181818u128));

    assert_eq!(state_changes.delta_position_reserve, BalanceUpdate::Increase(0u128),);

    assert_eq!(state_changes.delta_position_shares, BalanceUpdate::Increase(0u128));

    assert_eq!(state_changes.lp_hub_amount, 0u128);
}

#[test]
fn calculate_remove_liquidity_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_remove = 2 * UNIT;

    let imbalance = I129 {
        value: UNIT,
        negative: true,
    };
    let total_hub_reserve = 22 * UNIT;

    let position = Position {
        amount: 3 * UNIT,
        shares: 3 * UNIT,
        price: (FixedU128::from_float(0.23).into_inner(), 1_000_000_000_000_000_000),
    };

    let state_changes = calculate_remove_liquidity_state_changes(
        &asset_state,
        amount_to_remove,
        &position,
        imbalance,
        total_hub_reserve,
    );

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Decrease(amount_to_remove)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Decrease(4000000000000u128)
    );
    assert_eq!(
        state_changes.asset.delta_shares,
        BalanceUpdate::Decrease(amount_to_remove)
    );
    assert_eq!(
        state_changes.asset.delta_protocol_shares,
        BalanceUpdate::Increase(0u128)
    );
    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Increase(181818181818u128));

    assert_eq!(
        state_changes.delta_position_reserve,
        BalanceUpdate::Decrease(2000000000000u128)
    );

    assert_eq!(
        state_changes.delta_position_shares,
        BalanceUpdate::Decrease(amount_to_remove)
    );

    assert_eq!(state_changes.lp_hub_amount, 3174887892376u128);
}

#[test]
fn calculate_remove_liquidity_should_work_when_current_price_is_smaller_than_position_price() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount_to_remove = 2 * UNIT;

    let imbalance = I129 {
        value: UNIT,
        negative: true,
    };
    let total_hub_reserve = 22 * UNIT;

    let position = Position {
        amount: 3 * UNIT,
        shares: 3 * UNIT,
        price: (FixedU128::from_float(2.23).into_inner(), 1_000_000_000_000_000_000),
    };

    let state_changes = calculate_remove_liquidity_state_changes(
        &asset_state,
        amount_to_remove,
        &position,
        imbalance,
        total_hub_reserve,
    );

    assert!(state_changes.is_some());

    let state_changes = state_changes.unwrap();

    assert_eq!(
        state_changes.asset.delta_reserve,
        BalanceUpdate::Decrease(1891252955082u128)
    );
    assert_eq!(
        state_changes.asset.delta_hub_reserve,
        BalanceUpdate::Decrease(3782505910164u128)
    );
    assert_eq!(
        state_changes.asset.delta_shares,
        BalanceUpdate::Decrease(1891252955082u128)
    );
    assert_eq!(
        state_changes.asset.delta_protocol_shares,
        BalanceUpdate::Increase(108747044918u128)
    );
    assert_eq!(state_changes.delta_imbalance, BalanceUpdate::Increase(171932086825u128));

    assert_eq!(
        state_changes.delta_position_reserve,
        BalanceUpdate::Decrease(2000000000000u128)
    );

    assert_eq!(
        state_changes.delta_position_shares,
        BalanceUpdate::Decrease(amount_to_remove)
    );

    assert_eq!(state_changes.lp_hub_amount, 0u128);
}

#[test]
fn calculate_delta_imbalance_for_asset_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
    };

    let amount = 2 * UNIT;
    let imbalance = I129 {
        value: UNIT,
        negative: true,
    };
    let hub_reserve = 11 * UNIT;

    let d = asset_state.hub_reserve * amount / asset_state.reserve;

    let delta_imbalance = calculate_delta_imbalance(d, imbalance, hub_reserve);

    assert!(delta_imbalance.is_some());

    let delta_imbalance = delta_imbalance.unwrap();

    assert_eq!(delta_imbalance, 363636363636u128);
}
