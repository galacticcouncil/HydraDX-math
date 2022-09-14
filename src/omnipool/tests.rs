use crate::omnipool::types::{AssetReserveState, BalanceUpdate, Position};
use crate::omnipool::{
    calculate_add_liquidity_state_changes, calculate_asset_tvl, calculate_buy_for_hub_asset_state_changes,
    calculate_buy_state_changes, calculate_delta_imbalance, calculate_remove_liquidity_state_changes,
    calculate_sell_hub_state_changes, calculate_sell_state_changes,
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
        tvl: 20 * UNIT,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
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
        tvl: 20 * UNIT,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
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
        tvl: 20 * UNIT,
    };

    let amount_to_sell = 4 * UNIT;
    let asset_fee = Permill::from_percent(0);

    let state_changes = calculate_sell_hub_state_changes(&asset_state, amount_to_sell, asset_fee);

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
        BalanceUpdate::Decrease(7333333333333u128)
    );
}

#[test]
fn calculate_sell_hub_asset_with_fee_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
    };

    let amount_to_sell = 4 * UNIT;
    let asset_fee = Permill::from_percent(1);

    let state_changes = calculate_sell_hub_state_changes(&asset_state, amount_to_sell, asset_fee);

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
        BalanceUpdate::Decrease(7299999999999u128)
    );
}

#[test]
fn calculate_buy_should_work_when_correct_input_provided() {
    let asset_in_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
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
        tvl: 20 * UNIT,
    };
    let asset_out_state = AssetReserveState {
        reserve: 5 * UNIT,
        hub_reserve: 5 * UNIT,
        shares: 20 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
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
        tvl: 20 * UNIT,
    };

    let amount_to_buy = 2 * UNIT;
    let asset_fee = Permill::from_percent(0);

    let state_changes = calculate_buy_for_hub_asset_state_changes(&asset_state, amount_to_buy, asset_fee);

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
        BalanceUpdate::Decrease(9000000000001u128)
    );
}

#[test]
fn calculate_buy_for_hub_asset_with_fee_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
    };

    let amount_to_buy = 2 * UNIT;
    let asset_fee = Permill::from_percent(1);

    let state_changes = calculate_buy_for_hub_asset_state_changes(&asset_state, amount_to_buy, asset_fee);

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
        BalanceUpdate::Decrease(9063291139240u128)
    );
}

#[test]
fn calculate_add_liquidity_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
    };

    let amount_to_add = 2 * UNIT;
    let state_asset = (6 * UNIT, 12 * UNIT);

    let state_changes = calculate_add_liquidity_state_changes(&asset_state, amount_to_add, state_asset, false);

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

    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Decrease(2000000000000u128) // TOOD: really ?
    );

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
        tvl: 20 * UNIT,
    };

    let amount_to_remove = 2 * UNIT;
    let state_asset = (6 * UNIT, 12 * UNIT);

    let position = Position {
        amount: 3 * UNIT,
        shares: 3 * UNIT,
        price: FixedU128::from_float(0.23),
    };

    let state_changes =
        calculate_remove_liquidity_state_changes(&asset_state, amount_to_remove, &position, state_asset, false);

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
    assert_eq!(
        state_changes.asset.delta_tvl,
        BalanceUpdate::Decrease(12000000000000u128)
    );
    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Increase(2000000000000u128)
    );

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
        tvl: 20 * UNIT,
    };

    let amount_to_remove = 2 * UNIT;
    let state_asset = (6 * UNIT, 12 * UNIT);

    let position = Position {
        amount: 3 * UNIT,
        shares: 3 * UNIT,
        price: FixedU128::from_float(2.23),
    };

    let state_changes =
        calculate_remove_liquidity_state_changes(&asset_state, amount_to_remove, &position, state_asset, false);

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
        BalanceUpdate::Decrease(1891252955082u128) // TODO: why different to amount as parameter ?
    );
    assert_eq!(
        state_changes.asset.delta_protocol_shares,
        BalanceUpdate::Increase(108747044918u128)
    );
    assert_eq!(
        state_changes.asset.delta_tvl,
        BalanceUpdate::Decrease(11891252955082u128)
    );
    assert_eq!(
        state_changes.delta_imbalance,
        BalanceUpdate::Increase(1891252955082u128)
    );

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
fn calculate_delta_imbalance_should_work_when_correct_input_provided() {
    let asset_state = AssetReserveState {
        reserve: 10 * UNIT,
        hub_reserve: 20 * UNIT,
        shares: 10 * UNIT,
        protocol_shares: 0u128,
        tvl: 20 * UNIT,
    };

    let amount = 2 * UNIT;
    let imbalance = UNIT;
    let hub_reserve = 11 * UNIT;

    let delta_imbalance = calculate_delta_imbalance(&asset_state, amount, imbalance, hub_reserve);

    assert!(delta_imbalance.is_some());

    let delta_imbalance = delta_imbalance.unwrap();

    assert_eq!(delta_imbalance, 363636363636u128);
}

#[test]
fn calculate_tvl_should_work_when_correct_input_provided() {
    let hub_reserve = 2 * UNIT;
    let state_asset = (6 * UNIT, 12 * UNIT);

    let delta_tvl = calculate_asset_tvl(hub_reserve, state_asset);

    assert!(delta_tvl.is_some());

    let delta_tvl = delta_tvl.unwrap();

    assert_eq!(delta_tvl, 1000000000000u128);
}
