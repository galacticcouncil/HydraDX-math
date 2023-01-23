#![allow(clippy::too_many_arguments)]

use crate::omnipool::types::{
    AssetReserveState, AssetStateChange, BalanceUpdate, HubTradeStateChange, Position, TradeStateChange, I129,
};
use crate::omnipool::{
    calculate_buy_for_hub_asset_state_changes, calculate_buy_state_changes, calculate_sell_hub_state_changes,
    calculate_sell_state_changes,
};
use crate::stableswap::{
    calculate_amount_to_add_for_shares, calculate_d, calculate_shares_for_amount, calculate_shares_removed,
    calculate_withdraw_one_asset, calculate_y,
};
use crate::stableswap::{MAX_D_ITERATIONS, MAX_Y_ITERATIONS};
use crate::support::traits::{CheckedDivInner, CheckedMulInner, CheckedMulInto, Convert};
use crate::types::Balance;
use num_traits::{CheckedDiv, CheckedSub, One};
use sp_arithmetic::{FixedPointNumber, FixedU128, Permill};

pub struct MigrationDetails {
    pub price: (Balance, Balance),
    pub shares: Balance,
    pub hub_reserve: Balance,
    pub share_tokens: Balance,
}

pub fn convert_position(position: Position<Balance>, details: MigrationDetails) -> Option<Position<Balance>> {
    let shares = position
        .shares
        .checked_mul_into(&details.hub_reserve)?
        .checked_div_inner(&details.shares)?
        .try_to_inner()?;

    let amount = position
        .amount
        .checked_mul_into(&details.share_tokens)?
        .checked_div_inner(&details.shares)?
        .try_to_inner()?;

    let nominator = position.price.0.checked_mul_into(&details.price.1)?.fit_to_inner();
    let denom = position.price.1.checked_mul_into(&details.price.0)?.fit_to_inner();

    Some(Position {
        shares,
        amount,
        price: (nominator, denom),
    })
}

pub fn create_new_subpool(
    asset_state_a: &AssetReserveState<Balance>,
    asset_state_b: &AssetReserveState<Balance>,
) -> Option<AssetReserveState<Balance>> {
    let hub_reserve = asset_state_a.hub_reserve.checked_add(asset_state_b.hub_reserve)?;

    let protocol_shares = recalculate_protocol_shares(
        asset_state_a.hub_reserve,
        asset_state_a.shares,
        asset_state_a.protocol_shares,
    )?
    .checked_add(recalculate_protocol_shares(
        asset_state_b.hub_reserve,
        asset_state_b.shares,
        asset_state_b.protocol_shares,
    )?)?;

    let shares = hub_reserve;
    let reserve = shares;

    Some(AssetReserveState {
        reserve,
        hub_reserve,
        shares,
        protocol_shares,
    })
}

pub fn calculate_asset_migration_details(
    asset_state: &AssetReserveState<Balance>,
    subpool_state: Option<&AssetReserveState<Balance>>,
    share_issuance: Balance,
) -> Option<(MigrationDetails, Option<AssetStateChange<Balance>>)> {
    if let Some(subpool_state) = subpool_state {
        let p1 = subpool_state
            .shares
            .checked_mul_into(&asset_state.hub_reserve)?
            .checked_div_inner(&subpool_state.hub_reserve)?;
        let p2 = p1
            .checked_mul_inner(&asset_state.protocol_shares)?
            .checked_div_inner(&asset_state.shares)?;
        let delta_ps = p2.try_to_inner()?;

        let delta_s = asset_state
            .hub_reserve
            .checked_mul_into(&subpool_state.shares)?
            .checked_div_inner(&subpool_state.hub_reserve)?
            .try_to_inner()?;

        let delta_u = asset_state
            .hub_reserve
            .checked_mul_into(&share_issuance)?
            .checked_div_inner(&subpool_state.hub_reserve)?
            .try_to_inner()?;

        // price = asset price * share_issuance / pool shares
        // price = (hub reserve / reserve ) * share issuance / pool shares
        // price = hub*issuance / reserve * pool shares
        let price_denom = asset_state
            .reserve
            .checked_mul_into(&subpool_state.shares)?
            .fit_to_inner();

        let price_num = asset_state
            .hub_reserve
            .checked_mul_into(&share_issuance)?
            .fit_to_inner();

        let delta_q = asset_state.hub_reserve;

        Some((
            MigrationDetails {
                price: (price_num, price_denom),
                shares: asset_state.shares,
                hub_reserve: delta_q,
                share_tokens: delta_u,
            },
            Some(AssetStateChange {
                delta_reserve: BalanceUpdate::Increase(delta_u),
                delta_hub_reserve: BalanceUpdate::Increase(delta_q),
                delta_shares: BalanceUpdate::Increase(delta_s),
                delta_protocol_shares: BalanceUpdate::Increase(delta_ps),
            }),
        ))
    } else {
        // This case if when subpool is being created
        Some((
            MigrationDetails {
                price: asset_state.price_as_rational(),
                shares: asset_state.shares,
                hub_reserve: asset_state.hub_reserve,
                share_tokens: asset_state.hub_reserve,
            },
            None,
        ))
    }
}

pub fn recalculate_protocol_shares(hub_reserve: Balance, shares: Balance, protocol_shares: Balance) -> Option<Balance> {
    hub_reserve
        .checked_mul_into(&protocol_shares)?
        .checked_div_inner(&shares)?
        .try_to_inner()
}
