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

pub struct SubpoolState<'a> {
    pub reserves: &'a [Balance],
    pub amplification: Balance,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SubpoolStateChange {
    pub idx: usize,
    pub amount: BalanceUpdate<Balance>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TradeResult {
    pub asset_in: SubpoolStateChange,
    pub asset_out: SubpoolStateChange,
    pub iso_pool: TradeStateChange<Balance>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct MixedTradeResult {
    pub subpool: SubpoolStateChange,
    pub isopool: TradeStateChange<Balance>,
}
#[derive(Debug)]
pub struct MixedTradeHubResult {
    pub subpool: SubpoolStateChange,
    pub isopool: HubTradeStateChange<Balance>,
}

pub fn calculate_sell_between_subpools(
    pool_in: SubpoolState,
    pool_out: SubpoolState,
    idx_in: usize,
    idx_out: usize,
    amount_in: Balance,
    share_state_in: &AssetReserveState<Balance>,
    share_state_out: &AssetReserveState<Balance>,
    share_issuance_in: Balance,
    share_issuance_out: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<TradeResult> {
    if idx_in >= pool_in.reserves.len() || idx_out >= pool_out.reserves.len() {
        return None;
    }

    let delta_u = calculate_shares_for_amount::<MAX_D_ITERATIONS>(
        &pool_in.reserves,
        idx_in,
        amount_in,
        pool_in.amplification,
        share_issuance_in,
    )?;

    let sell_changes = calculate_sell_state_changes(
        share_state_in,
        share_state_out,
        delta_u,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;

    let (delta_t_j, f) = calculate_withdraw_one_asset::<MAX_D_ITERATIONS, MAX_Y_ITERATIONS>(
        &pool_out.reserves,
        *sell_changes.asset_out.delta_reserve,
        idx_out,
        share_issuance_out,
        pool_out.amplification,
        withdraw_fee,
    )?;

    let delta_t_j = delta_t_j.checked_sub(f)?;

    Some(TradeResult {
        asset_in: SubpoolStateChange {
            idx: idx_in,
            amount: BalanceUpdate::Increase(amount_in),
        },
        asset_out: SubpoolStateChange {
            idx: idx_out,
            amount: BalanceUpdate::Decrease(delta_t_j),
        },
        iso_pool: sell_changes,
    })
}

pub fn calculate_buy_between_subpools(
    pool_in: SubpoolState,
    pool_out: SubpoolState,
    idx_in: usize,
    idx_out: usize,
    amount_out: Balance,
    share_state_in: &AssetReserveState<Balance>,
    share_state_out: &AssetReserveState<Balance>,
    share_issuance_in: Balance,
    share_issuance_out: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<TradeResult> {
    if idx_in >= pool_in.reserves.len() || idx_out >= pool_out.reserves.len() {
        return None;
    }
    let delta_u = calculate_shares_removed::<MAX_D_ITERATIONS>(
        &pool_out.reserves,
        idx_out,
        amount_out,
        pool_out.amplification,
        share_issuance_out,
        withdraw_fee,
    )?;

    let buy_changes = calculate_buy_state_changes(
        share_state_in,
        share_state_out,
        delta_u,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;
    let delta_t_j = calculate_amount_to_add_for_shares::<MAX_D_ITERATIONS>(
        &pool_in.reserves,
        idx_in,
        *buy_changes.asset_in.delta_reserve,
        pool_in.amplification,
        share_issuance_in,
    )?;

    Some(TradeResult {
        asset_in: SubpoolStateChange {
            idx: idx_in,
            amount: BalanceUpdate::Increase(delta_t_j),
        },
        asset_out: SubpoolStateChange {
            idx: idx_out,
            amount: BalanceUpdate::Decrease(amount_out),
        },
        iso_pool: buy_changes,
    })
}

pub fn calculate_stable_out_given_iso_in(
    pool_out: SubpoolState,
    idx_out: usize,
    asset_state_in: &AssetReserveState<Balance>,
    share_state: &AssetReserveState<Balance>,
    share_issuance: Balance,
    amount_in: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<MixedTradeResult> {
    if idx_out >= pool_out.reserves.len() {
        return None;
    }

    let sell_changes = calculate_sell_state_changes(
        asset_state_in,
        share_state,
        amount_in,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;

    let (delta_t_j, f) = calculate_withdraw_one_asset::<MAX_D_ITERATIONS, MAX_Y_ITERATIONS>(
        &pool_out.reserves,
        *sell_changes.asset_out.delta_reserve,
        idx_out,
        share_issuance,
        pool_out.amplification,
        withdraw_fee,
    )?;

    let delta_t_j = delta_t_j.checked_sub(f)?;

    Some(MixedTradeResult {
        subpool: SubpoolStateChange {
            idx: idx_out,
            amount: BalanceUpdate::Increase(delta_t_j),
        },
        isopool: sell_changes,
    })
}

pub fn calculate_stable_out_given_hub_asset_in(
    pool_out: SubpoolState,
    idx_out: usize,
    share_state: &AssetReserveState<Balance>,
    share_issuance: Balance,
    amount_in: Balance,
    asset_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
    total_hub_reserve: Balance,
) -> Option<MixedTradeHubResult> {
    if idx_out >= pool_out.reserves.len() {
        return None;
    }

    let sell_changes = calculate_sell_hub_state_changes(
        share_state,
        amount_in,
        asset_fee,
        I129 {
            value: imbalance,
            negative: true,
        },
        total_hub_reserve,
    )?;

    let (delta_t_j, f) = calculate_withdraw_one_asset::<MAX_D_ITERATIONS, MAX_Y_ITERATIONS>(
        &pool_out.reserves,
        *sell_changes.asset.delta_reserve,
        idx_out,
        share_issuance,
        pool_out.amplification,
        withdraw_fee,
    )?;

    let delta_t_j = delta_t_j.checked_sub(f)?;

    Some(MixedTradeHubResult {
        subpool: SubpoolStateChange {
            idx: idx_out,
            amount: BalanceUpdate::Increase(delta_t_j),
        },
        isopool: sell_changes,
    })
}

pub fn calculate_iso_out_given_stable_in(
    pool_in: SubpoolState,
    idx_in: usize,
    asset_state_out: &AssetReserveState<Balance>,
    share_state: &AssetReserveState<Balance>,
    share_issuance: Balance,
    amount_in: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    _withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<MixedTradeResult> {
    if idx_in >= pool_in.reserves.len() {
        return None;
    }

    let delta_u = calculate_shares_for_amount::<MAX_D_ITERATIONS>(
        &pool_in.reserves,
        idx_in,
        amount_in,
        pool_in.amplification,
        share_issuance,
    )?;

    let sell_changes = calculate_sell_state_changes(
        share_state,
        asset_state_out,
        delta_u,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;

    Some(MixedTradeResult {
        subpool: SubpoolStateChange {
            idx: idx_in,
            amount: BalanceUpdate::Increase(amount_in),
        },
        isopool: sell_changes,
    })
}

pub fn calculate_iso_in_given_stable_out(
    pool_out: SubpoolState,
    idx_out: usize,
    asset_state_in: &AssetReserveState<Balance>,
    share_state: &AssetReserveState<Balance>,
    share_issuance: Balance,
    amount_out: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<MixedTradeResult> {
    let delta_u = calculate_shares_removed::<MAX_D_ITERATIONS>(
        &pool_out.reserves,
        idx_out,
        amount_out,
        pool_out.amplification,
        share_issuance,
        withdraw_fee,
    )?;

    let buy_changes =
        calculate_buy_state_changes(asset_state_in, share_state, delta_u, asset_fee, protocol_fee, imbalance)?;

    Some(MixedTradeResult {
        subpool: SubpoolStateChange {
            idx: idx_out,
            amount: BalanceUpdate::Decrease(amount_out),
        },
        isopool: buy_changes,
    })
}

pub fn calculate_hub_asset_in_given_stable_out(
    pool_out: SubpoolState,
    idx_out: usize,
    share_state: &AssetReserveState<Balance>,
    share_issuance: Balance,
    amount_out: Balance,
    asset_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
    total_hub_reserve: Balance,
) -> Option<MixedTradeHubResult> {
    let delta_u = calculate_shares_removed::<MAX_D_ITERATIONS>(
        &pool_out.reserves,
        idx_out,
        amount_out,
        pool_out.amplification,
        share_issuance,
        withdraw_fee,
    )?;

    let buy_changes = calculate_buy_for_hub_asset_state_changes(
        share_state,
        delta_u,
        asset_fee,
        I129 {
            value: imbalance,
            negative: true,
        },
        total_hub_reserve,
    )?;

    Some(MixedTradeHubResult {
        subpool: SubpoolStateChange {
            idx: idx_out,
            amount: BalanceUpdate::Decrease(amount_out),
        },
        isopool: buy_changes,
    })
}

pub fn calculate_stable_in_given_iso_out(
    pool_in: SubpoolState,
    idx_in: usize,
    asset_state_out: &AssetReserveState<Balance>,
    share_state: &AssetReserveState<Balance>,
    share_issuance: Balance,
    amount_out: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<MixedTradeResult> {
    let buy_changes = calculate_buy_state_changes(
        share_state,
        asset_state_out,
        amount_out,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;

    let delta_t_j = calculate_amount_to_add_for_shares::<MAX_D_ITERATIONS>(
        &pool_in.reserves,
        idx_in,
        *buy_changes.asset_in.delta_reserve,
        pool_in.amplification,
        share_issuance,
    )?;

    Some(MixedTradeResult {
        subpool: SubpoolStateChange {
            idx: idx_in,
            amount: BalanceUpdate::Increase(delta_t_j),
        },
        isopool: buy_changes,
    })
}

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
