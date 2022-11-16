#![allow(clippy::too_many_arguments)]

use crate::omnipool::types::{AssetReserveState, BalanceUpdate, Position, TradeStateChange};
use crate::omnipool::{calculate_buy_state_changes, calculate_sell_state_changes};
use crate::omnipool_subpools::types::{CheckedMathInner, HpCheckedMath};
use crate::stableswap::{calculate_d, calculate_y};
use crate::stableswap::{MAX_D_ITERATIONS, MAX_Y_ITERATIONS};
use crate::types::Balance;
use num_traits::{CheckedDiv, One};
use sp_arithmetic::{FixedPointNumber, FixedU128, Permill};

pub struct SubpoolState<'a> {
    pub reserves: &'a [Balance],
    pub amplification: Balance,
}

pub struct SubpoolStateChange {
    pub idx: usize,
    pub amount: BalanceUpdate<Balance>,
}

pub struct TradeResult {
    pub asset_in: SubpoolStateChange,
    pub asset_out: SubpoolStateChange,
    pub iso_pool: TradeStateChange<Balance>,
}

pub struct MixedTradeResult {
    pub subpool: SubpoolStateChange,
    pub isopool: TradeStateChange<Balance>,
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
    asset_fee: Permill,
    protocol_fee: Permill,
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<TradeResult> {
    if idx_in >= pool_in.reserves.len() || idx_out >= pool_out.reserves.len() {
        return None;
    }

    let initial_d = calculate_d::<MAX_D_ITERATIONS>(pool_in.reserves, pool_in.amplification)?;

    let new_reserve_in = pool_in.reserves[idx_in].checked_add(amount_in)?;

    let updated_reserves: Vec<Balance> = pool_in
        .reserves
        .iter()
        .enumerate()
        .map(|(idx, v)| if idx == idx_in { new_reserve_in } else { *v })
        .collect();

    let d_plus = calculate_d::<MAX_D_ITERATIONS>(&updated_reserves, pool_in.amplification)?;

    let delta_d = d_plus.checked_sub(initial_d)?;

    let delta_u = share_issuance_in
        .hp_checked_mul(&delta_d)?
        .checked_div_inner(&initial_d)?
        .to_inner()?;

    let sell_changes = calculate_sell_state_changes(
        share_state_in,
        share_state_out,
        delta_u,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;

    let initial_out_d = calculate_d::<MAX_D_ITERATIONS>(pool_out.reserves, pool_out.amplification)?;

    let delta_u_t = *sell_changes.asset_out.delta_reserve;
    let fee_w = FixedU128::from(withdraw_fee);
    let delta_d = initial_out_d * delta_u_t
        / (FixedU128::one() - fee_w)
            .checked_mul_int(share_state_out.reserve)
            .unwrap();

    let d_plus = initial_out_d - delta_d;
    let xp: Vec<Balance> = pool_out
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_out)
        .map(|(_, v)| *v)
        .collect();

    let delta_t_j = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_out.amplification)?;

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

    let fee_w = FixedU128::from(withdraw_fee);

    let initial_d = calculate_d::<MAX_D_ITERATIONS>(pool_out.reserves, pool_out.amplification)?;

    let new_reserve_out = pool_out.reserves[idx_out].checked_sub(amount_out)?;

    let updated_reserves: Vec<Balance> = pool_out
        .reserves
        .iter()
        .enumerate()
        .map(|(idx, v)| if idx == idx_out { new_reserve_out } else { *v })
        .collect();

    let d_plus = calculate_d::<MAX_D_ITERATIONS>(&updated_reserves, pool_out.amplification)?;

    let delta_d = d_plus.checked_sub(initial_d)?;

    let delta_u = (FixedU128::one() / (FixedU128::one() - fee_w))
        .checked_mul_int(share_issuance_out * delta_d / initial_d)
        .unwrap();

    let buy_changes = calculate_buy_state_changes(
        share_state_in,
        share_state_out,
        delta_u,
        asset_fee,
        protocol_fee,
        imbalance,
    )?;

    let initial_in_d = calculate_d::<MAX_D_ITERATIONS>(pool_in.reserves, pool_in.amplification)?;

    let delta_u_t = *buy_changes.asset_in.delta_reserve;
    let delta_d = initial_in_d * ((delta_u_t + share_issuance_in) / share_issuance_in);

    let d_plus = initial_in_d + delta_d;
    let xp: Vec<Balance> = pool_in
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_in)
        .map(|(_, v)| *v)
        .collect();

    let delta_t_j = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_in.amplification)?;

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
    None
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
    withdraw_fee: Permill,
    imbalance: Balance,
) -> Option<MixedTradeResult> {
    if idx_in >= pool_in.reserves.len() {
        return None;
    }

    let initial_d = calculate_d::<MAX_D_ITERATIONS>(pool_in.reserves, pool_in.amplification)?;

    let new_reserve_in = pool_in.reserves[idx_in].checked_add(amount_in)?;

    let updated_reserves: Vec<Balance> = pool_in
        .reserves
        .iter()
        .enumerate()
        .map(|(idx, v)| if idx == idx_in { new_reserve_in } else { *v })
        .collect();

    let d_plus = calculate_d::<MAX_D_ITERATIONS>(&updated_reserves, pool_in.amplification)?;

    let delta_d = d_plus.checked_sub(initial_d)?;

    let delta_u = share_issuance
        .hp_checked_mul(&delta_d)?
        .checked_div_inner(&initial_d)?
        .to_inner()?;

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
    let fee_w = FixedU128::from(withdraw_fee);

    let initial_d = calculate_d::<MAX_D_ITERATIONS>(pool_out.reserves, pool_out.amplification)?;

    let new_reserve_out = pool_out.reserves[idx_out].checked_sub(amount_out)?;

    let updated_reserves: Vec<Balance> = pool_out
        .reserves
        .iter()
        .enumerate()
        .map(|(idx, v)| if idx == idx_out { new_reserve_out } else { *v })
        .collect();

    let d_plus = calculate_d::<MAX_D_ITERATIONS>(&updated_reserves, pool_out.amplification)?;

    let delta_d = d_plus.checked_sub(initial_d)?;

    let delta_u = (FixedU128::one() / (FixedU128::one() - fee_w))
        .checked_mul_int(share_issuance * delta_d / initial_d)
        .unwrap();

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
    None
}

pub struct MigrationDetails {
    pub price: FixedU128,
    pub shares: Balance,
    pub hub_reserve: Balance,
    pub share_tokens: Balance,
}

pub fn convert_position(position: Position<Balance>, details: MigrationDetails) -> Option<Position<Balance>> {
    let shares = position
        .shares
        .hp_checked_mul(&details.hub_reserve)?
        .checked_div_inner(&details.shares)?
        .to_inner()?;

    let amount = position
        .amount
        .hp_checked_mul(&details.share_tokens)?
        .checked_div_inner(&details.shares)?
        .to_inner()?;
    let price = position.price.checked_div(&details.price)?;

    Some(Position { shares, amount, price })
}
