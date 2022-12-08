#![allow(clippy::too_many_arguments)]

use crate::omnipool::types::{AssetReserveState, BalanceUpdate, HubTradeStateChange, Position, TradeStateChange, I129};
use crate::omnipool::{
    calculate_buy_for_hub_asset_state_changes, calculate_buy_state_changes, calculate_sell_hub_state_changes,
    calculate_sell_state_changes,
};
use crate::omnipool_subpools::types::{CheckedMathInner, HpCheckedMath};
use crate::stableswap::{calculate_d, calculate_y};
use crate::stableswap::{MAX_D_ITERATIONS, MAX_Y_ITERATIONS};
use crate::types::Balance;
use num_traits::{CheckedDiv, CheckedSub, One};
use sp_arithmetic::{FixedPointNumber, FixedU128, Permill};

pub struct SubpoolState<'a> {
    pub reserves: &'a [Balance],
    pub amplification: Balance,
}

#[derive(Debug)]
pub struct SubpoolStateChange {
    pub idx: usize,
    pub amount: BalanceUpdate<Balance>,
}

#[derive(Debug)]
pub struct TradeResult {
    pub asset_in: SubpoolStateChange,
    pub asset_out: SubpoolStateChange,
    pub iso_pool: TradeStateChange<Balance>,
}

#[derive(Debug)]
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
    let delta_d = FixedU128::one().checked_sub(&fee_w)?.checked_mul_int(
        initial_out_d
            .hp_checked_mul(&delta_u_t)?
            .checked_div_inner(&share_issuance_out)?
            .to_inner()?,
    )?;

    let d_plus = initial_out_d.checked_sub(delta_d)?;
    let xp: Vec<Balance> = pool_out
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_out)
        .map(|(_, v)| *v)
        .collect();

    let reserve_out = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_out.amplification)?;

    let delta_t_j = pool_out.reserves[idx_out].checked_sub(reserve_out)?;

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

    let delta_d = initial_d.checked_sub(d_plus)?;

    let delta_u = (FixedU128::one().checked_div(&FixedU128::one().checked_sub(&fee_w)?)?).checked_mul_int(
        share_issuance_out
            .hp_checked_mul(&delta_d)?
            .checked_div_inner(&initial_d)?
            .to_inner()?,
    )?;

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
    let d_plus = initial_in_d
        .hp_checked_mul(&delta_u_t.checked_add(share_issuance_in)?)?
        .checked_div_inner(&share_issuance_in)?
        .to_inner()?;

    let xp: Vec<Balance> = pool_in
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_in)
        .map(|(_, v)| *v)
        .collect();

    let reserve_in = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_in.amplification)?;

    let delta_t_j = reserve_in.checked_sub(pool_out.reserves[idx_out])?;

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

    let initial_out_d = calculate_d::<MAX_D_ITERATIONS>(pool_out.reserves, pool_out.amplification)?;

    let delta_u_t = *sell_changes.asset_out.delta_reserve;
    let fee_w = FixedU128::from(withdraw_fee);
    let delta_d = (FixedU128::one().checked_sub(&fee_w)?).checked_mul_int(
        initial_out_d
            .hp_checked_mul(&delta_u_t)?
            .checked_div_inner(&share_issuance)?
            .to_inner()?,
    )?;

    let d_plus = initial_out_d.checked_sub(delta_d)?;
    let xp: Vec<Balance> = pool_out
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_out)
        .map(|(_, v)| *v)
        .collect();

    let reserve_out = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_out.amplification)?;
    let delta_t_j = pool_out.reserves[idx_out].checked_sub(reserve_out)?;

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

    let initial_out_d = calculate_d::<MAX_D_ITERATIONS>(pool_out.reserves, pool_out.amplification)?;

    let delta_u_t = *sell_changes.asset.delta_reserve;
    let fee_w = FixedU128::from(withdraw_fee);
    let delta_d = (FixedU128::one().checked_sub(&fee_w)?).checked_mul_int(
        initial_out_d
            .hp_checked_mul(&delta_u_t)?
            .checked_div_inner(&share_issuance)?
            .to_inner()?,
    )?;

    let d_plus = initial_out_d.checked_sub(delta_d)?;
    let xp: Vec<Balance> = pool_out
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_out)
        .map(|(_, v)| *v)
        .collect();

    let reserve_out = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_out.amplification)?;

    let delta_t_j = pool_out.reserves[idx_out].checked_sub(reserve_out)?;

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

    let delta_d = initial_d.checked_sub(d_plus)?;

    let delta_u = (FixedU128::one().checked_div(&FixedU128::one().checked_sub(&fee_w)?))?.checked_mul_int(
        share_issuance
            .hp_checked_mul(&delta_d)?
            .checked_div_inner(&initial_d)?
            .to_inner()?,
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

    let delta_d = initial_d.checked_sub(d_plus)?;

    let delta_u = (FixedU128::one().checked_div(&FixedU128::one().checked_sub(&fee_w)?))?.checked_mul_int(
        share_issuance
            .hp_checked_mul(&delta_d)?
            .checked_div_inner(&initial_d)?
            .to_inner()?,
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
    _withdraw_fee: Permill,
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

    let initial_in_d = calculate_d::<MAX_D_ITERATIONS>(pool_in.reserves, pool_in.amplification)?;

    let delta_u_t = *buy_changes.asset_in.delta_reserve;
    let d_plus = initial_in_d
        .hp_checked_mul(&delta_u_t.checked_add(share_issuance)?)?
        .checked_div_inner(&share_issuance)?
        .to_inner()?;

    let xp: Vec<Balance> = pool_in
        .reserves
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_in)
        .map(|(_, v)| *v)
        .collect();

    let reserve_in = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_in.amplification)?;

    let delta_t_j = reserve_in.checked_sub(pool_in.reserves[idx_in])?;

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
        .hp_checked_mul(&details.hub_reserve)?
        .checked_div_inner(&details.shares)?
        .to_inner()?;

    let amount = position
        .amount
        .hp_checked_mul(&details.share_tokens)?
        .checked_div_inner(&details.shares)?
        .to_inner()?;

    let nominator = position.price.0.hp_checked_mul(&details.price.0)?.to_inner()?;
    let denom = position.price.1.hp_checked_mul(&details.price.1)?.to_inner()?;

    Some(Position { shares, amount, price: (nominator, denom)})
}
