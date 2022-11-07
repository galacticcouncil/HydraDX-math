use crate::omnipool::calculate_sell_state_changes;
use crate::omnipool::types::AssetReserveState;
use crate::stableswap::{calculate_d, calculate_y};
use crate::stableswap::{MAX_D_ITERATIONS, MAX_Y_ITERATIONS};
use crate::types::Balance;
use sp_arithmetic::Permill;

pub struct SubpoolState<'a> {
    reserves: &'a [Balance],
    amplification: Balance,
}

pub fn calculate_sell_between_subpools(
    pool_in: &SubpoolState,
    pool_out: &SubpoolState,
    idx_in: usize,
    idx_out: usize,
    amount_in: Balance,
    share_state_in: &AssetReserveState<Balance>,
    share_state_out: &AssetReserveState<Balance>,
    share_issuance: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    imbalance: Balance,
) -> Option<Balance> {
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

    let delta_u = share_issuance.checked_mul(delta_d)?.checked_div(initial_d)?; // TODO: higher precision needed?

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
    let fee_w = 0u128;
    let delta_d = initial_out_d * delta_u_t / share_state_out.reserve * (1 - fee_w);

    let d_plus = initial_out_d - delta_d;
    let xp: Vec<Balance> = pool_out.reserves 
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_out)
        .map(|(_, v)| *v )
        .collect();

    let delta_t_j = calculate_y::<MAX_Y_ITERATIONS>(&xp, d_plus, pool_out.amplification)?;

    Some(delta_t_j) //TODO: return lof of more info
}
