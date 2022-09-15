use crate::omnipool::types::BalanceUpdate::{Decrease, Increase};
use crate::omnipool::types::{
    AssetReserveState, AssetStateChange, BalanceUpdate, HubTradeStateChange, LiquidityStateChange, Position,
    TradeStateChange, I129,
};
use crate::types::Balance;
use crate::MathError::Overflow;
use crate::{to_balance, to_u256};
use num_traits::{CheckedDiv, CheckedMul, CheckedSub, One, Zero};
use primitive_types::U256;
use sp_arithmetic::{FixedPointNumber, FixedU128, Permill};
use sp_std::cmp::min;
use sp_std::ops::Sub;

#[inline]
fn amount_without_fee(amount: Balance, fee: Permill) -> Option<Balance> {
    Some(Permill::from_percent(100).checked_sub(&fee)?.mul_floor(amount))
}

/// Calculate delta changes of a sell trade given current state of asset in and out.
pub fn calculate_sell_state_changes(
    asset_in_state: &AssetReserveState<Balance>,
    asset_out_state: &AssetReserveState<Balance>,
    amount: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    imbalance: Balance,
) -> Option<TradeStateChange<Balance>> {
    let (in_hub_reserve, in_reserve, in_amount) = to_u256!(asset_in_state.hub_reserve, asset_in_state.reserve, amount);

    let delta_hub_reserve_in = in_amount
        .checked_mul(in_hub_reserve)
        .and_then(|v| v.checked_div(in_reserve.checked_add(in_amount)?))?;

    let delta_hub_reserve_in = to_balance!(delta_hub_reserve_in).ok()?;

    let protocol_fee_amount = protocol_fee.mul_floor(delta_hub_reserve_in);

    let delta_hub_reserve_out = delta_hub_reserve_in.checked_sub(protocol_fee_amount)?;

    let (out_reserve_hp, out_hub_reserve_hp, delta_hub_reserve_out_hp) = to_u256!(
        asset_out_state.reserve,
        asset_out_state.hub_reserve,
        delta_hub_reserve_out
    );

    let delta_reserve_out = out_reserve_hp
        .checked_mul(delta_hub_reserve_out_hp)
        .and_then(|v| v.checked_div(out_hub_reserve_hp.checked_add(delta_hub_reserve_out_hp)?))?;

    let delta_reserve_out = amount_without_fee(to_balance!(delta_reserve_out).ok()?, asset_fee)?;

    let delta_imbalance = min(protocol_fee_amount, imbalance);

    let hdx_fee_amount = protocol_fee_amount.checked_sub(delta_imbalance)?;

    Some(TradeStateChange {
        asset_in: AssetStateChange {
            delta_reserve: Increase(amount),
            delta_hub_reserve: Decrease(delta_hub_reserve_in),
            ..Default::default()
        },
        asset_out: AssetStateChange {
            delta_reserve: Decrease(delta_reserve_out),
            delta_hub_reserve: Increase(delta_hub_reserve_out),
            ..Default::default()
        },
        delta_imbalance: BalanceUpdate::Decrease(delta_imbalance),
        hdx_hub_amount: hdx_fee_amount,
    })
}

/// Calculate delta changes of a sell where asset_in is Hub Asset
pub fn calculate_sell_hub_state_changes(
    asset_out_state: &AssetReserveState<Balance>,
    hub_asset_amount: Balance,
    asset_fee: Permill,
    imbalance: I129<Balance>,
    total_hub_reserve: Balance,
) -> Option<HubTradeStateChange<Balance>> {
    if !imbalance.negative {
        return None;
    }

    let (reserve_hp, hub_reserve_hp, amount_hp) =
        to_u256!(asset_out_state.reserve, asset_out_state.hub_reserve, hub_asset_amount);

    let delta_reserve_out_hp = reserve_hp
        .checked_mul(amount_hp)
        .and_then(|v| v.checked_div(hub_reserve_hp.checked_add(amount_hp)?))?;

    let delta_reserve_out = to_balance!(delta_reserve_out_hp).ok()?;
    let delta_reserve_out = amount_without_fee(delta_reserve_out, asset_fee)?;

    // IMBALANCE
    // L+ = Q+ * fixed(Ri+ / Ri) * fixed(Qi / Qi+)   +  L * fixed(Ri+ / Ri) * fixed(Qi / Qi+) * fixed(Q+ / Q)  -  Q+
    // L+ = Q+ * X1 * X2 + L *  Y1 * X2 * Y2 - Q+

    let q = total_hub_reserve;
    let r_i = asset_out_state.reserve;
    let q_i = asset_out_state.hub_reserve;

    let q_plus = total_hub_reserve.checked_add(hub_asset_amount)?;
    let r_i_plus = r_i.checked_sub(delta_reserve_out)?;
    let q_i_plus = q_i.checked_add(hub_asset_amount)?;

    let imbalance_value = imbalance.value;

    let x1 = FixedU128::checked_from_rational(r_i_plus, r_i)?;
    let x2 = FixedU128::checked_from_rational(q_i, q_i_plus)?;
    let y1 = FixedU128::checked_from_rational(r_i_plus, r_i)?;
    let y2 = FixedU128::checked_from_rational(q_plus, q)?;

    let x = x1.checked_mul(&x2)?.checked_mul_int(q_plus)?;
    let y = y1
        .checked_mul(&x2)?
        .checked_mul(&y2)?
        .checked_mul_int(imbalance_value)?;
    let imbalance_plus = q_plus.checked_sub(x.checked_sub(y)?)?;

    let delta_imbalance = imbalance_plus.checked_sub(imbalance_value)?;

    Some(HubTradeStateChange {
        asset: AssetStateChange {
            delta_reserve: Decrease(delta_reserve_out),
            delta_hub_reserve: Increase(hub_asset_amount),
            ..Default::default()
        },
        delta_imbalance: Decrease(delta_imbalance),
    })
}

/// Calculate delta changes of a buy trade where asset_in is Hub Asset
pub fn calculate_buy_for_hub_asset_state_changes(
    asset_out_state: &AssetReserveState<Balance>,
    asset_out_amount: Balance,
    asset_fee: Permill,
    imbalance: I129<Balance>,
    total_hub_reserve: Balance,
) -> Option<HubTradeStateChange<Balance>> {
    let hub_denominator = amount_without_fee(asset_out_state.reserve, asset_fee)?.checked_sub(asset_out_amount)?;

    let (hub_reserve_hp, amount_hp, hub_denominator_hp) =
        to_u256!(asset_out_state.hub_reserve, asset_out_amount, hub_denominator);

    let delta_hub_reserve_hp = hub_reserve_hp.checked_mul(amount_hp).and_then(|v| {
        v.checked_div(hub_denominator_hp)
            .and_then(|v| v.checked_add(U256::one()))
    })?;

    let delta_hub_reserve = to_balance!(delta_hub_reserve_hp).ok()?;

    // IMBALANCE
    // L+ = Q+ * fixed(Ri+ / Ri) * fixed(Qi / Qi+)   +  L * fixed(Ri+ / Ri) * fixed(Qi / Qi+) * fixed(Q+ / Q)  -  Q+
    // L+ = Q+ * X1 * X2 + L *  Y1 * X2 * Y2 - Q+

    let q = total_hub_reserve;
    let r_i = asset_out_state.reserve;
    let q_i = asset_out_state.hub_reserve;

    let q_plus = total_hub_reserve.checked_add(delta_hub_reserve)?;
    let r_i_plus = r_i.checked_sub(asset_out_amount)?;
    let q_i_plus = q_i.checked_add(delta_hub_reserve)?;

    let imbalance_value = imbalance.value;

    let x1 = FixedU128::checked_from_rational(r_i_plus, r_i)?;
    let x2 = FixedU128::checked_from_rational(q_i, q_i_plus)?;
    let y1 = FixedU128::checked_from_rational(r_i_plus, r_i)?;
    let y2 = FixedU128::checked_from_rational(q_plus, q)?;

    let x = x1.checked_mul(&x2)?.checked_mul_int(q_plus)?;
    let y = y1
        .checked_mul(&x2)?
        .checked_mul(&y2)?
        .checked_mul_int(imbalance_value)?;
    let imbalance_plus = q_plus.checked_sub(x.checked_sub(y)?)?;

    let delta_imbalance = imbalance_plus.checked_sub(imbalance_value)?;

    Some(HubTradeStateChange {
        asset: AssetStateChange {
            delta_reserve: Decrease(asset_out_amount),
            delta_hub_reserve: Increase(delta_hub_reserve),
            ..Default::default()
        },
        delta_imbalance: Decrease(delta_imbalance),
    })
}

/// Calculate delta changes of a buy trade given current state of asset in and out
pub fn calculate_buy_state_changes(
    asset_in_state: &AssetReserveState<Balance>,
    asset_out_state: &AssetReserveState<Balance>,
    amount: Balance,
    asset_fee: Permill,
    protocol_fee: Permill,
    imbalance: Balance,
) -> Option<TradeStateChange<Balance>> {
    let reserve_no_fee = amount_without_fee(asset_out_state.reserve, asset_fee)?;
    let (out_hub_reserve, out_reserve_no_fee, out_amount) =
        to_u256!(asset_out_state.hub_reserve, reserve_no_fee, amount);

    let delta_hub_reserve_out = out_hub_reserve
        .checked_mul(out_amount)
        .and_then(|v| v.checked_div(out_reserve_no_fee.checked_sub(out_amount)?))?;

    let delta_hub_reserve_out = to_balance!(delta_hub_reserve_out).ok()?;
    let delta_hub_reserve_out = delta_hub_reserve_out.checked_add(Balance::one())?;

    // Negative
    let delta_hub_reserve_in: Balance = FixedU128::from_inner(delta_hub_reserve_out)
        .checked_div(&Permill::from_percent(100).sub(protocol_fee).into())?
        .into_inner();

    if delta_hub_reserve_in >= asset_in_state.hub_reserve {
        return None;
    }

    let (delta_hub_reserve_in_hp, in_hub_reserve_hp, in_reserve_hp) =
        to_u256!(delta_hub_reserve_in, asset_in_state.hub_reserve, asset_in_state.reserve);

    let delta_reserve_in = in_reserve_hp
        .checked_mul(delta_hub_reserve_in_hp)
        .and_then(|v| v.checked_div(in_hub_reserve_hp.checked_sub(delta_hub_reserve_in_hp)?))?;

    let delta_reserve_in = to_balance!(delta_reserve_in).ok()?;
    let delta_reserve_in = delta_reserve_in.checked_add(Balance::one())?;

    // Fee accounting and imbalance
    let protocol_fee_amount = protocol_fee.mul_floor(delta_hub_reserve_in);
    let delta_imbalance = min(protocol_fee_amount, imbalance);

    let hdx_fee_amount = protocol_fee_amount.checked_sub(delta_imbalance)?;

    Some(TradeStateChange {
        asset_in: AssetStateChange {
            delta_reserve: Increase(delta_reserve_in),
            delta_hub_reserve: Decrease(delta_hub_reserve_in),
            ..Default::default()
        },
        asset_out: AssetStateChange {
            delta_reserve: Decrease(amount),
            delta_hub_reserve: Increase(delta_hub_reserve_out),
            ..Default::default()
        },
        delta_imbalance: BalanceUpdate::Decrease(delta_imbalance),
        hdx_hub_amount: hdx_fee_amount,
    })
}

/// Calculate delta changes of add liqudiity given current asset state
pub fn calculate_add_liquidity_state_changes(
    asset_state: &AssetReserveState<Balance>,
    amount: Balance,
    imbalance: I129<Balance>,
    total_hub_reserve: Balance,
) -> Option<LiquidityStateChange<Balance>> {
    let delta_hub_reserve = asset_state.price()?.checked_mul_int(amount)?;

    let (amount_hp, shares_hp, reserve_hp) = to_u256!(amount, asset_state.shares, asset_state.reserve);

    let delta_shares_hp = shares_hp
        .checked_mul(amount_hp)
        .and_then(|v| v.checked_div(reserve_hp))?;

    let delta_imbalance = calculate_delta_imbalance_for_delta(delta_hub_reserve, imbalance, total_hub_reserve)?;

    let delta_shares = to_balance!(delta_shares_hp).ok()?;

    Some(LiquidityStateChange {
        asset: AssetStateChange {
            delta_reserve: Increase(amount),
            delta_hub_reserve: Increase(delta_hub_reserve),
            delta_shares: Increase(delta_shares),
            ..Default::default()
        },
        delta_imbalance: Decrease(delta_imbalance),
        ..Default::default()
    })
}

/// Calculate delta changes of remove liqudiity given current asset state and position from which liquidity should be removed.
pub fn calculate_remove_liquidity_state_changes(
    asset_state: &AssetReserveState<Balance>,
    shares_removed: Balance,
    position: &Position<Balance>,
    imbalance: I129<Balance>,
    total_hub_reserve: Balance,
) -> Option<LiquidityStateChange<Balance>> {
    let current_shares = asset_state.shares;
    let current_reserve = asset_state.reserve;
    let current_hub_reserve = asset_state.hub_reserve;

    let current_price = asset_state.price()?;
    let position_price = position.price;

    let (
        current_reserve_hp,
        current_hub_reserve_hp,
        current_shares_hp,
        shares_removed_hp,
        position_amount_hp,
        position_shares_hp,
    ) = to_u256!(
        current_reserve,
        current_hub_reserve,
        current_shares,
        shares_removed,
        position.amount,
        position.shares
    );

    let p_x_r = U256::from(position_price.checked_mul_int(current_reserve)?);

    // Protocol shares update
    let delta_b_hp = if current_price < position_price {
        let numer = p_x_r
            .checked_sub(current_hub_reserve_hp)?
            .checked_mul(shares_removed_hp)?;
        let denom = p_x_r.checked_add(current_hub_reserve_hp)?;
        numer.checked_div(denom)?.checked_add(U256::one())? // round up
    } else {
        U256::from(Balance::zero())
    };

    let delta_shares_hp = shares_removed_hp.checked_sub(delta_b_hp)?;

    let delta_reserve_hp = current_reserve_hp
        .checked_mul(delta_shares_hp)
        .and_then(|v| v.checked_div(current_shares_hp))?;
    let delta_hub_reserve_hp = delta_reserve_hp
        .checked_mul(current_hub_reserve_hp)
        .and_then(|v| v.checked_div(current_reserve_hp))?;

    let delta_position_amount_hp = shares_removed_hp
        .checked_mul(position_amount_hp)
        .and_then(|v| v.checked_div(position_shares_hp))?;

    let delta_reserve = to_balance!(delta_reserve_hp).ok()?;
    let delta_hub_reserve = to_balance!(delta_hub_reserve_hp).ok()?;
    let delta_position_amount = to_balance!(delta_position_amount_hp).ok()?;
    let delta_shares = to_balance!(delta_shares_hp).ok()?;
    let delta_b = to_balance!(delta_b_hp).ok()?;

    let delta_imbalance = calculate_delta_imbalance_for_delta(delta_hub_reserve, imbalance, total_hub_reserve)?;

    let hub_transferred = if current_price > position_price {
        // LP receives some hub asset

        // delta_q_a = -pi * ( 2pi / (pi + pa) * delta_s_a / Si * Ri + delta_r_a )
        // note: delta_s_a is < 0

        let sub = current_hub_reserve_hp.checked_sub(p_x_r)?;
        let sum = current_hub_reserve_hp.checked_add(p_x_r)?;
        let div1 = current_hub_reserve_hp.checked_mul(sub)?.checked_div(sum)?;
        to_balance!(div1.checked_mul(delta_shares_hp)?.checked_div(current_shares_hp)?).ok()?
    } else {
        Balance::zero()
    };

    Some(LiquidityStateChange {
        asset: AssetStateChange {
            delta_reserve: Decrease(delta_reserve),
            delta_hub_reserve: Decrease(delta_hub_reserve),
            delta_shares: Decrease(delta_shares),
            delta_protocol_shares: Increase(delta_b),
        },
        delta_imbalance: Increase(delta_imbalance),
        lp_hub_amount: hub_transferred,
        delta_position_reserve: Decrease(delta_position_amount),
        delta_position_shares: Decrease(shares_removed),
    })
}

pub fn calculate_tvl(hub_reserve: Balance, stable_asset: (Balance, Balance)) -> Option<Balance> {
    let (hub_reserve_hp, stable_reserve_hp, stable_hub_reserve_hp) =
        to_u256!(hub_reserve, stable_asset.0, stable_asset.1);

    let tvl = hub_reserve_hp
        .checked_mul(stable_reserve_hp)
        .and_then(|v| v.checked_div(stable_hub_reserve_hp))?;

    to_balance!(tvl).ok()
}

pub fn calculate_delta_imbalance(
    asset_state: &AssetReserveState<Balance>,
    amount: Balance,
    imbalance: Balance,
    hub_reserve: Balance,
) -> Option<Balance> {
    if amount == Balance::zero() || imbalance == Balance::zero() || hub_reserve == Balance::zero() {
        return Some(Balance::default());
    }

    let (asset_reserve_hp, asset_hub_reserve_hp, amount_hp, imbalance_hp, hub_reserve_hp) = to_u256!(
        asset_state.reserve,
        asset_state.hub_reserve,
        amount,
        imbalance,
        hub_reserve
    );

    let delta_imbalance_hp = asset_hub_reserve_hp
        .checked_mul(imbalance_hp)
        .and_then(|v| v.checked_div(asset_reserve_hp))
        .and_then(|v| v.checked_mul(amount_hp))
        .and_then(|v| v.checked_div(hub_reserve_hp))?;

    to_balance!(delta_imbalance_hp).ok()
}

pub fn calculate_delta_imbalance_for_delta(
    delta_asset_hub_reserve: Balance,
    imbalance: I129<Balance>,
    hub_reserve: Balance,
) -> Option<Balance> {
    if imbalance.value == Balance::zero() {
        return Some(Balance::default());
    }

    if !imbalance.negative {
        // currently support only negative imbalances
        return None;
    }
    let (asset_hub_reserve_hp, imbalance_hp, hub_reserve_hp) =
        to_u256!(delta_asset_hub_reserve, imbalance.value, hub_reserve);

    let delta_imbalance_hp = asset_hub_reserve_hp
        .checked_mul(imbalance_hp)
        .and_then(|v| v.checked_div(hub_reserve_hp))?;

    to_balance!(delta_imbalance_hp).ok()
}
