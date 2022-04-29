use crate::{
    ensure, round_up, to_balance, to_u256, MathError,
    MathError::{InsufficientOutReserve, Overflow, ZeroReserve},
};
use crate::transcendental::get_y_stableswap;
use core::convert::TryFrom;
use primitive_types::U256;

type Balance = u128;

const FIXED_ROUND_UP: Balance = 1;

/// Calculating spot price given reserve of selling asset and reserve of buying asset.
/// Formula : OUT_RESERVE * AMOUNT / IN_RESERVE
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `amount` - amount
///
/// Returns MathError in case of error
pub fn calculate_spot_price(in_reserve: Balance, out_reserve: Balance, amount: Balance) -> Result<Balance, MathError> {
    ensure!(in_reserve != 0, ZeroReserve);

    if amount == 0 || out_reserve == 0 {
        return to_balance!(0);
    }

    let (amount_hp, out_reserve_hp, in_reserve_hp) = to_u256!(amount, out_reserve, in_reserve);

    let spot_price_hp = out_reserve_hp
        .checked_mul(amount_hp)
        .ok_or(Overflow)?
        .checked_div(in_reserve_hp)
        .ok_or(Overflow)?;

    to_balance!(spot_price_hp)
}

/// Calculating amount to be received from the pool given the amount to be sent to the pool and both reserves.
/// Formula : OUT_RESERVE * AMOUNT_IN / (IN_RESERVE + AMOUNT_IN)
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `amount_in` - amount
///
/// Returns MathError in case of error
pub fn calculate_out_given_in(
    in_reserve: Balance,
    out_reserve: Balance,
    amount_in: Balance,
) -> Result<Balance, MathError> {
    if amount_in == 0 {
        return Ok(0);
    };

    let (in_reserve_hp, out_reserve_hp, amount_in_hp) = to_u256!(in_reserve, out_reserve, amount_in);

    let y_stableswap = get_y_stableswap(0, 1, amount_in_hp, [in_reserve_hp, out_reserve_hp], to_u256!(200_u128)).unwrap();

    let amount_out = y_stableswap.checked_sub(out_reserve_hp).ok_or(Overflow)?;

    to_balance!(amount_out)
}

/// Calculating amount to be sent to the pool given the amount to be received from the pool and both reserves.
/// Formula : IN_RESERVE * AMOUNT_OUT / (OUT_RESERVE - AMOUNT_OUT)
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `amount_out` - buy amount
///
/// Returns MathError in case of error
pub fn calculate_in_given_out(
    out_reserve: Balance,
    in_reserve: Balance,
    amount_out: Balance,
) -> Result<Balance, MathError> {
    if amount_out == 0 {
        return Ok(0);
    };
    ensure!(amount_out <= out_reserve, InsufficientOutReserve);

    let (out_reserve_hp, in_reserve_hp, amount_out_hp) = to_u256!(out_reserve, in_reserve, amount_out);

    let numerator = in_reserve_hp.checked_mul(amount_out_hp).ok_or(Overflow)?;
    let denominator = out_reserve_hp.checked_sub(amount_out_hp).ok_or(Overflow)?;
    ensure!(!denominator.is_zero(), ZeroReserve);
    let buy_price_hp = numerator.checked_div(denominator).ok_or(Overflow)?;

    let result = to_balance!(buy_price_hp).ok();
    round_up!(result.ok_or(Overflow)?)
}

/// Calculating required amount of asset b given asset a.
/// Formula : AMOUNT * ASSET_B_RESERVE / ASSET_A_RESERVE
///
/// - `asset_a_reserve` - reserve amount of asset a
/// - `asset_b_reserve` - reserve amount of asset b
/// - `amount` - liquidity amount
///
/// Returns MathError in case of error
pub fn calculate_liquidity_in(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    amount: Balance,
) -> Result<Balance, MathError> {
    ensure!(asset_a_reserve != 0, ZeroReserve);

    let (a_reserve_hp, b_reserve_hp, amount_hp) = to_u256!(asset_a_reserve, asset_b_reserve, amount);

    let b_required_hp = amount_hp
        .checked_mul(b_reserve_hp)
        .ok_or(Overflow)?
        .checked_div(a_reserve_hp)
        .ok_or(Overflow)?;

    to_balance!(b_required_hp)
}

/// Calculating amount of assets returned when removing liquidity.
/// Formula A: AMOUNT * ASSET_A_RESERVE / TOTAL_LIQUIDITY
/// Formula B: AMOUNT * ASSET_B_RESERVE / TOTAL_LIQUIDITY
///
/// - `asset_a_reserve` - reserve amount of asset a
/// - `asset_b_reserve` - reserve amount of asset b
/// - `amount` - liquidity amount
///
/// Returns MathError in case of error
pub fn calculate_liquidity_out(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    amount: Balance,
    total_liquidity: Balance,
) -> Result<(Balance, Balance), MathError> {
    ensure!(total_liquidity != 0, ZeroReserve);

    let (a_reserve_hp, b_reserve_hp, amount_hp, liquidity_hp) =
        to_u256!(asset_a_reserve, asset_b_reserve, amount, total_liquidity);

    let remove_amount_a_hp = amount_hp
        .checked_mul(a_reserve_hp)
        .ok_or(Overflow)?
        .checked_div(liquidity_hp)
        .ok_or(Overflow)?;

    let remove_amount_a = to_balance!(remove_amount_a_hp)?;

    let remove_amount_b_hp = b_reserve_hp
        .checked_mul(amount_hp)
        .ok_or(Overflow)?
        .checked_div(liquidity_hp)
        .ok_or(Overflow)?;

    let remove_amount_b = to_balance!(remove_amount_b_hp)?;

    Ok((remove_amount_a, remove_amount_b))
}
