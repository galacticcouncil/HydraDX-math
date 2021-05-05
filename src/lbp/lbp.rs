use primitive_types::U256;
use std::convert::TryFrom;

use crate::{
    ensure, to_balance, to_u256, MathError,
    MathError::{Overflow, ZeroInReserve, ZeroOutWeight},
};

use crate::lbp::traits::BinomMath;
use crate::lbp::types::Balance;

/// Calculating spot price given reserve of selling asset and reserve of buying asset.
/// Formula : BUY_RESERVE * AMOUNT / SELL_RESERVE
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `in_weight` - pool weight of selling asset
/// - `out_Weight` - pool weight of buying asset
/// - `amount` - amount
///
/// Returns None in case of error
pub fn calculate_spot_price(
    in_reserve: Balance,
    out_reserve: Balance,
    in_weight: Balance,
    out_weight: Balance,
    amount: Balance,
) -> Result<Balance, MathError> {
    // If any is 0 - let's not progress any further.
    ensure!(in_reserve != 0, ZeroInReserve);

    if amount == 0 || out_reserve == 0 {
        return to_balance!(0);
    }

    let (amount, out_reserve, in_reserve, out_weight, in_weight) =
        to_u256!(amount, out_reserve, in_reserve, out_weight, in_weight);

    let spot_price = amount
        .checked_mul(out_reserve)
        .ok_or(Overflow)?
        .checked_mul(in_weight)
        .ok_or(Overflow)?
        .checked_div(in_reserve.checked_mul(out_weight).expect("Cannot overflow"))
        .ok_or(Overflow)?;

    to_balance!(spot_price)
}

/// Calculating selling price given reserve of selling asset and reserve of buying asset.
/// Formula : BUY_RESERVE * AMOUNT / (SELL_RESERVE + AMOUNT )
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `in_weight` - pool weight of selling asset
/// - `out_weight` - pool weight of buying asset
/// - `amount` - amount
///
/// Returns None in case of error
pub fn calculate_out_given_in(
    in_reserve: Balance,
    out_reserve: Balance,
    in_weight: Balance,
    out_weight: Balance,
    amount: Balance,
) -> Result<Balance, MathError> {
    ensure!(out_weight != 0, ZeroOutWeight);

    let (in_weight, out_weight, amount, in_reserve, out_reserve) =
        to_u256!(in_weight, out_weight, amount, in_reserve, out_reserve);

    let weight_ratio = in_weight.hdiv(out_weight).ok_or(Overflow)?;

    let y = in_reserve
        .hdiv(in_reserve.hadd(amount).ok_or(Overflow)?)
        .ok_or(Overflow)?;

    let x3 = y.hpow(weight_ratio).ok_or(Overflow)?;

    let x4 = x3.hsubr_one().ok_or(Overflow)?;

    let r = out_reserve.hmul(x4).ok_or(Overflow)?;

    to_balance!(r)
}

/// Calculating buying price given reserve of selling asset and reserve of buying asset.
/// Formula :
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `in_weight` - pool weight of selling asset
/// - `out_weight` - pool weight of buying asset
/// - `amount` - buy amount
///
/// Returns None in case of error
pub fn calculate_in_given_out(
    in_reserve: Balance,
    out_reserve: Balance,
    in_weight: Balance,
    out_weight: Balance,
    amount: Balance,
) -> Result<Balance, MathError> {
    let (in_weight, out_weight, amount, in_reserve, out_reserve) =
        to_u256!(in_weight, out_weight, amount, in_reserve, out_reserve);

    let weight_ratio = out_weight.hdiv(in_weight).ok_or(Overflow)?;
    let diff = out_reserve.hsub(amount).ok_or(Overflow)?;
    let y = out_reserve.hdiv(diff).ok_or(Overflow)?;
    let y1 = y.hpow(weight_ratio).ok_or(Overflow)?;
    let y2 = y1.hsub_one().ok_or(Overflow)?;
    let r = in_reserve.hmul(y2).ok_or(Overflow)?;

    to_balance!(r)
}
