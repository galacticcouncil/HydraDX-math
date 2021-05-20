use core::convert::TryFrom;
use primitive_types::U256;

use crate::{
    ensure, to_balance, to_u256, MathError,
    MathError::{Overflow, ZeroDuration, ZeroInReserve, ZeroOutWeight},
};

use crate::lbp::traits::BinomMath;
use crate::lbp::types::{Balance, LBPWeight};
use std::convert::TryInto;

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

/// Calculating weight at any given block in an interval using linear interpolation.
///
/// - `start_x` - beginning of an interval
/// - `end_x` - end of an interval
/// - `start_y` - initial weight
/// - `end_y` - final weight
/// - `at` - block number at which to calculate the weight
pub fn calculate_linear_weights<BlockNumber: sp_arithmetic::traits::AtLeast32BitUnsigned>(
    start_x: BlockNumber,
    end_x: BlockNumber,
    start_y: LBPWeight,
    end_y: LBPWeight,
    at: BlockNumber,
) -> Result<LBPWeight, MathError> {
    let d1 = end_x.checked_sub(&at).ok_or(Overflow)?;
    let d2 = at.checked_sub(&start_x).ok_or(Overflow)?;
    let dx = end_x.checked_sub(&start_x).ok_or(Overflow)?;

    let dx: u32 = dx.try_into().map_err(|_| Overflow)?;
    // if dx fits into u32, d1 and d2 fit into u128
    let d1: u128 = d1.try_into().map_err(|_| Overflow)?;
    let d2: u128 = d2.try_into().map_err(|_| Overflow)?;

    ensure!(dx != 0, ZeroDuration);

    let (start_y, end_y, d1, d2) = to_u256!(start_y, end_y, d1, d2);

    let left_part = start_y.checked_mul(d1).ok_or(Overflow)?;
    let right_part = end_y.checked_mul(d2).ok_or(Overflow)?;
    let result = (left_part.checked_add(right_part).ok_or(Overflow)?)
        .checked_div(dx.into())
        .ok_or(Overflow)?;

    result.try_into().map_err(|_| Overflow)
}
