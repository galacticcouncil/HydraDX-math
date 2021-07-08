use core::convert::{TryFrom, TryInto};
use primitive_types::U256;

use crate::{
    ensure, to_balance, to_lbp_weight, to_u256, MathError,
    MathError::{Overflow, ZeroDuration, ZeroReserve, ZeroWeight},
};

use crate::math::p12;
use crate::types::Balance;

pub type Weight = Balance;

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
    ensure!(in_reserve != 0, ZeroReserve);

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

fn convert_to_fixed(value: Balance) -> FixedBalance {
    if value == Balance::from(1u32) {
        return FixedBalance::from_num(1);
    }

    let f = value.checked_div(1_000_000_000_000).unwrap();
    let r = value - (f.checked_mul(1_000_000_000_000).unwrap());
    return FixedBalance::from_num(f) + (FixedBalance::from_num(r) / 1_000_000_000_000);
}

fn convert_from_fixed(value: FixedBalance) -> Option<Balance> {
    let w: Balance = value.int().to_num();
    let frac = value.frac();
    let frac: Balance = frac.checked_mul_int(1_000_000_000_000u128)?.int().to_num();
    let r = w.checked_mul(1_000_000_000_000u128)?.checked_add(frac)?;
    Some(r)
}

use crate::experimental::experimental::FixedBalance;
use core::convert::From;
use fixed::traits::Fixed;

#[macro_export]
macro_rules! to_fixed_balance{
    ($($x:expr),+) => (
        {($(convert_to_fixed($x)),+)}
    );
}

#[macro_export]
macro_rules! to_balance_from_fixed {
    ($x:expr) => {
        convert_from_fixed($x).ok_or(Overflow)
    };
}

/// Calculating selling price given reserve of selling asset and reserve of buying asset.
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
    ensure!(out_weight != 0, ZeroWeight);
    ensure!(in_weight != 0, ZeroWeight);
    ensure!(out_reserve != 0, ZeroReserve);
    ensure!(in_reserve != 0, ZeroWeight);

    let (in_weight, out_weight, amount, in_reserve, out_reserve) =
        to_fixed_balance!(in_weight, out_weight, amount, in_reserve, out_reserve);

    let weight_ratio = in_weight.checked_div(out_weight).ok_or(Overflow)?;

    let one = FixedBalance::from_num(1);
    //let ir = in_reserve.checked_div(in_reserve.checked_add(amount).ok_or(Overflow)?).ok_or(Overflow)?;
    let ir = one / (one + (amount / in_reserve));

    let ir = crate::experimental::experimental::pow(ir, weight_ratio).map_err(|_| Overflow)?;

    let ir = FixedBalance::from_num(1).checked_sub(ir).ok_or(Overflow)?;

    let r = out_reserve.checked_mul(ir).ok_or(Overflow)?;

    to_balance_from_fixed!(r)
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
        to_fixed_balance!(in_weight, out_weight, amount, in_reserve, out_reserve);

    let weight_ratio = out_weight.checked_div(in_weight).ok_or(Overflow)?;
    let diff = out_reserve.checked_sub(amount).ok_or(Overflow)?;
    let y = out_reserve.checked_div(diff).ok_or(Overflow)?;
    let y1: FixedBalance = crate::experimental::experimental::pow(y, weight_ratio).map_err(|_| Overflow)?;
    let y2 = y1.checked_sub(FixedBalance::from_num(1u128)).ok_or(Overflow)?;
    let r = in_reserve.checked_mul(y2).ok_or(Overflow)?;

    to_balance_from_fixed!(r)
}

/// Calculating weight at any given block in an interval using linear interpolation.
///
/// - `start_x` - beginning of an interval
/// - `end_x` - end of an interval
/// - `start_y` - initial weight
/// - `end_y` - final weight
/// - `at` - block number at which to calculate the weight
pub fn calculate_linear_weights<BlockNumber: num_traits::CheckedSub + TryInto<u32> + TryInto<u128>>(
    start_x: BlockNumber,
    end_x: BlockNumber,
    start_y: Weight,
    end_y: Weight,
    at: BlockNumber,
) -> Result<Weight, MathError> {
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

    to_lbp_weight!(result)
}
