use core::convert::TryFrom;
use primitive_types::U256;
use crate::MathError::{ZeroInReserve, Overflow, InsufficientOutReserve};

type Balance = u128;

const FIXED_ROUND_UP: Balance = 1;

macro_rules! ensure {
    ($e:expr, $f:expr) => {
        match $e {
            true => (),
            false => {
                return Err($f);
            }
        }
    };
}

macro_rules! round_up {
    ($e:expr) => {
        $e.checked_add(FIXED_ROUND_UP)
    };
}

macro_rules! to_u256 {
    ($($x:expr),+) => (
        {($(U256::from($x)),+)}
    );
}

macro_rules! to_u128 {
    ($x:expr) => {
        u128::try_from($x).ok()
    };
}

#[derive(PartialEq)]
#[derive(Debug)]
pub enum MathError {
    ZeroInReserve,
    Overflow,
    InsufficientOutReserve,
}

/// Calculating spot price given reserve of selling asset and reserve of buying asset.
/// Formula : BUY_RESERVE * AMOUNT / SELL_RESERVE
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `amount` - amount
///
/// Returns MathError in case of error
pub fn calculate_spot_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> Result<Balance, MathError> {
    ensure!(sell_reserve != 0, ZeroInReserve);

    if amount == 0 || buy_reserve == 0 {
        return Ok(0u128);
    }

    let (sell_reserve_hp, buy_reserve_hp, amount_hp) = to_u256!(sell_reserve, buy_reserve, amount);

    let spot_price_hp = buy_reserve_hp
        .checked_mul(amount_hp).ok_or(Overflow).unwrap()
        .checked_div(sell_reserve_hp).ok_or(Overflow).unwrap();

    to_u128!(spot_price_hp).ok_or(Overflow)
}

/// Calculating selling price given reserve of selling asset and reserve of buying asset.
/// Formula : BUY_RESERVE * AMOUNT / (SELL_RESERVE + AMOUNT )
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `sell_amount` - amount
///
/// Returns MathError in case of error
pub fn calculate_sell_price(sell_reserve: Balance, buy_reserve: Balance, sell_amount: Balance) -> Result<Balance, MathError> {
    let (sell_reserve_hp, buy_reserve_hp, sell_amount_hp) = to_u256!(sell_reserve, buy_reserve, sell_amount);

    let denominator = sell_reserve_hp.checked_add(sell_amount_hp).expect("cannot");
    ensure!(!denominator.is_zero(), ZeroInReserve);

    let numerator = buy_reserve_hp.checked_mul(sell_amount_hp).ok_or(Overflow).unwrap();
    let sale_price_hp = numerator.checked_div(denominator).ok_or(Overflow).unwrap();

    let result = to_u128!(sale_price_hp).ok_or(Overflow).ok();
    round_up!(result.unwrap()).ok_or(Overflow)
}

/// Calculating buying price given reserve of selling asset and reserve of buying asset.
/// Formula : SELL_RESERVE * AMOUNT / (BUY_RESERVE - AMOUNT)
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `amount` - buy amount
///
/// Returns None in case of error
pub fn calculate_buy_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> Result<Balance, MathError> {
    ensure!(amount <= buy_reserve, InsufficientOutReserve);

    let (sell_reserve_hp, buy_reserve_hp, amount_hp) = to_u256!(sell_reserve, buy_reserve, amount);

    let numerator = sell_reserve_hp.checked_mul(amount_hp).ok_or(Overflow).unwrap();
    let denominator = buy_reserve_hp.checked_sub(amount_hp).ok_or(Overflow).unwrap();
    ensure!(!denominator.is_zero(), ZeroInReserve);
    let buy_price_hp = numerator.checked_div(denominator).ok_or(Overflow).unwrap();

    let result = to_u128!(buy_price_hp).ok_or(Overflow).ok();
    round_up!(result.unwrap()).ok_or(Overflow)
}

pub fn calculate_liquidity_in(asset_a_reserve: Balance, asset_b_reserve: Balance, amount: Balance) -> Result<Balance, MathError> {
    ensure!(asset_a_reserve != 0, ZeroInReserve);

    let (a_reserve_hp, b_reserve_hp, amount_hp) = to_u256!(asset_a_reserve, asset_b_reserve, amount);

    let b_required_hp = amount_hp
        .checked_mul(b_reserve_hp).ok_or(Overflow).unwrap()
        .checked_div(a_reserve_hp).ok_or(Overflow).unwrap();

    to_u128!(b_required_hp).ok_or(Overflow)
}

pub fn calculate_liquidity_out(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    amount: Balance,
    total_liquidity: Balance,
) -> Result<(Balance, Balance), MathError> {
    ensure!(total_liquidity != 0, ZeroInReserve);

    let (a_reserve_hp, b_reserve_hp, amount_hp, liquidity_hp) =
        to_u256!(asset_a_reserve, asset_b_reserve, amount, total_liquidity);

    let remove_amount_a_hp = amount_hp
        .checked_mul(a_reserve_hp).ok_or(Overflow).unwrap()
        .checked_div(liquidity_hp).ok_or(Overflow).unwrap();

    let remove_amount_a = to_u128!(remove_amount_a_hp).ok_or(Overflow);

    let remove_amount_b_hp = b_reserve_hp
        .checked_mul(amount_hp).ok_or(Overflow).unwrap()
        .checked_div(liquidity_hp).ok_or(Overflow).unwrap();

    let remove_amount_b = to_u128!(remove_amount_b_hp).ok_or(Overflow);

    Ok((remove_amount_a.unwrap(), remove_amount_b.unwrap()))
}