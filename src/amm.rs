use core::convert::TryFrom;
use primitive_types::U256;
use crate::MathError::{DivisorIsZero, ResultOverflow, InsufficientBuyReserve};

type Balance = u128;

const FIXED_ROUND_UP: Balance = 1;
const CANNOT_OVERFLOW: &str = "Cannot overflow";
const DENOMINATOR_NOT_ZERO: &str = "Cannot panic as denominator cannot be 0";

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

//TODO: Help wanted! Please make this macro so it would accept arbitrary number of args and return tuple of same length
// Currently explicitly covers only cases needed in this module.
macro_rules! to_u256 {
    ($x:expr) => {
        U256::from($x)
    };
    ($x:expr, $y:expr ) => {
        (to_u256!($x), to_u256!($y))
    };
    ($x:expr, $y:expr, $z:expr ) => {
        (to_u256!($x), to_u256!($y), to_u256!($z))
    };
    ($x:expr, $y:expr, $z:expr, $d:expr ) => {
        (to_u256!($x), to_u256!($y), to_u256!($z), to_u256!($d))
    };
}

macro_rules! to_u128 {
    ($x:expr) => {
        u128::try_from($x).ok()
    };
}

macro_rules! multiply {
    ($a:expr, $b:expr) => {
        $a.checked_mul($b).expect(CANNOT_OVERFLOW)
    };
}

macro_rules! add {
    ($a:expr, $b:expr) => {
        $a.checked_add($b).expect(CANNOT_OVERFLOW)
    };
}

macro_rules! divide {
    ($a:expr, $b:expr) => {
        $a.checked_div($b).expect(DENOMINATOR_NOT_ZERO)
    };
}

macro_rules! substract {
    ($a:expr, $b:expr) => {
        $a.checked_sub($b).expect(CANNOT_OVERFLOW)
    };
}


#[derive(PartialEq)]
#[derive(Debug)]
pub enum MathError {
    DivisorIsZero,
    ResultOverflow,
    InsufficientBuyReserve,
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
    ensure!(sell_reserve != 0, DivisorIsZero);

    if amount == 0 || buy_reserve == 0 {
        return Ok(0u128);
    }

    let (amount_hp, buy_reserve_hp, sell_reserve_hp) = to_u256!(amount, buy_reserve, sell_reserve);
    let dividend = multiply!(buy_reserve_hp, amount_hp);
    let spot_price_hp = divide!(dividend, sell_reserve_hp);

    to_u128!(spot_price_hp).ok_or(ResultOverflow)
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
    let (sell_amount_hp, buy_reserve_hp, sell_reserve_hp) = to_u256!(sell_amount, buy_reserve, sell_reserve);
    let divisor = add!(sell_reserve_hp, sell_amount_hp);
    ensure!(!divisor.is_zero(), DivisorIsZero);

    let dividend = multiply!(buy_reserve_hp, sell_amount_hp);
    let sale_price_hp = divide!(dividend, divisor);

    let result = to_u128!(sale_price_hp).ok_or(ResultOverflow).ok();
    round_up!(result.unwrap()).ok_or(ResultOverflow)
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
    ensure!(amount <= buy_reserve, InsufficientBuyReserve);

    let (amount_hp, buy_reserve_hp, sell_reserve_hp) = to_u256!(amount, buy_reserve, sell_reserve);
    let divisor = substract!(buy_reserve_hp, amount_hp);
    ensure!(!divisor.is_zero(), DivisorIsZero);

    let dividend = multiply!(sell_reserve_hp, amount_hp);
    let buy_price_hp = divide!(dividend, divisor);

    let result = to_u128!(buy_price_hp).ok_or(ResultOverflow).ok();
    round_up!(result.unwrap()).ok_or(ResultOverflow)
}

pub fn calculate_liquidity_in(asset_a_reserve: Balance, asset_b_reserve: Balance, amount: Balance) -> Result<Balance, MathError> {
    ensure!(asset_a_reserve != 0, DivisorIsZero);

    let (a_reserve_hp, b_reserve_hp, amount_hp) = to_u256!(asset_a_reserve, asset_b_reserve, amount);
    let dividend = multiply!(amount_hp, b_reserve_hp);
    let b_required_hp = divide!(dividend, a_reserve_hp);

    to_u128!(b_required_hp).ok_or(ResultOverflow)
}

pub fn calculate_liquidity_out(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    amount: Balance,
    total_liquidity: Balance,
) -> Result<(Balance, Balance), MathError> {
    ensure!(total_liquidity != 0, DivisorIsZero);

    let (a_reserve_hp, b_reserve_hp, amount_hp, liquidity_hp) =
        to_u256!(asset_a_reserve, asset_b_reserve, amount, total_liquidity);

    let dividend_a = multiply!(amount_hp, a_reserve_hp);
    let remove_amount_a_hp = divide!(dividend_a, liquidity_hp);
    let remove_amount_a = to_u128!(remove_amount_a_hp).ok_or(ResultOverflow);

    let dividend_b = multiply!(amount_hp, b_reserve_hp);
    let remove_amount_b_hp = divide!(dividend_b, liquidity_hp);
    let remove_amount_b = to_u128!(remove_amount_b_hp).ok_or(ResultOverflow);

    Ok((remove_amount_a.unwrap(), remove_amount_b.unwrap()))
}
