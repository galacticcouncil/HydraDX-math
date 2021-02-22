use core::convert::TryFrom;
use primitive_types::U256;

type Balance = u128;

const FIXED_ROUND_UP: Balance = 1;

macro_rules! ensure {
    ($e:expr) => {
        match $e {
            true => (),
            false => {
                return None;
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

/// Calculating spot price given reserve of selling asset and reserve of buying asset.
/// Formula : BUY_RESERVE * AMOUNT / SELL_RESERVE
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `amount` - amount
///
/// Returns None in case of error
pub fn calculate_spot_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> Option<Balance> {
    ensure!(sell_reserve != 0);

    let (amount_hp, buy_reserve_hp, sell_reserve_hp) = to_u256!(amount, buy_reserve, sell_reserve);

    let spot_price_hp = buy_reserve_hp
        .checked_mul(amount_hp)
        .expect("Cannot overflow")
        .checked_div(sell_reserve_hp)?;

    to_u128!(spot_price_hp)
}

/// Calculating selling price given reserve of selling asset and reserve of buying asset.
/// Formula : OUT_RESERVE * AMOUNT_IN / (IN_RESERVE + AMOUNT_IN)
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `sell_amount` - amount
///
/// Returns None in case of error
pub fn calculate_out_given_in(in_reserve: Balance, out_reserve: Balance, amount_in: Balance) -> Option<Balance> {
    let (in_reserve_hp, out_reserve_hp,amount_in_hp) = to_u256!(in_reserve, out_reserve, amount_in);

    let numerator = out_reserve_hp.checked_mul(amount_in_hp)?;
    let denominator = in_reserve_hp.checked_add(amount_in_hp)?;
    let amount_out_hp = numerator.checked_div(denominator)?;

    match to_u128!(amount_out_hp) {
        Some(amount_out) => round_up!(amount_out),
        None => None,
    }
}

/// Calculating buying price given reserve of selling asset and reserve of buying asset.
/// Formula : IN_RESERVE * AMOUNT_OUT / (OUT_RESERVE - AMOUNT_OUT)
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `amount` - buy amount
///
/// Returns None in case of error
pub fn calculate_in_given_out(out_reserve: Balance, in_reserve: Balance, amount_out: Balance) -> Option<Balance> {
    ensure!(amount_out <= out_reserve);

    let (out_reserve_hp, in_reserve_hp, amount_out_hp) = to_u256!(out_reserve, in_reserve, amount_out);

    let numerator = in_reserve_hp.checked_mul(amount_out_hp)?;
    let denominator = out_reserve_hp.checked_sub(amount_out_hp)?;
    let amount_in_hp = numerator.checked_div(denominator)?;

    match to_u128!(amount_in_hp) {
        Some(amount_in) => round_up!(amount_in),
        None => None,
    }
}

pub fn calculate_liquidity_in(asset_a_reserve: Balance, asset_b_reserve: Balance, amount: Balance) -> Option<Balance> {
    ensure!(asset_a_reserve != 0);

    let (a_reserve_hp, b_reserve_hp, amount_hp) = to_u256!(asset_a_reserve, asset_b_reserve, amount);

    let b_required_hp = amount_hp
        .checked_mul(b_reserve_hp)
        .expect("Cannot overflow")
        .checked_div(a_reserve_hp)
        .expect("Cannot panic as reserve cannot be 0");

    to_u128!(b_required_hp)
}

pub fn calculate_liquidity_out(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    amount: Balance,
    total_liquidity: Balance,
) -> Option<(Balance, Balance)> {
    ensure!(total_liquidity != 0);

    let (a_reserve_hp, b_reserve_hp, amount_hp, liquidity_hp) =
        to_u256!(asset_a_reserve, asset_b_reserve, amount, total_liquidity);

    let remove_amount_a_hp = amount_hp
        .checked_mul(a_reserve_hp)
        .expect("Cannot overflow")
        .checked_div(liquidity_hp)
        .expect("Cannot panic as liquidity cannot be 0");

    let remove_amount_a = to_u128!(remove_amount_a_hp)?;

    let remove_amount_b_hp = b_reserve_hp
        .checked_mul(amount_hp)
        .expect("Cannot overflow")
        .checked_div(liquidity_hp)
        .expect("Cannot panic as liquidity cannot be 0");

    let remove_amount_b = to_u128!(remove_amount_b_hp)?;

    Some((remove_amount_a, remove_amount_b))
}
