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
/// Formula : BUY_RESERVE * AMOUNT / (SELL_RESERVE + AMOUNT )
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `sell_amount` - amount
///
/// Returns None in case of error
pub fn calculate_sell_price(sell_reserve: Balance, buy_reserve: Balance, sell_amount: Balance) -> Option<Balance> {
    let (sell_amount_hp, buy_reserve_hp, sell_reserve_hp) = to_u256!(sell_amount, buy_reserve, sell_reserve);

    let numerator = buy_reserve_hp.checked_mul(sell_amount_hp)?;
    let denominator = sell_reserve_hp.checked_add(sell_amount_hp)?;

    let sale_price_hp = numerator.checked_div(denominator)?;

    match to_u128!(sale_price_hp) {
        Some(sale_price) => round_up!(sale_price),
        None => None,
    }
}

/// Calculating buying price given reserve of selling asset and reserve of buying asset.
/// Formula : SELL_RESERVE * AMOUNT / (BUY_RESERVE - AMOUNT )
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `amount` - buy amount
///
/// Returns None in case of error
pub fn calculate_buy_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> Option<Balance> {
    ensure!(amount <= buy_reserve);

    let (amount_hp, buy_reserve_hp, sell_reserve_hp) = to_u256!(amount, buy_reserve, sell_reserve);

    let numerator = sell_reserve_hp.checked_mul(amount_hp)?;
    let denominator = buy_reserve_hp.checked_sub(amount_hp)?;
    let buy_price_hp = numerator.checked_div(denominator)?;

    match to_u128!(buy_price_hp) {
        Some(buy_price) => round_up!(buy_price),
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
