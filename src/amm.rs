use core::convert::TryFrom;
use primitive_types::U256;

use crate::fee;

pub type HighPrecisionBalance = U256;
pub type LowPrecisionBalance = u128;
pub type Balance = u128;

/// Calculating spot price given reserve of selling asset and reserve of buying asset.
/// Formula : BUY_RESERVE * AMOUNT / SELL_RESERVE
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `amount` - amount
///
/// Returns None in case of error
pub fn calculate_spot_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> Option<Balance> {
    let amount_hp: HighPrecisionBalance = HighPrecisionBalance::from(amount);
    let buy_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(buy_reserve);
    let sell_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(sell_reserve);

    let spot_price_hp = buy_reserve_hp
        .checked_mul(amount_hp)
        .expect("Cannot overflow")
        .checked_div(sell_reserve_hp)?;

    let spot_price_lp: Result<LowPrecisionBalance, &'static str> = LowPrecisionBalance::try_from(spot_price_hp);
    spot_price_lp.ok()
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
    let sell_amount_hp: HighPrecisionBalance = HighPrecisionBalance::from(sell_amount);
    let buy_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(buy_reserve);
    let sell_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(sell_reserve);

    let numerator = buy_reserve_hp.checked_mul(sell_amount_hp)?;
    let denominator = sell_reserve_hp.checked_add(sell_amount_hp)?;

    let sale_price_hp = numerator.checked_div(denominator)?;

    let sale_price_lp: Result<LowPrecisionBalance, &'static str> = LowPrecisionBalance::try_from(sale_price_hp);

    match sale_price_lp.ok() {
        Some(sale_price) => fee::fixed_fee(sale_price),
        None => None,
    }
}

/// Calculating buying price given reserve of selling asset and reserve of buying asset.
/// Formula : SELL_RESERVE * AMOUNT / (BUY_RESERVE - AMOUNT )
///
/// - `sell_reserve` - reserve amount of selling asset
/// - `buy_reserve` - reserve amount of buying asset
/// - `_amount` - buy amount
///
/// Returns None in case of error
pub fn calculate_buy_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> Option<Balance> {
    if amount > buy_reserve {
        return None;
    }

    let amount_hp: HighPrecisionBalance = HighPrecisionBalance::from(amount);
    let buy_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(buy_reserve);
    let sell_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(sell_reserve);

    let numerator = sell_reserve_hp.checked_mul(amount_hp)?;
    let denominator = buy_reserve_hp.checked_sub(amount_hp)?;
    let buy_price_hp = numerator.checked_div(denominator)?;

    let buy_price_lp: Result<LowPrecisionBalance, &'static str> = LowPrecisionBalance::try_from(buy_price_hp);

    match buy_price_lp.ok() {
        Some(buy_price) => fee::fixed_fee(buy_price),
        None => None,
    }
}

pub fn calculate_liquidity_in(asset_a_reserve: Balance, asset_b_reserve: Balance, amount: Balance) -> Option<Balance> {
    let a_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(asset_a_reserve);
    let b_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(asset_b_reserve);
    let amount_hp: HighPrecisionBalance = HighPrecisionBalance::from(amount);

    let b_required_hp = amount_hp
        .checked_mul(b_reserve_hp)
        .expect("Cannot overflow")
        .checked_div(a_reserve_hp)
        .expect("Cannot panic as reserve cannot be 0"); //TODO: cant rely on this here atm!

    let b_required_lp: Result<Balance, &'static str> = Balance::try_from(b_required_hp);

    b_required_lp.ok()
}

pub fn calculate_liquidity_out(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    amount: Balance,
    total_liquidity: Balance,
) -> Option<(Balance, Balance)> {
    let a_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(asset_a_reserve);
    let b_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(asset_b_reserve);
    let amount_hp: HighPrecisionBalance = HighPrecisionBalance::from(amount);
    let liquidity_hp: HighPrecisionBalance = HighPrecisionBalance::from(total_liquidity);
    let remove_amount_a_hp = amount_hp
        .checked_mul(a_reserve_hp)
        .expect("Cannot overflow")
        .checked_div(liquidity_hp)
        .expect("Cannot panic as liquidity cannot be 0"); //TODO: cant rely on this here atm!
    let remove_amount_a_lp: Result<LowPrecisionBalance, &'static str> =
        LowPrecisionBalance::try_from(remove_amount_a_hp);
    if remove_amount_a_lp.is_err() {
        return None;
    }
    let remove_amount_a = remove_amount_a_lp.unwrap();

    let remove_amount_b_hp = b_reserve_hp
        .checked_mul(amount_hp)
        .expect("Cannot overflow")
        .checked_div(liquidity_hp)
        .expect("Cannot panic as liquidity cannot be 0"); //TODO: cant rely on this here atm!

    let remove_amount_b_lp: Result<LowPrecisionBalance, &'static str> =
        LowPrecisionBalance::try_from(remove_amount_b_hp);

    if remove_amount_b_lp.is_err() {
        return None;
    }
    let remove_amount_b = remove_amount_b_lp.unwrap();

    Some((remove_amount_a, remove_amount_b))
}
