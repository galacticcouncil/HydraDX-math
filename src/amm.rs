use core::convert::TryFrom;
use primitive_types::U256;

pub type HighPrecisionBalance = U256;
pub type LowPrecisionBalance = u128;
pub type Balance = u128;

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
