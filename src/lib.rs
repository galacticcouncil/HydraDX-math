use wasm_bindgen::prelude::*;

use core::convert::TryFrom;
use primitive_types::U256;

pub type HighPrecisionBalance = U256;
pub type LowPrecisionBalance = u128;
pub type Balance = u128;

fn calculate_spot_price(sell_reserve: Balance, buy_reserve: Balance, amount: Balance) -> u128 {
	let amount_hp: HighPrecisionBalance = HighPrecisionBalance::from(amount);
	let buy_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(buy_reserve);
	let sell_reserve_hp: HighPrecisionBalance = HighPrecisionBalance::from(sell_reserve);

	let spot_price_hp = buy_reserve_hp
		.checked_mul(amount_hp)
		.expect("Cannot overflow")
		.checked_div(sell_reserve_hp)
		.unwrap();

	let spot_price_lp: Result<LowPrecisionBalance, &'static str> = LowPrecisionBalance::try_from(spot_price_hp);
	spot_price_lp.unwrap_or(0)
}

fn convert_to_u128(s: &str) -> u128 {
	match s.parse::<u128>() {
		Ok(v) => v,
		Err(_) => 0,
	}
}

#[wasm_bindgen]
pub fn get_spot_price(s: String, b: String, a: String) -> String {
	let sell_reserve = convert_to_u128(&s);
	let buy_reserve = convert_to_u128(&b);
	let amount = convert_to_u128(&a);

	let result = calculate_spot_price(sell_reserve, buy_reserve, amount);

	result.to_string().chars().collect::<String>()
}
