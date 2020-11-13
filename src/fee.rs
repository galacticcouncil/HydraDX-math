#![allow(unused)]

pub type Balance = u128;

pub const FEE_RATE: Balance = 998;
pub const FEE_RATE_M: Balance = 1000;
const FIXED_ROUND_UP: Balance = 1;

pub const DISCOUNT_FEE_RATE: Balance = 9993;
pub const DISCOUNT_FEE_RATE_M: Balance = 10000;

pub fn apply_fee(amount: Balance) -> Option<Balance> {
    amount.checked_mul(FEE_RATE)?.checked_div(FEE_RATE_M)
}

pub fn get_fee(amount: Balance) -> Option<Balance> {
    amount.checked_mul(FEE_RATE_M - FEE_RATE)?.checked_div(FEE_RATE_M)
}

pub fn get_discounted_fee(amount: Balance) -> Option<Balance> {
    amount
        .checked_mul(DISCOUNT_FEE_RATE_M - DISCOUNT_FEE_RATE)?
        .checked_div(DISCOUNT_FEE_RATE_M)
}

pub fn fixed_fee(amount: Balance) -> Option<Balance> {
    amount.checked_add(FIXED_ROUND_UP)
}
