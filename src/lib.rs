#![cfg_attr(not(feature = "std"), no_std)]

mod fee;

pub mod amm;
pub use amm::calculate_spot_price;
pub use amm::calculate_sell_price;
