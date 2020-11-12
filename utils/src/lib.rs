#![cfg_attr(not(feature = "std"), no_std)]

pub mod amm;
pub use amm::calculate_spot_price;
