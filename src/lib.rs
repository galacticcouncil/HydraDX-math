#![cfg_attr(not(feature = "std"), no_std)]

mod fee;

pub mod amm;
pub use amm::*;
