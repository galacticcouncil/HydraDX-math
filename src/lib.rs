#![cfg_attr(not(feature = "std"), no_std)]

pub mod amm;
mod tests;
mod proptests;

pub use amm::*;
