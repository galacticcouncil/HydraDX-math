//! # HydraDX Math
//!
//! A collection of utilities to make performing liquidity pool
//! calculations more convenient.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod amm;
mod tests;

pub use amm::*;
