#![cfg_attr(not(feature = "std"), no_std)]

pub mod amm;

#[cfg(feature = "wasm")]
mod wasm;

#[cfg(feature = "wasm")]
wasm_api!();
