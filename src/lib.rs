//! # HydraDX Math
//!
//! A collection of utilities to make performing liquidity pool
//! calculations more convenient.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate lazy_static;

pub mod amm;
pub mod lbp;

pub use amm::*;

#[cfg(test)]
mod tests;

#[macro_export]
macro_rules! ensure {
    ($e:expr, $f:expr) => {
        match $e {
            true => (),
            false => {
                return Err($f);
            }
        }
    };
}

#[macro_export]
macro_rules! round_up {
    ($e:expr) => {
        $e.checked_add(FIXED_ROUND_UP).ok_or(Overflow)
    };
}

#[macro_export]
macro_rules! to_u256 {
    ($($x:expr),+) => (
        {($(U256::from($x)),+)}
    );
}

#[macro_export]
macro_rules! to_balance {
    ($x:expr) => {
        Balance::try_from($x).map_err(|_| Overflow)
    };
}

#[macro_export]
macro_rules! to_lbp_weight {
    ($x:expr) => {
        LBPWeight::try_from($x).map_err(|_| Overflow)
    };
}

#[derive(PartialEq, Debug)]
pub enum MathError {
    ZeroInReserve,
    Overflow,
    InsufficientOutReserve,
    ZeroOutWeight,
    ZeroDuration,
}
