//! # HydraDX Math
//!
//! A collection of utilities to make performing liquidity pool
//! calculations more convenient.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(not(feature = "std"), test))]
extern crate std;

#[cfg(feature = "p12")]
#[macro_use]
extern crate lazy_static;

#[cfg(test)]
#[macro_use]
extern crate approx;

pub mod lbp;
pub mod transcendental;
pub mod xyk;

#[cfg(feature = "p12")]
pub mod p12;

#[cfg(test)]
mod tests;
pub mod types;

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
        Weight::try_from($x).map_err(|_| Overflow)
    };
}

#[derive(PartialEq, Debug)]
pub enum MathError {
    Overflow,
    InsufficientOutReserve,
    ZeroWeight,
    ZeroReserve,
    ZeroDuration,
}

#[cfg(test)]
mod conversion_tests {
    use super::MathError::Overflow;
    use crate::lbp::Weight;
    use crate::types::Balance;
    use core::convert::TryFrom;

    const FIXED_ROUND_UP: Balance = 1;

    #[test]
    fn test_conversion() {
        let one: u32 = 1;
        assert_eq!(to_balance!(one), Ok(Balance::from(1u128)));
        assert_eq!(to_lbp_weight!(one), Ok(Balance::from(1u128)));
        assert_eq!(round_up!(Balance::from(one)), Ok(Balance::from(2u128)));
    }
}
