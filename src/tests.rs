#![allow(unused_imports)]
use crate::MathError::{InsufficientOutReserve, Overflow, ZeroReserve};
use crate::{to_u256, to_balance};
use crate::stableswap::{get_d, get_y_stableswap};
use crate::stableswap::calculate_out_given_in as stableswap_out_given_in;
use primitive_types::U256;
use crate::approx::assert_abs_diff_eq;
use crate::types::Balance;
use std::convert::TryFrom;

use std::vec;

#[test]
fn get_d_should_work() {
    let cases = vec![
        (
            to_u256!(10_000_000_000_000_000_u128),
            to_u256!(10_000_000_000_000_000_u128),
            to_u256!(100_u128),
            "Case1"
        ),
        (
            to_u256!(1_000_000_000_000_000_u128),
            to_u256!(10_000_000_000_000_000_u128),
            to_u256!(100_u128),
            "Case2"
        ),
        (
            to_u256!(17_000_000_000_000_000_u128),
            to_u256!(7_000_000_000_000_u128),
            to_u256!(300_u128),
            "Case3"
        ),
    ];

    let n = 2_i32;

    for case in cases {
        let a = case.2;
        let x1 = case.0;
        let x2 = case.1;
        let d = get_d([x1, x2], to_u256!(n) * a).unwrap();
        let lhs = a * to_u256!(n.pow(n as u32)) * (x1 + x2) + d;
        let mut d_pow = to_u256!(1_u128);
        for i in 0..((n+1) as usize) {
            d_pow *= d;
        }
        let rhs = a * d * to_u256!(n.pow(n as u32)) + d_pow/(to_u256!(n.pow(n as u32)) * x1 * x2);
        assert_eq!((lhs - rhs)/(to_u256!(10_000_u128)), to_u256!(0_u128), "{}", case.3);

    }
}

#[test]
fn get_y_stableswap_should_work() {
    let i = 0_i128;
    let j = 1_i128;
    let cases = vec![
        (
            to_u256!(100_100_u128),
            to_u256!(100_000_u128),
            to_u256!(100_000_u128),
            to_u256!(100_u128),
            "Case1"
        ),
        (
            to_u256!(1_001_000_000_000_000_u128),
            to_u256!(1_000_000_000_000_000_u128),
            to_u256!(10_000_000_000_000_000_u128),
            to_u256!(100_u128),
            "Case2"
        ),
        (
            to_u256!(17_000_100_000_000_000_u128),
            to_u256!(17_000_000_000_000_000_u128),
            to_u256!(7_000_000_000_000_u128),
            to_u256!(300_u128),
            "Case3"
        ),
        (
            to_u256!(16_999_900_000_000_000_u128),
            to_u256!(17_000_000_000_000_000_u128),
            to_u256!(7_000_000_000_000_u128),
            to_u256!(300_u128),
            "Case4"
        ),
    ];

    let n = 2_i32;

    for case in cases {
        let a = case.3;
        let x1 = case.1;
        let x2 = case.2;
        let delta_x1 = case.0;
        let x1_new = x1 + delta_x1;
        let x2_new = get_y_stableswap(i, j, delta_x1, [x1, x2], a).unwrap();
        let d = get_d([x1, x2], to_u256!(n) * a).unwrap();
        let lhs = a * to_u256!(n.pow(n as u32)) * (x1 + x2) + d;
        let mut d_pow = to_u256!(1_u128);
        for i in 0..((n+1) as usize) {
            d_pow *= d;
        }
        let rhs = a * d * to_u256!(n.pow(n as u32)) + d_pow/(to_u256!(n.pow(n as u32)) * x1 * x2);
        assert_eq!((lhs - rhs)/(to_u256!(10_000_u128)), to_u256!(0_u128), "{}", case.4);

    }
}

#[test]
fn out_given_in_stableswap_should_work() {
    let i = 0_i128;
    let j = 1_i128;
    let cases = vec![
        (
            5_000_000_000_000_000_u128,
            10_000_000_000_000_000_u128,
            10_000_000_000_000_000_u128,
            "Case1"
        ),
        (
            1_000_000_000_000_u128,
            1_000_000_000_000_000_u128,
            10_000_000_000_000_000_u128,
            "Case2"
        ),
        (
            100_000_000_000_u128,
            17_000_000_000_000_000_u128,
            7_000_000_000_000_u128,
            "Case3"
        ),
    ];

    let n = 2_i32;

    for case in cases {
        let a = to_u256!(100_u128);
        let x1_old = to_balance!(case.1).unwrap();
        let x2_old = to_balance!(case.2).unwrap();
        let delta_x1 = to_balance!(case.0).unwrap();
        let x1 = to_u256!(x1_old.checked_add(delta_x1).unwrap());
        let delta_x2 = stableswap_out_given_in(x1_old, x2_old, delta_x1).unwrap();
        let x2 = to_u256!(x2_old.checked_sub(delta_x2).unwrap());

        let d = get_d([to_u256!(x1_old), to_u256!(x2_old)], to_u256!(n) * a).unwrap();
        let lhs = a * to_u256!(n.pow(n as u32)) * (x1 + x2) + d;
        let mut d_pow = to_u256!(1_u128);
        let d_by_x1 = d.checked_div(x1).ok_or(Overflow).unwrap();
        let d_by_x2 = d.checked_div(x2).ok_or(Overflow).unwrap();
        let d_squared = d.checked_mul(d).unwrap();
        let d_squared_by_x1 = d_squared.checked_div(x1).unwrap();
        let d_pow_by_x1 = d_squared_by_x1.checked_mul(d).unwrap();
        let d_pow_by_prod = d_pow_by_x1.checked_div(x2).unwrap();
        // println!("x1: {}", to_balance!(x1).unwrap().to_string());
        // println!("x2: {}", to_balance!(x2).unwrap().to_string());
        // println!("d: {}", to_balance!(d).unwrap().to_string());
        // println!("d_by_x1: {}", to_balance!(d_by_x1).unwrap().to_string());
        for i in 0..((n+1) as usize) {
            d_pow *= d;
        }
        let rhs_old = a * d * to_u256!(n.pow(n as u32)) + d_pow/(to_u256!(n.pow(n as u32)) * x1 * x2);
        let rhs = a * d * to_u256!(n.pow(n as u32)) + d_pow_by_prod/to_u256!(n.pow(n as u32));
        if rhs > lhs {
            assert!(lhs/(rhs - lhs) > to_u256!(1_000_000_000_000_u128))
        }
        else if lhs > rhs {
            assert!(lhs/(lhs - rhs) > to_u256!(1_000_000_000_000_u128))
        }

    }
}

#[test]
fn spot_price_should_work() {
    let cases = vec![
        (1000, 2000, 500, Ok(1000), "Easy case"),
        (1, 1, 1, Ok(1), "Easy case"),
        (0, 1, 1, Err(ZeroReserve), "Zero sell_reserve"),
        (1, 0, 1, Ok(0), "Zero buy_reserve"),
        (1, 1, 0, Ok(0), "Zero amount"),
        (u128::MAX, u128::MAX - 1, 1, Ok(0), "Truncated result"),
        (1, u128::MAX, u128::MAX, Err(Overflow), "Overflow weights"),
    ];

    for case in cases {
        assert_eq!(
            crate::xyk::calculate_spot_price(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}




#[test]
fn out_given_in_should_work() {
    let cases = vec![
        (1000, 2000, 500, Ok(666), "Easy case"),
        (1000, 1000, 0, Ok(0), "Zero amount in"),
        (0, u128::MAX, u128::MAX, Ok(u128::MAX), "Zero sell reserve"),
        (0, 0, 0, Ok(0), "Zero reserves and weights"),
        (0, 1, 0, Ok(0), "Zero sell reserve and amount"),
        (1, 0, 0, Ok(0), "Zero buy reserve and amount"),
        (0, 0, u128::MAX, Ok(0), "Zero buy reserve and sell reserve"),
    ];

    for case in cases {
        assert_eq!(
            crate::xyk::calculate_out_given_in(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn in_given_out_should_work() {
    let cases = vec![
        (2000, 1000, 500, Ok(334), "Easy case"),
        (1000, 1000, 0, Ok(0), "Zero amount out"),
        (0, 0, 0, Ok(0), "Zero reserves and weights"),
        (0, 1, 0, Ok(0), "Zero buy reserve and amount"),
        (1000, 1000, 1000, Err(ZeroReserve), "Zero reserves and weights"),
        (
            0,
            10,
            1000,
            Err(InsufficientOutReserve),
            "amount cannot be > buy reserve",
        ),
        (0, u128::MAX, u128::MAX, Err(InsufficientOutReserve), "div by zero"),
        (u128::MAX, u128::MAX, u128::MAX - 1, Err(Overflow), "Overflow weights"),
    ];

    for case in cases {
        assert_eq!(
            crate::xyk::calculate_in_given_out(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn add_liquidity_should_work() {
    let cases = vec![
        (1000, 2000, 500, Ok(1000), "Easy case"),
        (100, 100, 0, Ok(0), "amount is zero"),
        (110, 0, 100, Ok(0), "asset b is zero"),
        (0, 110, 100, Err(ZeroReserve), "asset a is zero"),
        (1, u128::MAX, u128::MAX, Err(Overflow), "asset b and amount are zero"),
    ];

    for case in cases {
        assert_eq!(
            crate::xyk::calculate_liquidity_in(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn remove_liquidity_should_work() {
    let cases = vec![
        (1000, 2000, 500, 2500, Ok((200, 400)), "Easy case"),
        (100, 100, 100, 0, Err(ZeroReserve), "total liquidity is zero"),
        (0, 0, 0, 100, Ok((0, 0)), "amount is zero"),
        (0, 110, 100, 100, Ok((0, 110)), "remove amount a is zero"),
        (110, 0, 100, 100, Ok((110, 0)), "remove amount b is zero"),
        (u128::MAX, 0, u128::MAX, 1, Err(Overflow), "Formula a overflow"),
        (0, u128::MAX, u128::MAX, 1, Err(Overflow), "Formula b overflow"),
    ];

    for case in cases {
        assert_eq!(
            crate::xyk::calculate_liquidity_out(case.0, case.1, case.2, case.3),
            case.4,
            "{}",
            case.5
        );
    }
}
