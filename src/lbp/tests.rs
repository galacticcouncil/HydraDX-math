use crate::lbp::lbp;
use primitives::fee::Fee;

use crate::MathError::{FeeAmountInvalid, Overflow, ZeroDuration, ZeroInReserve, ZeroOutWeight};

#[test]
fn spot_price_should_work() {
    let cases = vec![
        (
            1_000_000,
            2_000_000,
            500,
            500,
            100_000,
            Fee::default(),
            Ok((199_600, 400)),
            "Easy case",
        ),
        (
            1_000_000,
            2_000_000,
            500,
            500,
            100_000,
            Fee {
                numerator: 0,
                denominator: 1,
            },
            Ok((200_000, 0)),
            "Easy case zero fee",
        ),
        (
            0,
            0,
            0,
            0,
            100,
            Fee::default(),
            Err(ZeroInReserve),
            "Zero reserves and weights",
        ),
        (0, 1, 1, 1, 1, Fee::default(), Err(ZeroInReserve), "Zero sell_reserve"),
        (1, 0, 1, 1, 1, Fee::default(), Ok((0, 0)), "Zero buy_reserve"),
        (1, 1, 0, 1, 1, Fee::default(), Ok((0, 0)), "Zero amount"),
        (
            u128::MAX,
            u128::MAX - 1,
            1,
            1,
            1,
            Fee::default(),
            Ok((0, 0)),
            "Truncated result",
        ),
        (
            1,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Fee::default(),
            Err(Overflow),
            "Overflow weights",
        ),
        (
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Fee::default(),
            Err(Overflow),
            "max",
        ),
        (
            2,
            2,
            1,
            1,
            1,
            Fee {
                numerator: 1,
                denominator: 0,
            },
            Err(FeeAmountInvalid),
            "invalid fee",
        ),
    ];

    for case in cases {
        assert_eq!(
            lbp::calculate_spot_price(case.0, case.1, case.2, case.3, case.4, case.5),
            case.6,
            "{}",
            case.7
        );
    }
}

#[test]
fn out_given_in_should_work() {
    let cases = vec![
        (
            1_000_000,
            2_000_000,
            500,
            500,
            100_000,
            Fee::default(),
            Ok((181_456, 363)),
            "Easy case",
        ),
        (
            1_000_000,
            2_000_000,
            500,
            500,
            100_000,
            Fee {
                numerator: 0,
                denominator: 1,
            },
            Ok((181_819, 0)),
            "Easy case zero fee",
        ),
        (
            0,
            0,
            0,
            0,
            100,
            Fee::default(),
            Err(ZeroOutWeight),
            "Zero reserves and weights",
        ),
        (
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Fee {
                numerator: 0,
                denominator: 1,
            },
            Ok((170141183460469231731687303715884105728, 0)),
            "max",
        ),
        (
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Fee::default(),
            Err(FeeAmountInvalid),
            "max",
        ),
        (
            1,
            0,
            1,
            1,
            0,
            Fee::default(),
            Err(Overflow),
            "Zero out reserve and amount",
        ),
        (
            0,
            0,
            1,
            1,
            u128::MAX,
            Fee::default(),
            Ok((1, 0)),
            "Zero buy reserve and sell reserve",
        ),
        (
            2,
            2,
            1,
            1,
            1,
            Fee {
                numerator: 1,
                denominator: 0,
            },
            Err(FeeAmountInvalid),
            "invalid fee",
        ),
    ];

    for case in cases {
        assert_eq!(
            lbp::calculate_out_given_in(case.0, case.1, case.2, case.3, case.4, case.5),
            case.6,
            "{}",
            case.7
        );
    }
}

#[test]
fn in_given_out_should_work() {
    let cases = vec![
        (
            1_000_000,
            2_000_000,
            500,
            500,
            100_000,
            Fee::default(),
            Ok((52_632, 105)),
            "Easy case",
        ),
        (
            1_000_000,
            2_000_000,
            500,
            500,
            100_000,
            Fee {
                numerator: 0,
                denominator: 1,
            },
            Ok((52_632, 0)),
            "Easy case zero fee",
        ),
        (
            0,
            0,
            0,
            0,
            100,
            Fee::default(),
            Err(Overflow),
            "Zero reserves and weights",
        ),
        (
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Fee::default(),
            Err(Overflow),
            "max",
        ),
        (
            2,
            2,
            1,
            1,
            1,
            Fee {
                numerator: 1,
                denominator: 0,
            },
            Err(FeeAmountInvalid),
            "invalid fee",
        ),
    ];

    for case in cases {
        assert_eq!(
            lbp::calculate_in_given_out(case.0, case.1, case.2, case.3, case.4, case.5),
            case.6,
            "{}",
            case.7
        );
    }
}

#[test]
fn linear_weights_should_work() {
    let u32_cases = vec![
        (100u32, 200u32, 1_000u128, 2_000u128, 170u32, Ok(1_700), "Easy case"),
        (
            100u32,
            200u32,
            2_000u128,
            1_000u128,
            170u32,
            Ok(1_300),
            "Easy decreasing case",
        ),
        (
            100u32,
            200u32,
            2_000u128,
            2_000u128,
            170u32,
            Ok(2_000),
            "Easy constant case",
        ),
        (
            100u32,
            200u32,
            1_000u128,
            2_000u128,
            100u32,
            Ok(1_000),
            "Initial weight",
        ),
        (
            100u32,
            200u32,
            2_000u128,
            1_000u128,
            100u32,
            Ok(2_000),
            "Initial decreasing weight",
        ),
        (
            100u32,
            200u32,
            2_000u128,
            2_000u128,
            100u32,
            Ok(2_000),
            "Initial constant weight",
        ),
        (100u32, 200u32, 1_000u128, 2_000u128, 200u32, Ok(2_000), "Final weight"),
        (
            100u32,
            200u32,
            2_000u128,
            1_000u128,
            200u32,
            Ok(1_000),
            "Final decreasing weight",
        ),
        (
            100u32,
            200u32,
            2_000u128,
            2_000u128,
            200u32,
            Ok(2_000),
            "Final constant weight",
        ),
        (
            200u32,
            100u32,
            1_000u128,
            2_000u128,
            170u32,
            Err(Overflow),
            "Invalid interval",
        ),
        (
            100u32,
            100u32,
            1_000u128,
            2_000u128,
            100u32,
            Err(ZeroDuration),
            "Invalid interval",
        ),
        (
            100u32,
            200u32,
            1_000u128,
            2_000u128,
            10u32,
            Err(Overflow),
            "Out of bound",
        ),
        (
            100u32,
            200u32,
            1_000u128,
            2_000u128,
            210u32,
            Err(Overflow),
            "Out of bound",
        ),
    ];
    let u64_cases = vec![
        (100u64, 200u64, 1_000u128, 2_000u128, 170u64, Ok(1_700), "Easy case"),
        (
            100u64,
            u64::MAX,
            1_000u128,
            2_000u128,
            200u64,
            Err(Overflow),
            "Interval too long",
        ),
    ];

    for case in u32_cases {
        assert_eq!(
            lbp::calculate_linear_weights(case.0, case.1, case.2, case.3, case.4),
            case.5,
            "{}",
            case.6
        );
    }
    for case in u64_cases {
        assert_eq!(
            lbp::calculate_linear_weights(case.0, case.1, case.2, case.3, case.4),
            case.5,
            "{}",
            case.6
        );
    }
}
