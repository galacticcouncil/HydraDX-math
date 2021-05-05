use crate::lbp::lbp;

use crate::MathError::{Overflow, ZeroInReserve, ZeroOutWeight};

#[test]
fn spot_price_should_work() {
    let cases = vec![
        (1000, 2000, 500, 500, 100, Ok(200), "Easy case"),
        (0, 0, 0, 0, 100, Err(ZeroInReserve), "Zero reserves and weights"),
        (0, 1, 1, 1, 1, Err(ZeroInReserve), "Zero sell_reserve"),
        (1, 0, 1, 1, 1, Ok(0), "Zero buy_reserve"),
        (1, 1, 0, 1, 1, Ok(0), "Zero amount"),
        (u128::MAX, u128::MAX - 1, 1, 1, 1, Ok(0), "Truncated result"),
        (
            1,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Err(Overflow),
            "Overflow weights",
        ),
    ];

    for case in cases {
        assert_eq!(
            lbp::calculate_spot_price(case.0, case.1, case.2, case.3, case.4),
            case.5,
            "{}",
            case.6
        );
    }
}

#[test]
fn out_given_in_should_work() {
    let cases = vec![
        (1000, 2000, 500, 500, 100, Ok(182), "Easy case"),
        (0, 0, 0, 0, 100, Err(ZeroOutWeight), "Zero reserves and weights"),
        (
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            u128::MAX,
            Ok(170141183460469231731687303715884105728),
            "max",
        ),
        (1, 0, 1, 1, 0, Err(Overflow), "Zero out reserve and amount"),
        (0, 0, 1, 1, u128::MAX, Ok(1), "Zero buy reserve and sell reserve"),
    ];

    for case in cases {
        assert_eq!(
            lbp::calculate_out_given_in(case.0, case.1, case.2, case.3, case.4),
            case.5,
            "{}",
            case.6
        );
    }
}

#[test]
fn in_give_out_should_work() {
    let cases = vec![
        (1000, 2000, 500, 500, 100, Ok(53), "Easy case"),
        (0, 0, 0, 0, 100, Err(Overflow), "Zero reserves and weights"),
    ];

    for case in cases {
        assert_eq!(
            lbp::calculate_in_given_out(case.0, case.1, case.2, case.3, case.4),
            case.5,
            "{}",
            case.6
        );
    }
}
