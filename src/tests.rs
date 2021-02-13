#[test]
fn spot_price_should_work() {
    let cases = vec![
        (1000, 2000, 500, Some(1000), "Easy case"),
        (0, 0, 0, None, "Zero reserves and weights"),
        (1, u128::MAX, u128::MAX, None, "Overflow weights"),
    ];

    for case in cases {
        assert_eq!(
            crate::amm::calculate_spot_price(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn sell_price_should_work() {
    let cases = vec![
        (1000, 2000, 500, Some(667), "Easy case"),
        (0, 0, 0, None, "Zero reserves and weights"),
        (0, 1, 0, None, "Zero sell reserve and amount"),
        (1, 0, 0, Some(1), "Zero buy reserve and amount"),
        (0, 0, u128::MAX, Some(1), "Zero buy reserve and sell reserve"),
        (0, u128::MAX, u128::MAX, None, "Zero sell reserve"),
    ];

    for case in cases {
        assert_eq!(
            crate::amm::calculate_sell_price(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn buy_price_should_work() {
    let cases = vec![
        (1000, 2000, 500, Some(334), "Easy case"),
        (0, 0, 0, None, "Zero reserves and weights"),
        (0, 10, 1000, None, "amount cannot be > buy reserve"),
        (0, u128::MAX, u128::MAX, None, "div by zero"),
        (u128::MAX, u128::MAX, u128::MAX-1, None, "Overflow weights"),
    ];

    for case in cases {
        assert_eq!(
            crate::amm::calculate_buy_price(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn add_liquidity_should_work() {
    let cases = vec![
        (1000, 2000, 500, Some(1000), "Easy case"),
        (100, 100, 0, Some(0), "amount is zero"),
        (110, 0, 100, Some(0), "asset b is zero"),
        (0, 110, 100, None, "asset a is zero"),
        (1, u128::MAX, u128::MAX, None, "asset b and amount are zero"),
    ];

    for case in cases {
        assert_eq!(
            crate::amm::calculate_liquidity_in(case.0, case.1, case.2),
            case.3,
            "{}",
            case.4
        );
    }
}

#[test]
fn remove_liquidity_should_work() {
    let cases = vec![
        (1000, 2000, 500, 2500, Some((200, 400)), "Easy case"),
        (100, 100, 100, 0, None, "total liquidity is zero"),
        (0, 0, 0, 100, Some((0,0)), "amount is zero"),
        (0, 110, 100, 100, Some((0,110)), "remove amount a is zero"),
        (110, 0, 100, 100, Some((110,0)), "remove amount b is zero"),
        (u128::MAX, 0, u128::MAX, 1, None, "Formula a overflow"),
        (0, u128::MAX, u128::MAX, 1, None, "Formula b overflow"),
    ];

    for case in cases {
        assert_eq!(
            crate::amm::calculate_liquidity_out(case.0, case.1, case.2, case.3),
            case.4,
            "{}",
            case.5
        );
    }
}
