#[test]
fn spot_price_should_work() {
    let cases = vec![
        (1000, 2000, 500, Some(1000), "Easy case"),
        (0, 0, 0, None, "Zero reserves and weights"),
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
        (0, 0, 0, None, "Zero reserves and weights"),
        (110, 0, 100, Some(0), "asset b and amount are zero"),
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
        (0, 0, 0, 0, None, "Zero reserves and weights"),
        (110, 0, 0, 100, Some((0,0)), "Not sure"),
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
