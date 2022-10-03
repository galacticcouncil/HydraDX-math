use crate::types::Balance;
use primitive_types::U256;
use proptest::prelude::*;
use sp_arithmetic::FixedU128;
use rug::{Assign, Integer, Float, Rational};

pub const ONE: Balance = 1_000_000_000_000;
const TOLERANCE: f64 = 1e-9;

#[macro_export]
macro_rules! assert_eq_approx {
    ( $x:expr, $y:expr, $z:expr, $r:expr) => {{
        let diff = if $x >= $y { $x - $y } else { $y - $x };
        if diff > $z {
            panic!("\n{} not equal\n left: {:?}\nright: {:?}\n", $r, $x, $y);
        }
    }};
}

fn asset_reserve() -> impl Strategy<Value = Balance> {
    1000 * ONE..1_000_000_000 * ONE
}

fn trade_amount() -> impl Strategy<Value = Balance> {
    ONE..100 * ONE
}

fn assert_asset_invariant(
    old_state: (Balance, Balance),
    new_state: (Balance, Balance),
    tolerance: f64,
    desc: &str,
) {
    let new_state_x = Integer::from(new_state.0);
    let new_state_y = Integer::from(new_state.1);
    let old_state_x = Integer::from(old_state.0);
    let old_state_y = Integer::from(old_state.1);

    let new_s = new_state_x * new_state_y;
    let old_s = old_state_x * old_state_y;

    // This checks that the invariant never decreases
    assert!(new_s >= old_s, "Invariant decreased for {}", desc);

    let inv_ratio = Rational::from((new_s, old_s));
    let diff = inv_ratio - 1;

    assert!(diff <= tolerance, "Invariant difference above tolerance for {}", desc);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn sell_invariants( asset_in_reserve in asset_reserve(),
        asset_out_reserve in asset_reserve(),
        amount in  trade_amount()
    ) {
        let amount_out = crate::xyk::calculate_out_given_in(asset_in_reserve, asset_out_reserve, amount).unwrap();

        assert_asset_invariant((asset_in_reserve, asset_out_reserve),
            (asset_in_reserve + amount, asset_out_reserve - amount_out),
            TOLERANCE,
            "out given in"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn buy_invariants( asset_in_reserve in asset_reserve(),
        asset_out_reserve in asset_reserve(),
        amount in  trade_amount()
    ) {
        let amount_in = crate::xyk::calculate_in_given_out(asset_out_reserve, asset_in_reserve, amount).unwrap();

        assert_asset_invariant((asset_in_reserve, asset_out_reserve),
            (asset_in_reserve + amount_in, asset_out_reserve - amount),
            TOLERANCE,
            "in given out"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn add_liquidity( asset_a_reserve in asset_reserve(),
        asset_b_reserve in asset_reserve(),
        amount in  trade_amount(),
        issuance in asset_reserve(),
    ) {
        let amount_b = crate::xyk::calculate_liquidity_in(asset_a_reserve, asset_b_reserve, amount).unwrap();

        let p0 = Rational::from((asset_a_reserve, asset_b_reserve));
        let p1 = Rational::from((asset_a_reserve + amount, asset_b_reserve + amount_b));

        // Price should not change
        let mut diff = p1 - p0;
        diff.abs_mut();
        assert!(diff <= TOLERANCE, "Price has changed after add liquidity");

        let shares = crate::xyk::calculate_shares(asset_a_reserve, amount, issuance).unwrap();

        // THe following must hold when adding liquiduity.
        //delta_S / S <= delta_X / X
        //delta_S / S <= delta_Y / Y

        let shares_ratio = Rational::from((shares, issuance));
        let asset_a_ratio = Rational::from((amount, asset_a_reserve));
        let asset_b_ratio = Rational::from((amount_b, asset_b_reserve));

        assert!(shares_ratio <= asset_a_ratio, "Shares ratio is greater than asset a ratio");
        assert!(shares_ratio <= asset_b_ratio, "Shares ratio is greater than asset b ratio");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn remove_liquidity_prices( asset_a_reserve in asset_reserve(),
        asset_b_reserve in asset_reserve(),
        shares in  trade_amount(),
        issuance in asset_reserve(),
    ) {
        let (amount_a, amount_b) = crate::xyk::calculate_liquidity_out(asset_a_reserve, asset_b_reserve, shares, issuance).unwrap();

        let p0 = Rational::from((asset_a_reserve, asset_b_reserve));
        let p1 = Rational::from((asset_a_reserve - amount_a, asset_b_reserve - amount_b));

        // Price should not change
        let mut diff = p1 - p0;
        diff.abs_mut();
        assert!(diff <= TOLERANCE, "Price has changed after add liquidity");

        // The following must hold when removing liquidity
        // delta_S / S >= delta_X / X
        // delta_S / S >= delta_Y / Y

        let shares_ratio = Rational::from((shares, issuance));
        let asset_a_ratio = Rational::from((amount_a, asset_a_reserve));
        let asset_b_ratio = Rational::from((amount_b, asset_b_reserve));

        assert!(shares_ratio >= asset_a_ratio, "Shares ratio is greater than asset a ratio");
        assert!(shares_ratio >= asset_b_ratio, "Shares ratio is greater than asset b ratio");
    }
}
