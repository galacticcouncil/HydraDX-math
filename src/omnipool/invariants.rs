use crate::assert_eq_approx;
use crate::omnipool::types::{AssetReserveState, Position, I129};
use crate::omnipool::*;
use crate::types::Balance;
use primitive_types::U256;
use proptest::prelude::*;
use sp_arithmetic::{FixedU128, Permill};

pub const ONE: Balance = 1_000_000_000_000;
pub const TOLERANCE: Balance = 1_000;

const BALANCE_RANGE: (Balance, Balance) = (100_000 * ONE, 10_000_000 * ONE);

fn asset_state() -> impl Strategy<Value = AssetReserveState<Balance>> {
    (
        BALANCE_RANGE.0..BALANCE_RANGE.1,
        BALANCE_RANGE.0..BALANCE_RANGE.1,
        BALANCE_RANGE.0..BALANCE_RANGE.1,
        BALANCE_RANGE.0..BALANCE_RANGE.1,
        BALANCE_RANGE.0..BALANCE_RANGE.1,
    )
        .prop_map(
            |(reserve, hub_reserve, shares, protocol_shares, tvl)| AssetReserveState {
                reserve,
                hub_reserve,
                shares,
                protocol_shares,
                tvl,
            },
        )
}

fn asset_reserve() -> impl Strategy<Value = Balance> {
    BALANCE_RANGE.0..BALANCE_RANGE.1
}

fn trade_amount() -> impl Strategy<Value = Balance> {
    1_000_000_000..10000 * ONE
}

fn price() -> impl Strategy<Value = FixedU128> {
    (0.1f64..2f64).prop_map(FixedU128::from_float)
}

fn stable_asset_state() -> impl Strategy<Value = (Balance, Balance)> {
    (asset_reserve(), asset_reserve())
}

fn position() -> impl Strategy<Value = Position<Balance>> {
    (trade_amount(), price()).prop_map(|(amount, price)| Position {
        amount,
        shares: amount,
        price,
    })
}

fn some_imbalance() -> impl Strategy<Value = I129<Balance>> {
    (0..10000 * ONE).prop_map(|value| I129 { value, negative: true })
}

fn assert_asset_invariant(
    old_state: &AssetReserveState<Balance>,
    new_state: &AssetReserveState<Balance>,
    tolerance: FixedU128,
    desc: &str,
) {
    let new_s = U256::from(new_state.reserve) * U256::from(new_state.hub_reserve);
    let s1 = new_s.integer_sqrt();

    let old_s = U256::from(old_state.reserve) * U256::from(old_state.hub_reserve);
    let s2 = old_s.integer_sqrt();

    assert!(new_s >= old_s, "Invariant decreased for {}", desc);

    let s1_u128 = Balance::try_from(s1).unwrap();
    let s2_u128 = Balance::try_from(s2).unwrap();

    let invariant = FixedU128::from((s1_u128, ONE)) / FixedU128::from((s2_u128, ONE));
    assert_eq_approx!(invariant, FixedU128::from(1u128), tolerance, desc);
}
fn fee() -> impl Strategy<Value = Permill> {
    // Allow values between 0.001 and 0.1
    (0u32..1u32, prop_oneof![Just(1000u32), Just(10000u32), Just(100_000u32)])
        .prop_map(|(n, d)| Permill::from_rational(n, d))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn sell_update_invariants_no_fees(asset_in in asset_state(), asset_out in asset_state(),
        amount in trade_amount()
    ) {
        let result = calculate_sell_state_changes(&asset_in, &asset_out, amount,
            Permill::from_percent(0),
            Permill::from_percent(0),
            Balance::default()
        );

        assert!(result.is_some());

        let state_changes = result.unwrap();

        let asset_in_state = asset_in.clone();
        let asset_in_state = asset_in_state.delta_update(&state_changes.asset_in).unwrap();

        assert_asset_invariant(&asset_in, &asset_in_state,  FixedU128::from((TOLERANCE, ONE)), "Sell update invariant - token in");

        let asset_out_state = asset_out.clone();
        let asset_out_state = asset_out_state.delta_update(&state_changes.asset_out).unwrap();

        assert_asset_invariant(&asset_out, &asset_out_state,  FixedU128::from((TOLERANCE, ONE)), "Sell update invariant - token out");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn sell_update_invariants_with_fees(asset_in in asset_state(),
        asset_out in asset_state(),
        amount in trade_amount(),
        asset_fee in fee(),
        protocol_fee in fee()
    ) {
        let result = calculate_sell_state_changes(&asset_in, &asset_out, amount,
            asset_fee,
            protocol_fee,
            Balance::default()
        );

        assert!(result.is_some());

        let state_changes = result.unwrap();

        let asset_in_state = asset_in.clone();
        let asset_in_state = asset_in_state.delta_update(&state_changes.asset_in).unwrap();
        assert_asset_invariant(&asset_in, &asset_in_state,  FixedU128::from((TOLERANCE, ONE)), "Sell update invariant - token in");

        let asset_out_state = asset_out.clone();
        let asset_out_state = asset_out_state.delta_update(&state_changes.asset_out).unwrap();
        assert_asset_invariant(&asset_out, &asset_out_state,  FixedU128::from((TOLERANCE, ONE)), "Sell update invariant - token out");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn sell_hub_update_invariants_with_fees(asset_out in asset_state(),
        amount in trade_amount(),
        asset_fee in fee(),
        imbalance in some_imbalance(),
    ) {
        let result = calculate_sell_hub_state_changes(&asset_out, amount,
            asset_fee,
            imbalance,
            100 * ONE + asset_out.hub_reserve,
        );

        assert!(result.is_some());

        let state_changes = result.unwrap();

        let asset_out_state = asset_out.clone();
        let asset_out_state = asset_out_state.delta_update(&state_changes.asset).unwrap();
        assert_asset_invariant(&asset_out, &asset_out_state,  FixedU128::from((TOLERANCE, ONE)), "Sell update invariant - token out");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn buy_hub_update_invariants_with_fees(asset_out in asset_state(),
        amount in trade_amount(),
        asset_fee in fee(),
        imbalance in some_imbalance(),
    ) {
        let result = calculate_buy_for_hub_asset_state_changes(&asset_out, amount,
            asset_fee,
            imbalance,
            100 * ONE + asset_out.hub_reserve,
        );

        assert!(result.is_some());

        let state_changes = result.unwrap();

        let asset_out_state = asset_out.clone();
        let asset_out_state = asset_out_state.delta_update(&state_changes.asset).unwrap();
        assert_asset_invariant(&asset_out, &asset_out_state,  FixedU128::from((TOLERANCE, ONE)), "Sell update invariant - token out");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn buy_update_invariants_with_fees(asset_in in asset_state(), asset_out in asset_state(),
        amount in trade_amount(),
        asset_fee in fee(),
        protocol_fee in fee()
    ) {
        let result = calculate_buy_state_changes(&asset_in, &asset_out, amount,
            asset_fee,
            protocol_fee,
            Balance::default()
        );

        // ignore the invalid result
        if let Some(state_changes) = result {
            let asset_in_state = asset_in.clone();
            let asset_in_state = asset_in_state.delta_update(&state_changes.asset_in).unwrap();
            assert_asset_invariant(&asset_in, &asset_in_state,  FixedU128::from((TOLERANCE, ONE)), "Buy update invariant - token in");

            let asset_out_state = asset_out.clone();
            let asset_out_state = asset_out_state.delta_update(&state_changes.asset_out).unwrap();
            assert_asset_invariant(&asset_out, &asset_out_state,  FixedU128::from((TOLERANCE, ONE)), "Buy update invariant - token out");
        }
    }
}
#[test]
fn buy_update_invariants_no_fees_case() {
    let asset_in = AssetReserveState {
        reserve: 10_000_000_000_000_000,
        hub_reserve: 10_000_000_000_000_000,
        shares: 10_000_000_000_000_000,
        protocol_shares: 10_000_000_000_000_000,
        tvl: 10_000_000_000_000_000,
    };
    let asset_out = AssetReserveState {
        reserve: 10_000_000_000_000_000,
        hub_reserve: 89_999_999_999_999_991,
        shares: 10_000_000_000_000_000,
        protocol_shares: 10_000_000_000_000_000,
        tvl: 10_000_000_000_000_000,
    };
    let amount = 1_000_000_000_000_000;

    let result = calculate_buy_state_changes(
        &asset_in,
        &asset_out,
        amount,
        Permill::from_percent(0),
        Permill::from_percent(0),
        Balance::default(),
    );

    assert!(result.is_none()); // This fails because of not enough asset out in pool out
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn buy_update_invariants_no_fees(asset_in in asset_state(), asset_out in asset_state(),
        amount in trade_amount()
    ) {
        let result = calculate_buy_state_changes(&asset_in, &asset_out, amount,

        Permill::from_percent(0),
        Permill::from_percent(0),
            Balance::default()
        );

        // perform assertion only when result is valid
        if let Some(state_changes) = result {
            let asset_in_state = asset_in.clone();
            let asset_in_state = asset_in_state.delta_update(&state_changes.asset_in).unwrap();
            assert_asset_invariant(&asset_in, &asset_in_state,  FixedU128::from((TOLERANCE, ONE)), "Buy update invariant - token in");

            let asset_out_state = asset_out.clone();
            let asset_out_state = asset_out_state.delta_update(&state_changes.asset_out).unwrap();
            assert_asset_invariant(&asset_out, &asset_out_state,  FixedU128::from((TOLERANCE, ONE)), "Buy update invariant - token out");
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn price_should_not_change_when_liquidity_added(asset in asset_state(),
        amount in trade_amount(),
        stable_asset in stable_asset_state(),
        imbalance in some_imbalance(),
    ) {
        let result = calculate_add_liquidity_state_changes(&asset,
            amount,
            stable_asset,
            false,
            imbalance,
            100 * ONE,
        );

        assert!(result.is_some());

        let state_changes = result.unwrap();

        let new_asset_state= asset.clone();
        let new_asset_state = new_asset_state.delta_update(&state_changes.asset).unwrap();

        // Price should not change
        assert_eq_approx!(asset.price().unwrap(),
            new_asset_state.price().unwrap(),
            FixedU128::from_float(0.0000000001),
            "Price has changed after add liquidity");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]
    #[test]
    fn price_should_not_change_when_liquidity_removed(asset in asset_state(),
        position in position(),
        stable_asset in stable_asset_state(),
        imbalance in some_imbalance(),
    ) {
        let result = calculate_remove_liquidity_state_changes(&asset,
            position.amount,
            &position,
            stable_asset,
            false,
            imbalance,
            100 * ONE,
        );

        assert!(result.is_some());

        let state_changes = result.unwrap();

        let new_asset_state= asset.clone();
        let new_asset_state = new_asset_state.delta_update(&state_changes.asset).unwrap();

        assert_ne!(new_asset_state.reserve, asset.reserve);

        // Price should not change
        assert_eq_approx!(asset.price().unwrap(),
            new_asset_state.price().unwrap(),
            FixedU128::from_float(0.0000000001),
            "Price has changed after remove liquidity");
    }
}
