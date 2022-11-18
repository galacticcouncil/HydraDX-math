use crate::omnipool::types::AssetReserveState;
use crate::omnipool_subpools::{calculate_iso_in_given_stable_out, SubpoolState};
use sp_arithmetic::Permill;

#[test]
fn mixed_trade_should_work_when_buying_stable_with_omnipool_asset() {
    let pool_out = SubpoolState {
        reserves: &[3_000_000_000_000_000, 4_000_000_000_000_000],
        amplification: 100,
    };

    let idx_out = 0;

    let asset_state_in = AssetReserveState {
        reserve: 5_000_000_000_000_000,
        hub_reserve: 3250000000000000,
        shares: 5000000000000000,
        protocol_shares: 0,
    };

    let sshare_issuance_out = 4_550_000_000_000_000;

    let share_state_out = AssetReserveState {
        reserve: 4550000000000000,
        hub_reserve: 4550000000000000,
        shares: 4550000000000000,
        protocol_shares: 0,
    };

    let amount = 100_000_000_000_000;

    let result = calculate_iso_in_given_stable_out(
        pool_out,
        idx_out,
        &asset_state_in,
        &share_state_out,
        sshare_issuance_out,
        amount,
        Permill::zero(),
        Permill::zero(),
        Permill::zero(),
        0u128,
    );

    assert!(result.is_some());
}
