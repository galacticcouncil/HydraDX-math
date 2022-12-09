use crate::omnipool::types::BalanceUpdate::{Decrease, Increase};
use crate::omnipool::types::{AssetReserveState, AssetStateChange, TradeStateChange};
use crate::omnipool_subpools::{
    calculate_buy_between_subpools, calculate_iso_in_given_stable_out, SubpoolState, SubpoolStateChange, TradeResult,
};
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

#[test]
fn calculate_buy_between_subpools_should_work() {
    let pool_in = SubpoolState {
        reserves: &[3000000000000000, 4000000000000000],
        amplification: 10u128,
    };

    let pool_out = SubpoolState {
        reserves: &[5000000000000000, 6000000000000000],
        amplification: 10u128,
    };

    let idx_in = 0;
    let idx_out = 0;
    let amount_out = 15000000000000;

    let share_state_in = AssetReserveState {
        reserve: 4550000000000000,
        hub_reserve: 4550000000000000,
        shares: 4550000000000000,
        protocol_shares: 0,
    };
    let share_state_out = AssetReserveState {
        reserve: 7150000000000000,
        hub_reserve: 7150000000000000,
        shares: 7150000000000000,
        protocol_shares: 0,
    };

    let share_issuance_in = 4550000000000000;
    let share_issuance_out = 7150000000000000;

    let asset_fee = Permill::from_percent(0);
    let protocol_fee = Permill::from_percent(0);
    let withdraw_fee = Permill::from_percent(0);
    let imbalance = 0;

    let result = calculate_buy_between_subpools(
        pool_in,
        pool_out,
        idx_in,
        idx_out,
        amount_out,
        &share_state_in,
        &share_state_out,
        share_issuance_in,
        share_issuance_out,
        asset_fee,
        protocol_fee,
        withdraw_fee,
        imbalance,
    );

    assert_eq!(
        result,
        Some(TradeResult {
            asset_in: SubpoolStateChange {
                idx: 0,
                amount: Increase(15005692740828),
            },
            asset_out: SubpoolStateChange {
                idx: 0,
                amount: Decrease(amount_out)
            },
            iso_pool: TradeStateChange {
                asset_in: AssetStateChange {
                    delta_reserve: Increase(9831807614855),
                    delta_hub_reserve: Decrease(9810608490621),
                    delta_shares: Increase(0),
                    delta_protocol_shares: Increase(0)
                },
                asset_out: AssetStateChange {
                    delta_reserve: Decrease(9797165671499),
                    delta_hub_reserve: Increase(9810608490621),
                    delta_shares: Increase(0),
                    delta_protocol_shares: Increase(0)
                },
                delta_imbalance: Decrease(0),
                hdx_hub_amount: 0
            },
        })
    );
}
