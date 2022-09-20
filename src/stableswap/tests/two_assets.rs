const D_ITERATIONS: u8 = 128;
const Y_ITERATIONS: u8 = 64;

use super::*;
use crate::stableswap::*;
use crate::types::Balance;
use sp_arithmetic::Permill;

#[test]
fn test_d() {
    let precision = 1_u128;

    let reserves = [1000u128, 1000u128];
    assert_eq!(
        calculate_d::<D_ITERATIONS>(&reserves, 1, precision),
        Some(2000u128 + 2u128)
    );

    let reserves = [1_000_000_000_000_000_000_000u128, 1_000_000_000_000_000_000_000u128];
    assert_eq!(
        calculate_d::<D_ITERATIONS>(&reserves, 1, precision),
        Some(2_000_000_000_000_000_000_000u128 + 2u128)
    );
}

#[test]
fn test_d_with_zero_reserves() {
    let precision = 1_u128;
    let reserves = [0u128, 0u128];
    assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, 1, precision), Some(0u128));
}

#[test]
fn test_y_given_in() {
    let precision = 1_u128;
    let reserves = [1000u128, 2000u128];

    let amount_in = 100u128;
    assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, 1, precision), Some(2942u128));
    assert_eq!(
        calculate_y_given_in::<D_ITERATIONS, Y_ITERATIONS>(amount_in, 0, 1, &reserves, 1, precision),
        Some(2000u128 - 121u128)
    );
    assert_eq!(
        calculate_d::<D_ITERATIONS>(&[1100u128, 2000u128 - 125u128], 1, precision),
        Some(2942u128)
    );
}

#[test]
fn test_y_given_out() {
    let precision = 1_u128;
    let reserves = [1000u128, 2000u128];

    let amount_out = 100u128;

    let expected_in = 83u128;

    assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, 1, precision), Some(2942u128));

    assert_eq!(
        calculate_y_given_out::<D_ITERATIONS, Y_ITERATIONS>(amount_out, 0, 1, &reserves, 1, precision),
        Some(1000u128 + expected_in)
    );
    assert_eq!(
        calculate_d::<D_ITERATIONS>(&[1000u128 + expected_in, 2000u128 - amount_out], 1, precision),
        Some(2946u128)
    );
}

#[test]
fn test_d_case() {
    let amp = 400u128;

    let precision = 1u128;

    let result = calculate_d::<D_ITERATIONS>(&[500000000000008580273458u128, 10u128], amp, precision);

    assert!(result.is_some());
}

#[test]
fn test_d_case2() {
    let amp = 168u128;

    let precision = 1u128;

    let result = calculate_d::<D_ITERATIONS>(&[500000000000000000000010u128, 11u128], amp, precision);

    assert!(result.is_some());
}

#[test]
fn test_case_03() {
    let reserve_in: Balance = 95329220803912837655;
    let reserve_out: Balance = 57374284583541134907;
    let amp: u128 = 310;

    let precision = 1u128;

    let d = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], amp, precision);

    assert!(d.is_some());
}

#[test]
fn test_shares() {
    let precision = 1u128;
    let amp = 100u128;

    let initial_reserves = &[0u128, 0u128];
    let updated_reserves = &[1000 * ONE, 0u128];

    let result = calculate_shares::<D_ITERATIONS>(initial_reserves, updated_reserves, amp, precision, 0u128);

    assert!(result.is_some());
    assert_eq!(result.unwrap(), 1_000_000_000_000_000u128);
}
#[test]
fn remove_one_asset_should_work() {
    let precision = 1u128;
    let amp = 100u128;

    let reserves = &[1000 * ONE, 2000u128];

    let result = calculate_withdraw_one_asset::<D_ITERATIONS, Y_ITERATIONS>(
        reserves,
        100u128,
        1,
        3000u128,
        amp,
        precision,
        Permill::from_percent(10),
    );

    assert!(result.is_some());

    let result = result.unwrap();

    assert_eq!(result, (168, 24));
}
