use crate::to_u256;
use crate::types::Balance;
use num_traits::Zero;
use primitive_types::U256;
use sp_std::prelude::*;

/// Calculating amount to be received from the pool given the amount to be sent to the pool and both reserves.
/// N - number of iterations to use for Newton's formula to calculate parameter D ( it should be >=1 otherwise it wont converge at all and will always fail
/// N_Y - number of iterations to use for Newton's formula to calculate reserve Y ( it should be >=1 otherwise it wont converge at all and will always fail
pub fn calculate_out_given_in<const N: u8, const N_Y: u8>(
    balances: &[Balance],
    idx_in: usize,
    idx_out: usize,
    amount_in: Balance,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = calculate_ann(balances.len(), amplification)?;
    let new_reserve_out = calculate_y_given_in::<N, N_Y>(amount_in, idx_in, idx_out, balances, ann, precision)?;
    balances[idx_out].checked_sub(new_reserve_out)
}

/// Calculating amount to be sent to the pool given the amount to be received from the pool and both reserves.
/// N - number of iterations to use for Newton's formula ( it should be >=1 otherwise it wont converge at all and will always fail
/// N_Y - number of iterations to use for Newton's formula to calculate reserve Y ( it should be >=1 otherwise it wont converge at all and will always fail
pub fn calculate_in_given_out<const N: u8, const N_Y: u8>(
    balances: &[Balance],
    idx_in: usize,
    idx_out: usize,
    amount_out: Balance,
    amplification: Balance,
    precision: Balance,
) -> Option<Balance> {
    let ann = calculate_ann(balances.len(), amplification)?;
    let new_reserve_in = calculate_y_given_out::<N, N_Y>(amount_out, idx_in, idx_out, balances, ann, precision)?;
    new_reserve_in.checked_sub(balances[idx_in])
}

pub fn calculate_shares<const N: u8>(
    initial_reserves: &[Balance],
    updated_reserves: &[Balance],
    amplification: Balance,
    precision: Balance,
    share_issuance: Balance,
) -> Option<Balance> {
    let ann = calculate_ann(initial_reserves.len(), amplification)?;

    let initial_d = calculate_d::<N>(initial_reserves, ann, precision)?;

    // We must make sure the updated_d is rounded *down* so that we are not giving the new position too many shares.
    // calculate_d can return a D value that is above the correct D value by up to 2, so we subtract 2.
    let updated_d = calculate_d::<N>(updated_reserves, ann, precision)?.checked_sub(2_u128)?;

    if updated_d < initial_d {
        return None;
    }

    if share_issuance == 0 {
        // if first liquidity added
        Some(updated_d)
    } else {
        let (issuance_hp, d_diff, d0) = to_u256!(share_issuance, updated_d - initial_d, initial_d);
        let share_amount = issuance_hp.checked_mul(d_diff)?.checked_div(d0)?;
        Balance::try_from(share_amount).ok()
    }
}

/// Given amount of shares and asset reserves, calculate corresponding amounts of each asset to be withdrawn.
pub fn calculate_remove_liquidity_amounts(
    reserves: &[Balance],
    shares: Balance,
    share_asset_issuance: Balance,
) -> Option<Vec<Balance>> {
    if share_asset_issuance.is_zero() {
        return None;
    }

    let (shares_hp, issuance_hp) = to_u256!(shares, share_asset_issuance);

    let calculate_amount = |asset_reserve: Balance| {
        Balance::try_from(
            to_u256!(asset_reserve)
                .checked_mul(shares_hp)?
                .checked_div(issuance_hp)?,
        )
        .ok()
    };

    let mut r = Vec::<Balance>::new();
    for reserve in reserves {
        r.push(calculate_amount(*reserve)?);
    }

    Some(r)
}

/// amplification * n^n where n is number of assets in pool.
fn calculate_ann(len: usize, amplification: Balance) -> Option<Balance> {
    (0..len).try_fold(amplification, |acc, _| acc.checked_mul(len as u128))
}

fn calculate_y_given_in<const N: u8, const N_Y: u8>(
    amount: Balance,
    idx_in: usize,
    idx_out: usize,
    balances: &[Balance],
    ann: Balance,
    precision: Balance,
) -> Option<Balance> {
    let new_reserve_in = balances[idx_in].checked_add(amount)?;

    let d = calculate_d::<N>(balances, ann, precision)?;

    let xp: Vec<Balance> = balances
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_out)
        .map(|(idx, v)| if idx == idx_in { new_reserve_in } else { *v })
        .collect();

    calculate_y::<N_Y>(&xp, d, ann, precision)
}

/// Calculate new amount of reserve IN given amount to be withdrawn from the pool
fn calculate_y_given_out<const N: u8, const N_Y: u8>(
    amount: Balance,
    idx_in: usize,
    idx_out: usize,
    balances: &[Balance],
    ann: Balance,
    precision: Balance,
) -> Option<Balance> {
    let new_reserve_out = balances[idx_out].checked_sub(amount)?;

    let d = calculate_d::<N>(balances, ann, precision)?;
    let xp: Vec<Balance> = balances
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != idx_in)
        .map(|(idx, v)| if idx == idx_out { new_reserve_out } else { *v })
        .collect();

    calculate_y::<N_Y>(&xp, d, ann, precision)
}

/// Calculate required amount of asset b when adding liquidity of asset a.
///
/// Note: currently here to be backwards compatible with 2-asset support until decided how to do add liquidity
///
/// new_reserve_b = (reserve_a + amount) * reserve_b / reserve_a
///
/// required_amount = new_reserve_b - asset_b_reserve
///
pub fn calculate_asset_b_required(
    asset_a_reserve: Balance,
    asset_b_reserve: Balance,
    updated_a_reserve: Balance,
) -> Option<Balance> {
    let (reserve_a, reserve_b, updated_reserve_a) = to_u256!(asset_a_reserve, asset_b_reserve, updated_a_reserve);
    let updated_reserve_b =
        Balance::try_from(updated_reserve_a.checked_mul(reserve_b)?.checked_div(reserve_a)?).ok()?;
    updated_reserve_b.checked_sub(asset_b_reserve)
}

pub fn calculate_d<const N: u8>(xp: &[Balance], ann: Balance, precision: Balance) -> Option<Balance> {
    let two_u256 = to_u256!(2_u128);
    let n_coins = to_u256!(xp.len());

    //let mut xp_hp: [U256; 2] = [to_u256!(xp[0]), to_u256!(xp[1])];
    let mut xp_hp: Vec<U256> = xp.iter().map(|v| to_u256!(*v)).collect();
    xp_hp.sort();

    let mut s_hp = U256::zero();

    for x in xp_hp.iter() {
        s_hp = s_hp.checked_add(*x)?;
    }

    if s_hp == U256::zero() {
        return Some(Balance::zero());
    }

    let mut d = s_hp;

    let (ann_hp, precision_hp) = to_u256!(ann, precision);

    for _ in 0..N {
        let d_p = xp_hp
            .iter()
            .try_fold(d, |acc, v| acc.checked_mul(d)?.checked_div(v.checked_mul(n_coins)?))?;
        let d_prev = d;

        d = ann_hp
            .checked_mul(s_hp)?
            .checked_add(d_p.checked_mul(n_coins)?)?
            .checked_mul(d)?
            .checked_div(
                ann_hp
                    .checked_sub(U256::one())?
                    .checked_mul(d)?
                    .checked_add(n_coins.checked_add(U256::one())?.checked_mul(d_p)?)?,
            )?
            // adding two here is sufficient to account for rounding
            // errors, AS LONG AS the minimum reserves are 2 for each
            // asset. I.e., as long as xp_hp[0] >= 2 and xp_hp[1] >= 2
            // adding two guarantees that this function will return
            // a value larger than or equal to the correct D invariant
            .checked_add(two_u256)?;

        if has_converged(d_prev, d, precision_hp) {
            // If runtime-benchmarks - dont return and force max iterations
            #[cfg(not(feature = "runtime-benchmarks"))]
            return Balance::try_from(d).ok();
        }
    }

    Balance::try_from(d).ok()
}

fn calculate_y<const N: u8>(xp: &[Balance], d: Balance, ann: Balance, precision: Balance) -> Option<Balance> {
    let (d_hp, n_coins_hp, ann_hp, precision_hp) = to_u256!(d, xp.len().checked_add(1)?, ann, precision);
    let mut xp_hp: Vec<U256> = xp.iter().map(|v| to_u256!(*v)).collect();
    xp_hp.sort();

    let two_hp = to_u256!(2u128);
    let mut s_hp = U256::zero();
    for x in xp_hp.iter() {
        s_hp = s_hp.checked_add(*x)?;
    }
    let mut c = d_hp;

    for _i in 0..xp.len() {
        c = c.checked_mul(d_hp)?.checked_div(xp_hp[_i].checked_mul(n_coins_hp)?)?;
    }

    c = c.checked_mul(d_hp)?.checked_div(ann_hp.checked_mul(n_coins_hp)?)?;

    let b = s_hp.checked_add(d_hp.checked_div(ann_hp)?)?;
    let mut y = d_hp;

    for _i in 0..N {
        let y_prev = y;
        y = y
            .checked_mul(y)?
            .checked_add(c)?
            .checked_div(two_hp.checked_mul(y)?.checked_add(b)?.checked_sub(d_hp)?)?
            .checked_add(two_hp)?;

        if has_converged(y_prev, y, precision_hp) {
            // If runtime-benchmarks - dont return and force max iterations
            #[cfg(not(feature = "runtime-benchmarks"))]
            return Balance::try_from(y).ok();
        }
    }
    Balance::try_from(y).ok()
}

#[inline]
fn has_converged(v0: U256, v1: U256, precision: U256) -> bool {
    let diff = abs_diff(v0, v1);

    if (v1 <= v0 && diff < precision) || (v1 > v0 && diff <= precision) {
        return true;
    }

    false
}

#[inline]
fn abs_diff(d0: U256, d1: U256) -> U256 {
    if d1 >= d0 {
        // This is safe due the previous condition
        d1 - d0
    } else {
        d0 - d1
    }
}

#[cfg(test)]
mod test_two_assets_math {
    const D_ITERATIONS: u8 = 128;
    const Y_ITERATIONS: u8 = 64;

    use super::*;
    use crate::stableswap::math::invariants::ONE;
    use crate::types::Balance;

    #[test]
    fn test_ann() {
        assert_eq!(calculate_ann(2, 1u128), Some(4u128));
        assert_eq!(calculate_ann(2, 10u128), Some(40u128));
        assert_eq!(calculate_ann(2, 100u128), Some(400u128));
    }

    #[test]
    fn test_d() {
        let precision = 1_u128;

        let reserves = [1000u128, 1000u128];
        let ann = 4u128;
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&reserves, ann, precision),
            Some(2000u128 + 2u128)
        );

        let reserves = [1_000_000_000_000_000_000_000u128, 1_000_000_000_000_000_000_000u128];
        let ann = 4u128;
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&reserves, ann, precision),
            Some(2_000_000_000_000_000_000_000u128 + 2u128)
        );
    }

    #[test]
    fn test_d_with_zero_reserves() {
        let precision = 1_u128;
        let reserves = [0u128, 0u128];
        let ann = 4u128;
        assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, ann, precision), Some(0u128));
    }

    #[test]
    fn test_y_given_in() {
        let precision = 1_u128;
        let reserves = [1000u128, 2000u128];
        let ann = 4u128;

        let amount_in = 100u128;
        assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, ann, precision), Some(2942u128));
        assert_eq!(
            calculate_y_given_in::<D_ITERATIONS, Y_ITERATIONS>(amount_in, 0, 1, &reserves, ann, precision),
            Some(2000u128 - 121u128)
        );
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&[1100u128, 2000u128 - 125u128], ann, precision),
            Some(2942u128)
        );
    }

    #[test]
    fn test_y_given_out() {
        let precision = 1_u128;
        let reserves = [1000u128, 2000u128];
        let ann = 4u128;

        let amount_out = 100u128;

        let expected_in = 83u128;

        assert_eq!(calculate_d::<D_ITERATIONS>(&reserves, ann, precision), Some(2942u128));

        assert_eq!(
            calculate_y_given_out::<D_ITERATIONS, Y_ITERATIONS>(amount_out, 0, 1, &reserves, ann, precision),
            Some(1000u128 + expected_in)
        );
        assert_eq!(
            calculate_d::<D_ITERATIONS>(&[1000u128 + expected_in, 2000u128 - amount_out], ann, precision),
            Some(2946u128)
        );
    }

    #[test]
    fn test_d_case() {
        let amp = 400u128;
        let ann = amp * 4u128;

        let precision = 1u128;

        let result = calculate_d::<D_ITERATIONS>(&[500000000000008580273458u128, 10u128], ann, precision);

        assert!(result.is_some());
    }

    #[test]
    fn test_d_case2() {
        let amp = 168u128;
        let ann = amp * 4u128;

        let precision = 1u128;

        let result = calculate_d::<D_ITERATIONS>(&[500000000000000000000010u128, 11u128], ann, precision);

        assert!(result.is_some());
    }

    #[test]
    fn test_case_03() {
        let reserve_in: Balance = 95329220803912837655;
        let reserve_out: Balance = 57374284583541134907;
        let amp: u128 = 310;

        let ann = amp * 4u128;

        let precision = 1u128;

        let d = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision);

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
    }
}

#[cfg(test)]
mod invariants {
    use super::Balance;
    use super::*;
    use super::{calculate_in_given_out, calculate_out_given_in, calculate_shares};
    use proptest::prelude::*;
    use proptest::proptest;

    pub const ONE: Balance = 1_000_000_000_000;

    const D_ITERATIONS: u8 = 255;
    const Y_ITERATIONS: u8 = 64;

    const RESERVE_RANGE: (Balance, Balance) = (100_000 * ONE, 100_000_000 * ONE);
    const LOW_RESERVE_RANGE: (Balance, Balance) = (10_u128, 11_u128);
    const HIGH_RESERVE_RANGE: (Balance, Balance) = (500_000_000_000 * ONE, 500_000_000_001 * ONE);

    fn trade_amount() -> impl Strategy<Value = Balance> {
        1000..10000 * ONE
    }

    fn high_trade_amount() -> impl Strategy<Value = Balance> {
        500_000_000_000 * ONE..500_000_000_001 * ONE
    }

    fn asset_reserve() -> impl Strategy<Value = Balance> {
        RESERVE_RANGE.0..RESERVE_RANGE.1
    }
    fn low_asset_reserve() -> impl Strategy<Value = Balance> {
        LOW_RESERVE_RANGE.0..LOW_RESERVE_RANGE.1
    }
    fn high_asset_reserve() -> impl Strategy<Value = Balance> {
        HIGH_RESERVE_RANGE.0..HIGH_RESERVE_RANGE.1
    }

    fn amplification() -> impl Strategy<Value = Balance> {
        2..10000u128
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_d_extreme(reserve_in in low_asset_reserve(),
            reserve_out in high_asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision);

            assert!(d.is_some());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in_extreme(amount_in in high_trade_amount(),
            reserve_in in low_asset_reserve(),
            reserve_out in high_asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_out_given_in::<D_ITERATIONS, Y_ITERATIONS>(&[reserve_in, reserve_out],0,1, amount_in, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in + amount_in, reserve_out - result.unwrap() ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_out_given_in(amount_in in trade_amount(),
            reserve_in in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp * 4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_out_given_in::<D_ITERATIONS, Y_ITERATIONS>(&[reserve_in, reserve_out],0,1, amount_in, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in + amount_in, reserve_out - result.unwrap() ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_in_given_out(amount_out in trade_amount(),
            reserve_in in asset_reserve(),
            reserve_out in asset_reserve(),
            amp in amplification(),
        ) {
            let ann = amp*4u128;

            let precision = 1u128;

            let d1 = calculate_d::<D_ITERATIONS>(&[reserve_in, reserve_out], ann, precision).unwrap();

            let result = calculate_in_given_out::<D_ITERATIONS,Y_ITERATIONS>(&[reserve_in, reserve_out],0,1, amount_out, amp, precision);

            assert!(result.is_some());

            let d2 = calculate_d::<D_ITERATIONS>(&[reserve_in + result.unwrap(), reserve_out - amount_out ], ann, precision).unwrap();

            assert!(d2 >= d1);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn test_add_liquidity(
            amount_a in trade_amount(),
            amount_b in trade_amount(),
            reserve_a in asset_reserve(),
            reserve_b in asset_reserve(),
            amp in amplification(),
            issuance in asset_reserve(),
        ) {
            let precision = 1u128;

            let initial_reserves = &[reserve_a, reserve_b];
            let updated_reserves = &[reserve_a.checked_add(amount_a).unwrap(), reserve_b.checked_add(amount_b).unwrap()];

            let result = calculate_shares::<D_ITERATIONS>(initial_reserves, updated_reserves, amp, precision, issuance);

            assert!(result.is_some());
        }
    }
}
