use crate::{assert_eq_approx, types::Balance};
use proptest::prelude::*;
use sp_arithmetic::traits::One;
use sp_arithmetic::{
    traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub},
    FixedPointNumber, FixedU128,
};

fn periods() -> impl Strategy<Value = u32> {
    0..=u32::MAX
}

fn initial_reward_percentage() -> impl Strategy<Value = u128> {
    1..=999_999_999_999_999_999_u128 //< FixedU128::one()
}

fn accumulated_rpvs() -> impl Strategy<Value = Balance> {
    1..=1_000_000_000_000_000_u128
}

//this value is alwaych >= accumulated_rpvs
fn accumulated_rpvs_now() -> impl Strategy<Value = Balance> {
    1_000_000_000_000_000..1_000_000_000_000_000_000_u128
}

fn valued_shares() -> impl Strategy<Value = Balance> {
    1_000..=100_000_000_u128
}

fn accumulated_claimed_rewards() -> impl Strategy<Value = Balance> {
    0..3_000_000_000_000_000_000_u128
}

fn loyalty_multiplier() -> impl Strategy<Value = u128> {
    //FixedU128::from_inner(999_999_999_999_999_999) should be max multiplier we can reach
    1_000_000..999_999_999_999_999_999_u128 //0.000_000_000_001 - 0.999_999
}

prop_compose! {
    fn get_scale_coef_and_periods_gte() (
        periods in 0..u32::MAX/2
    )
    (
        scale_coef in periods..u32::MAX, periods in Just(periods)
    ) -> (u32, u32) {
        (scale_coef, periods)
    }
}

prop_compose! {
    fn get_scale_coef_and_periods_lte() (
        periods in u32::MAX/2..u32::MAX
    )
    (
        scale_coef in 0..periods, periods in Just(periods)
    ) -> (u32, u32) {
        (scale_coef, periods)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_000))]
    #[test]
    fn calculate_loyalty_multiplier_scale_coef_lte_periods(
        (scale_coef, periods) in get_scale_coef_and_periods_lte(),
        initial_reward_percentage in initial_reward_percentage(),
    ) {
        assert!(scale_coef <= periods, "scale_coef > periods");

        let b = FixedU128::from_inner(initial_reward_percentage);
        let multiplier = crate::liquidity_mining::calculate_loyalty_multiplier(
            periods,
            b,
            scale_coef,
        ).unwrap();

        assert!(multiplier < FixedU128::one(), "loyalty multiplier is >= 1");

        //b + (1 - b)/2;
        let bound = FixedU128::one()
                .checked_sub(&b).unwrap()
                .checked_div(&FixedU128::from(2_u128)).unwrap()
                .checked_add(&b).unwrap();

        //multiplier is between b + (1 - b)/2 and 1 if T >= scaleCoef
        assert!(multiplier >= bound && multiplier <= FixedU128::one());

        //LoyaltyFactor * (t + tb + scaleCoef*(b + 1)) == t + tb + b*scaleCoef*(b + 1)
        let t = FixedU128::from(TryInto::<u128>::try_into(periods).unwrap());
        let t_add_tb =  b
            .checked_mul(&t).unwrap()
            .checked_add(&t).unwrap();

        let scale_coef_mul_b_add_one = FixedU128::one()
            .checked_add(&b).unwrap()
            .checked_mul(&FixedU128::from(scale_coef as u128)).unwrap();

        let lhs = t_add_tb
            .checked_add(&scale_coef_mul_b_add_one).unwrap()
            .checked_mul(&multiplier).unwrap();

        let rhs = b
            .checked_mul(&scale_coef_mul_b_add_one).unwrap()
            .checked_add(&t_add_tb).unwrap();

        let tolerance = FixedU128::from_inner(20_000_000_000); //0.000_000_02
        assert_eq_approx!(
            lhs,
            rhs,
            tolerance,
            "loyalty multiplier, LoyaltyFactor * (t + tb + scaleCoef*(b + 1)) == t + tb + b*scaleCoef*(b + 1)"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_000))]
    #[test]
    fn calculate_loyalty_multiplier_periods_gte_scale_coef(
        (scale_coef, periods) in get_scale_coef_and_periods_gte(),
        initial_reward_percentage in initial_reward_percentage(),
    ) {
        let b = FixedU128::from_inner(initial_reward_percentage);
        let multiplier = crate::liquidity_mining::calculate_loyalty_multiplier(
            periods,
            b,
            scale_coef,
        ).unwrap();

        assert!(multiplier < FixedU128::one(), "loyalty multiplier is >= 1");

        //b + (1 - b)/2;
        let bound = FixedU128::one()
                .checked_sub(&b).unwrap()
                .checked_div(&FixedU128::from(2_u128)).unwrap()
                .checked_add(&b).unwrap();

        //multiplier is between b + (1 - b)/2 and 1 if T >= scaleCoef
        assert!(multiplier >= b && multiplier <= bound);

        //LoyaltyFactor * (t + tb + scaleCoef*(b + 1)) == t + tb + b*scaleCoef*(b + 1)
        let t = FixedU128::from(TryInto::<u128>::try_into(periods).unwrap());
        let t_add_tb =  b
            .checked_mul(&t).unwrap()
            .checked_add(&t).unwrap();

        let scale_coef_mul_b_add_one = FixedU128::one()
            .checked_add(&b).unwrap()
            .checked_mul(&FixedU128::from(scale_coef as u128)).unwrap();

        let lhs = t_add_tb
            .checked_add(&scale_coef_mul_b_add_one).unwrap()
            .checked_mul(&multiplier).unwrap();

        let rhs = b
            .checked_mul(&scale_coef_mul_b_add_one).unwrap()
            .checked_add(&t_add_tb).unwrap();

        let tolerance = FixedU128::from_inner(20_000_000_000); //0.000_000_02
        assert_eq_approx!(
            lhs,
            rhs,
            tolerance,
            "loyalty multiplier, LoyaltyFactor * (t + tb + scaleCoef*(b + 1)) == t + tb + b*scaleCoef*(b + 1)"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_000))]
    #[test]
    fn calculate_loyalty_multiplier_should_eqaul_to_bound_when_period_is_equal_scale_coef(
        periods in periods(),
        initial_reward_percentage in initial_reward_percentage(),
    ) {
        //This case is never hit by test above, that's why there is special test only for this
        let scale_coef = periods;
        let b = FixedU128::from_inner(initial_reward_percentage);
        let multiplier = crate::liquidity_mining::calculate_loyalty_multiplier(
            periods,
            b,
            scale_coef,
        ).unwrap();

        //b + (1 - b)/2;
        let bound = FixedU128::one()
                .checked_sub(&b).unwrap()
                .checked_div(&FixedU128::from(2_u128)).unwrap()
                .checked_add(&b).unwrap();

        let tolerance = FixedU128::from_inner(1_000); //0.000_000_000_000_001
        assert_eq_approx!(multiplier, bound, tolerance, "loyalty multiplier, periods == scale_coef");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_000))]
    #[test]
    fn calculate_user_reward(
        accumulated_rpvs in accumulated_rpvs(),
        accumulated_rpvs_now in accumulated_rpvs_now(),
        valued_shares in valued_shares(),
        accumulated_claimed_rewards in accumulated_claimed_rewards(),
        loyalty_multiplier in loyalty_multiplier()
    ) {
        let loyalty_multiplier = FixedU128::from_inner(loyalty_multiplier);

        let (user_rewards, unclaimable_rewards) = crate::liquidity_mining::calculate_user_reward(
            accumulated_rpvs,
            valued_shares,
            accumulated_claimed_rewards,
            accumulated_rpvs_now,
            loyalty_multiplier).unwrap();

        let max_rewards = user_rewards
            .checked_add(unclaimable_rewards).unwrap()
            .checked_add(accumulated_claimed_rewards).unwrap();

        let p = accumulated_rpvs_now
            .checked_sub(accumulated_rpvs).unwrap()
            .checked_mul(valued_shares).unwrap();

        assert!(max_rewards == p, "max_rewards ~= (accumulated_rpvs_now - accumulated_rpvs) * valued_shares");

        let tolerance = 1_u128; //0.000_000_000_000_001
        assert_eq_approx!(
            user_rewards.checked_add(accumulated_claimed_rewards).unwrap(),
            loyalty_multiplier.checked_mul_int(max_rewards).unwrap(),
            tolerance,
            "(user_rewards + accumulated_claimed_rewards) ~= loyalty_factor * max_rewards"
        );
    }
}
