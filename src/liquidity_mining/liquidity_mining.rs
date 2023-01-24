use crate::MathError;

use sp_arithmetic::{
    traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub},
    FixedPointNumber, FixedU128,
};

use crate::types::Balance;
use core::convert::TryInto;

/// This function calculate loyalty multiplier or error.
///
/// `t = periodNow - periodAdded`
/// `num = t + initial_reward_percentage * scale_coef`
/// `denom = t + scale_coef`
///
/// `loyalty_multiplier = num/denom`

pub fn calculate_loyalty_multiplier<Period: num_traits::CheckedSub + TryInto<u32> + TryInto<u128>>(
    periods: Period,
    initial_reward_percentage: FixedU128,
    scale_coef: u32,
) -> Result<FixedU128, MathError> {
    let periods = FixedU128::from(TryInto::<u128>::try_into(periods).map_err(|_e| MathError::Overflow)?);
    let sc_coef = FixedU128::from(scale_coef as u128);

    //t + initial_reward_percentage * scale_coef
    let num = initial_reward_percentage
        .checked_mul(&sc_coef)
        .ok_or(MathError::Overflow)?
        .checked_add(&periods)
        .ok_or(MathError::Overflow)?;

    //t + scale_coef
    let denom = periods.checked_add(&sc_coef).ok_or(MathError::Overflow)?;

    num.checked_div(&denom).ok_or(MathError::Overflow)
}

/// This function return `GlobalFarm`'s reward per one period or error.
/// Reward per period is capped by `max_reward_per_period`.             
pub fn calculate_global_farm_reward_per_period(
    yield_per_period: FixedU128,
    total_farm_shares_z: Balance,
    max_reward_per_period: Balance,
) -> Result<FixedU128, MathError> {
    Ok(yield_per_period
        .checked_mul(&FixedU128::from(total_farm_shares_z))
        .ok_or(MathError::Overflow)?
        .min(FixedU128::from(max_reward_per_period)))
}

/// This function calculate and return reward per share or error.
pub fn calculate_accumulated_rps(
    accumulated_rps_now: FixedU128,
    total_shares: Balance,
    reward: Balance,
) -> Result<FixedU128, MathError> {
    let rps = FixedU128::checked_from_rational(reward, total_shares).ok_or(MathError::DivisionByZero)?;

    rps.checked_add(&accumulated_rps_now).ok_or(MathError::Overflow)
}

/// This function calculate and return `(user_rewards, unclaimable_rewards)`.
pub fn calculate_user_reward(
    accumulated_rpvs: FixedU128,
    valued_shares: Balance, // Value of shares at the time of entry in incentivized tokens.
    accumulated_claimed_rewards: Balance,
    accumulated_rpvs_now: FixedU128,
    loyalty_multiplier: FixedU128,
) -> Result<(Balance, Balance), MathError> {
    let max_rewards = calculate_reward(accumulated_rpvs, accumulated_rpvs_now, valued_shares)?;

    if max_rewards == 0 {
        return Ok((0, 0));
    }

    let claimable_rewards = loyalty_multiplier
        .checked_mul_int(max_rewards)
        .ok_or(MathError::Overflow)?;

    let unclaimable_rewards = max_rewards.checked_sub(claimable_rewards).ok_or(MathError::Overflow)?;

    let user_rewards = claimable_rewards
        .checked_sub(accumulated_claimed_rewards)
        .ok_or(MathError::Overflow)?;

    Ok((user_rewards, unclaimable_rewards))
}

/// This function calculate account's valued shares [`Balance`] or error.
pub fn calculate_valued_shares(shares: Balance, incentivized_asset_balance: Balance) -> Result<Balance, MathError> {
    shares
        .checked_mul(incentivized_asset_balance)
        .ok_or(MathError::Overflow)
}

/// This function calculate yield farm's shares amount [`Balance`] in `GlobalFarm` or error.
pub fn calculate_global_farm_shares(valued_shares: Balance, multiplier: FixedU128) -> Result<Balance, MathError> {
    multiplier.checked_mul_int(valued_shares).ok_or(MathError::Overflow)
}

/// General formula to calculate reward. Usage depends on type of rps and shares used for
/// calculations
pub fn calculate_reward(
    accumulated_rps_start: FixedU128,
    accumulated_rps_now: FixedU128,
    shares: Balance,
) -> Result<Balance, MathError> {
    accumulated_rps_now
        .checked_sub(&accumulated_rps_start)
        .ok_or(MathError::Overflow)?
        .checked_mul_int(shares)
        .ok_or(MathError::Overflow)
}

/// This function calculate adjusted shares amount [`Balance`] or error.
pub fn calculate_adjusted_shares(shares: Balance, price_adjustment: FixedU128) -> Result<Balance, MathError> {
    price_adjustment.checked_mul_int(shares).ok_or(MathError::Overflow)
}

/// This function calculates rewards [`Balance`] for number of periods or error.
pub fn calculate_rewards_for_periods<Period: num_traits::CheckedSub + TryInto<u32> + TryInto<u128>>(
    reward_per_period: FixedU128,
    periods_since_last_update: Period,
) -> Result<Balance, MathError> {
    let periods = TryInto::<u128>::try_into(periods_since_last_update).map_err(|_e| MathError::Overflow)?;
    reward_per_period.checked_mul_int(periods).ok_or(MathError::Overflow)
}
