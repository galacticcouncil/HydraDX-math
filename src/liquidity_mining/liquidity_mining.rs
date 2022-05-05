use crate::MathError;

use sp_arithmetic::{
    traits::{CheckedAdd, CheckedDiv, CheckedMul},
    FixedPointNumber, FixedU128,
};

use core::convert::TryInto;

type Balance = u128;

/// This function calculate loyalty multiplier or error.
///
/// `t = periodNow - periodAdded`
/// `𝞣 = t/[(initial_reward_percentage + 1) * scale_coef]`
/// `num = [𝞣 + (𝞣 * initial_reward_percentage) + initial_reward_percentage]`
/// `denom = [𝞣 + (𝞣 * initial_reward_percentage) + 1]`
///
/// `loyalty_multiplier = num/denom`

pub fn calculate_loyalty_multiplier(
    periods: u32,
    initial_reward_percentage: FixedU128,
    scale_coef: u32,
) -> Result<FixedU128, MathError> {
    let denom = initial_reward_percentage
        .checked_add(&1.into())
        .ok_or(MathError::Overflow)?
        .checked_mul(&FixedU128::from(scale_coef as u128))
        .ok_or(MathError::Overflow)?;

    let periods = FixedU128::from(TryInto::<u128>::try_into(periods).map_err(|_e| MathError::Overflow)?);
    let tau = periods.checked_div(&denom).ok_or(MathError::Overflow)?;

    //tau * initial_reward_percentage
    let tau_mul_initial_reward_percentage = tau.checked_mul(&initial_reward_percentage).ok_or(MathError::Overflow)?;

    //tau + (tau * initial_reward_percentage)
    let tau_add_tau_mul_initial_reward_percentage = tau
        .checked_add(&tau_mul_initial_reward_percentage)
        .ok_or(MathError::Overflow)?;

    //tau + (tau * initial_reward_percentage) + initial_reward_percentage
    let num = tau_add_tau_mul_initial_reward_percentage
        .checked_add(&initial_reward_percentage)
        .ok_or(MathError::Overflow)?;

    //tau + (tau * initial_reward_percentage) + 1
    let denom = tau_add_tau_mul_initial_reward_percentage
        .checked_add(&1.into())
        .ok_or(MathError::Overflow)?;

    num.checked_div(&denom).ok_or(MathError::Overflow)
}

/// This function return `GlobalPool`'s reward per one period or error.
/// Reward per period is capped by `max_reward_per_period`.             
pub fn calculate_global_pool_reward_per_period(
    yield_per_period: FixedU128,
    total_pool_shares_z: Balance,
    max_reward_per_period: Balance,
) -> Result<Balance, MathError> {
    Ok(yield_per_period
        .checked_mul_int(total_pool_shares_z)
        .ok_or(MathError::Overflow)?
        .min(max_reward_per_period))
}

/// This function calculate and return reward per share or error.
pub fn calculate_accumulated_rps(
    accumulated_rps_now: Balance,
    total_shares: Balance,
    reward: Balance,
) -> Result<Balance, MathError> {
    reward
        .checked_div(total_shares)
        .ok_or(MathError::Overflow)?
        .checked_add(accumulated_rps_now)
        .ok_or(MathError::Overflow)
}

/// This function calculate and return `(user_rewards, unclaimable_rewards)`.
pub fn calculate_user_reward(
    accumulated_rpvs: Balance,
    valued_shares: Balance, // Value of shares at the time of entry in incentivized tokens.
    accumulated_claimed_rewards: Balance,
    accumulated_rpvs_now: Balance,
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

/// This function calculate account's valued shares[`Balance`] or error.
pub fn calculate_valued_shares(shares: Balance, incentivized_asset_balance: Balance) -> Result<Balance, MathError> {
    shares
        .checked_mul(incentivized_asset_balance)
        .ok_or(MathError::Overflow)
}

/// This function calculate liq. pool's shares amount in `GlobalPool` or error.
pub fn calculate_global_pool_shares(valued_shares: Balance, multiplier: FixedU128) -> Result<Balance, MathError> {
    multiplier.checked_mul_int(valued_shares).ok_or(MathError::Overflow)
}

/// General formula to calculate reward. Usage depends on type of rps and shares used for
/// calculations
pub fn calculate_reward(
    accumulated_rps_start: Balance,
    accumulated_rps_now: Balance,
    shares: Balance,
) -> Result<Balance, MathError> {
    accumulated_rps_now
        .checked_sub(accumulated_rps_start)
        .ok_or(MathError::Overflow)?
        .checked_mul(shares)
        .ok_or(MathError::Overflow)
}
