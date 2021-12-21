use codec::{Decode, Encode};
use scale_info::TypeInfo;
use crate::types::Balance;
use num_traits::Zero;

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Debug, Encode, Decode, Clone, Copy, PartialEq, Eq, TypeInfo)]
pub struct Fee {
    pub numerator: u32,
    pub denominator: u32,
}

impl From<(u32, u32)> for Fee {
    fn from(value: (u32, u32)) -> Self {
        Fee {
            numerator: value.0,
            denominator: value.1,
        }
    }
}

pub fn calculate_pool_trade_fee(amount: Balance, fee: (u32, u32)) -> Option<Balance> {
    let fee: Fee = fee.into();

    if fee.denominator.is_zero() || fee.numerator.is_zero() {
        return Some(0);
    }

    if fee.denominator == fee.numerator {
        return Some(amount);
    }

    amount
        .checked_div(fee.denominator as Balance)?
        .checked_mul(fee.numerator as Balance)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fee_calculations_should_work() {
        let default_fee = (2, 1000).into();

        assert_eq!(calculate_pool_trade_fee(1_000, default_fee), Some(2));
        assert_eq!(
            calculate_pool_trade_fee(1_000_000_000_000, default_fee),
            Some(2_000_000_000)
        );

        let ten_percent_fee = (1, 10).into();

        assert_eq!(calculate_pool_trade_fee(1_000, ten_percent_fee), Some(100));
        assert_eq!(
            calculate_pool_trade_fee(1_000_000_000_000, ten_percent_fee),
            Some(100_000_000_000)
        );

        assert_eq!(calculate_pool_trade_fee(1_000, (1, 10).into()), Some(100));
        assert_eq!(
            calculate_pool_trade_fee(1_000_000_000_000, (1, 10).into()),
            Some(100_000_000_000)
        );

        let max_amount = Balance::MAX;

        assert_eq!(
            calculate_pool_trade_fee(max_amount, default_fee),
            Some(680564733841876926926749214863536422)
        );
        assert_eq!(
            calculate_pool_trade_fee(max_amount, ten_percent_fee),
            Some(34028236692093846346337460743176821145)
        );

        let max_fee = (1, 1).into();

        assert_eq!(calculate_pool_trade_fee(max_amount, max_fee), Some(max_amount));
        assert_eq!(calculate_pool_trade_fee(1_000, max_fee), Some(1_000));

        assert_eq!(calculate_pool_trade_fee(max_amount, (1, 1).into()), Some(max_amount));
        assert_eq!(calculate_pool_trade_fee(1_000, (1, 1).into()), Some(1_000));

        let zero_amount = 0u128;
        assert_eq!(calculate_pool_trade_fee(zero_amount, default_fee), Some(0));

        let unrealistic_fee = (1, u32::MAX).into();

        assert_eq!(
            calculate_pool_trade_fee(max_amount, unrealistic_fee),
            Some(79228162532711081671548469249)
        );

        assert_eq!(
            calculate_pool_trade_fee(max_amount, (1, u32::MAX).into()),
            Some(79228162532711081671548469249)
        );

        let unrealistic_fee = (u32::MAX, 1).into();

        assert_eq!(calculate_pool_trade_fee(max_amount, unrealistic_fee), None);
        assert_eq!(calculate_pool_trade_fee(max_amount, (u32::MAX, 1).into()), None);

        let zero_fee = (0, 0).into();

        assert_eq!(calculate_pool_trade_fee(max_amount, zero_fee), Some(0));
        assert_eq!(calculate_pool_trade_fee(1_000, zero_fee), Some(0));

        assert_eq!(calculate_pool_trade_fee(max_amount, (0, 0).into()), Some(0));
        assert_eq!(calculate_pool_trade_fee(1_000, (0, 0).into()), Some(0));

        assert_eq!(calculate_pool_trade_fee(max_amount, (1, 0).into()), Some(0));
        assert_eq!(calculate_pool_trade_fee(1_000, (0, 1).into()), Some(0));
    }
}
