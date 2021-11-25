use crate::types::Balance;

#[derive(Debug, Copy, Clone)]
pub struct Fee {
    pub numerator: u32,
    pub denominator: u32,
}

impl Default for Fee {
    fn default() -> Self {
        Fee {
            numerator: 2,
            denominator: 1000,
        } // 0.2%
    }
}

pub fn calculate_default_pool_trade_fee(amount: Balance) -> Option<Balance> {
    calculate_pool_trade_fee(amount, Fee::default())
}

pub fn calculate_pool_trade_fee(amount: Balance, fee: Fee) -> Option<Balance> {
    amount
        .checked_div(fee.denominator as Balance)?
        .checked_mul(fee.numerator as Balance)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fee_calculations_should_work() {
        assert_eq!(calculate_default_pool_trade_fee(1_000), Some(2));
        assert_eq!(calculate_default_pool_trade_fee(1_000_000_000_000), Some(2_000_000_000));

        assert_eq!(calculate_pool_trade_fee(1_000, Fee::default()), Some(2));
        assert_eq!(
            calculate_pool_trade_fee(1_000_000_000_000, Fee::default()),
            Some(2_000_000_000)
        );

        let ten_percent_fee = Fee {
            numerator: 1,
            denominator: 10,
        };

        assert_eq!(calculate_pool_trade_fee(1_000, ten_percent_fee), Some(100));
        assert_eq!(
            calculate_pool_trade_fee(1_000_000_000_000, ten_percent_fee),
            Some(100_000_000_000)
        );

        let max_amount = Balance::MAX;

        assert_eq!(
            calculate_pool_trade_fee(max_amount, Fee::default()),
            Some(680564733841876926926749214863536422)
        );
        assert_eq!(
            calculate_pool_trade_fee(max_amount, ten_percent_fee),
            Some(34028236692093846346337460743176821145)
        );

        let max_fee = Fee {
            numerator: 1,
            denominator: 1,
        };

        assert_eq!(calculate_pool_trade_fee(max_amount, max_fee), Some(max_amount));
        assert_eq!(calculate_pool_trade_fee(1_000, max_fee), Some(1_000));

        let zero_amount = 0u128;
        assert_eq!(calculate_pool_trade_fee(zero_amount, Fee::default()), Some(0));

        let unrealistic_fee = Fee {
            numerator: 1,
            denominator: u32::MAX,
        };

        assert_eq!(
            calculate_pool_trade_fee(max_amount, unrealistic_fee),
            Some(79228162532711081671548469249)
        );
    }
}
