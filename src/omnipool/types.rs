use crate::omnipool::types::BalanceUpdate::{Decrease, Increase};
use num_traits::{CheckedAdd, CheckedSub};
use sp_arithmetic::{FixedPointNumber, FixedU128};
use sp_std::ops::{Add, Deref};

/// Asset state representation including asset pool reserve.
#[derive(Clone, Default, Debug)]
pub struct AssetReserveState<Balance> {
    /// Quantity of asset in omnipool
    pub reserve: Balance,
    /// Quantity of Hub Asset matching this asset
    pub hub_reserve: Balance,
    /// Quantity of LP shares for this asset
    pub shares: Balance,
    /// Quantity of LP shares for this asset owned by protocol
    pub protocol_shares: Balance,
    /// TVL of asset
    pub tvl: Balance,
}

impl<Balance> AssetReserveState<Balance>
where
    Balance: Into<<FixedU128 as FixedPointNumber>::Inner> + Copy + CheckedAdd + CheckedSub + Default,
{
    /// Calculate price for actual state
    pub(crate) fn price(&self) -> Option<FixedU128> {
        FixedU128::checked_from_rational(self.hub_reserve.into(), self.reserve.into())
    }

    /// Update current asset state with given delta changes.
    pub fn delta_update(self, delta: &AssetStateChange<Balance>) -> Option<Self> {
        Some(Self {
            reserve: (delta.delta_reserve + self.reserve)?,
            hub_reserve: (delta.delta_hub_reserve + self.hub_reserve)?,
            shares: (delta.delta_shares + self.shares)?,
            protocol_shares: (delta.delta_protocol_shares + self.protocol_shares)?,
            tvl: (delta.delta_tvl + self.tvl)?,
        })
    }
}

/// Indicates whether delta amount should be added or subtracted.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BalanceUpdate<Balance> {
    Increase(Balance),
    Decrease(Balance),
}

impl<Balance: CheckedAdd + CheckedSub + PartialOrd + Copy + Default> BalanceUpdate<Balance> {
    /// Merge two update together
    pub fn merge(self, other: Self) -> Option<Self> {
        self.checked_add(&other)
    }
}

/// The addition operator + for BalanceUpdate.
///
/// Panics if overflows in debug builds, in non-debug debug it wraps instead. Use `checked_add` for safe operation.
///
/// # Example
///
/// ```ignore
/// assert_eq!(BalanceUpdate::Increase(100) + BalanceUpdate::Increase(100), BalanceUpdate::Increase(200));
/// ```
impl<Balance: CheckedAdd + CheckedSub + PartialOrd + Default> Add<Self> for BalanceUpdate<Balance> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Increase(a), Increase(b)) => BalanceUpdate::Increase(a + b),
            (Decrease(a), Decrease(b)) => BalanceUpdate::Decrease(a + b),
            (Increase(a), Decrease(b)) => {
                if a >= b {
                    BalanceUpdate::Increase(a - b)
                } else {
                    BalanceUpdate::Decrease(b - a)
                }
            }
            (Decrease(a), Increase(b)) => {
                if a >= b {
                    BalanceUpdate::Decrease(a - b)
                } else {
                    BalanceUpdate::Increase(b - a)
                }
            }
        }
    }
}

/// Performs addition that returns `None` instead of wrapping around on overflow
impl<Balance: CheckedAdd + CheckedSub + PartialOrd + Copy + Default> CheckedAdd for BalanceUpdate<Balance> {
    fn checked_add(&self, v: &Self) -> Option<Self> {
        match (self, v) {
            (Increase(a), Increase(b)) => Some(BalanceUpdate::Increase(a.checked_add(b)?)),
            (Decrease(a), Decrease(b)) => Some(BalanceUpdate::Decrease(a.checked_add(b)?)),
            (Increase(a), Decrease(b)) => {
                if a >= b {
                    Some(BalanceUpdate::Increase(a.checked_sub(b)?))
                } else {
                    Some(BalanceUpdate::Decrease(b.checked_sub(a)?))
                }
            }
            (Decrease(a), Increase(b)) => {
                if a >= b {
                    Some(BalanceUpdate::Decrease(a.checked_sub(b)?))
                } else {
                    Some(BalanceUpdate::Increase(b.checked_sub(a)?))
                }
            }
        }
    }
}

impl<Balance: Default> Default for BalanceUpdate<Balance> {
    fn default() -> Self {
        BalanceUpdate::Increase(Balance::default())
    }
}

impl<Balance: Default> Deref for BalanceUpdate<Balance> {
    type Target = Balance;

    fn deref(&self) -> &Self::Target {
        match self {
            Increase(amount) | Decrease(amount) => amount,
        }
    }
}

impl<Balance: Into<<FixedU128 as FixedPointNumber>::Inner> + CheckedAdd + CheckedSub + Copy + Default> Add<Balance>
    for BalanceUpdate<Balance>
{
    type Output = Option<Balance>;

    fn add(self, rhs: Balance) -> Self::Output {
        match &self {
            BalanceUpdate::Increase(amount) => rhs.checked_add(amount),
            BalanceUpdate::Decrease(amount) => rhs.checked_sub(amount),
        }
    }
}

/// Delta changes of asset state
#[derive(Default, Clone, Debug)]
pub struct AssetStateChange<Balance>
where
    Balance: Default,
{
    pub delta_reserve: BalanceUpdate<Balance>,
    pub delta_hub_reserve: BalanceUpdate<Balance>,
    pub delta_shares: BalanceUpdate<Balance>,
    pub delta_protocol_shares: BalanceUpdate<Balance>,
    pub delta_tvl: BalanceUpdate<Balance>,
}

/// Delta changes after a trade is executed
#[derive(Default)]
pub struct TradeStateChange<Balance>
where
    Balance: Default,
{
    pub asset_in: AssetStateChange<Balance>,
    pub asset_out: AssetStateChange<Balance>,
    pub delta_imbalance: BalanceUpdate<Balance>,
    pub hdx_hub_amount: Balance,
}

/// Delta changes after a trade with hub asset is executed.
#[derive(Default)]
pub struct HubTradeStateChange<Balance>
where
    Balance: Default,
{
    pub asset: AssetStateChange<Balance>,
    pub delta_imbalance: BalanceUpdate<Balance>,
}

/// Delta changes after add or remove liquidity.
#[derive(Default)]
pub struct LiquidityStateChange<Balance>
where
    Balance: Default,
{
    pub asset: AssetStateChange<Balance>,
    pub delta_imbalance: BalanceUpdate<Balance>,
    pub delta_position_reserve: BalanceUpdate<Balance>,
    pub delta_position_shares: BalanceUpdate<Balance>,
    pub lp_hub_amount: Balance,
}

#[derive(Debug)]
pub struct Position<Balance> {
    /// Amount of asset added to omnipool
    pub amount: Balance,
    /// Quantity of LP shares owned by LP
    pub shares: Balance,
    /// Price at which liquidity was provided
    pub price: FixedU128,
}

#[cfg(test)]
mod tests {
    use super::BalanceUpdate;
    use super::CheckedAdd;
    //use cool_asserts::assert_panics;

    #[test]
    fn balance_update_addition_works() {
        assert_eq!(
            BalanceUpdate::Increase(100) + BalanceUpdate::Increase(100),
            BalanceUpdate::Increase(200)
        );
        assert_eq!(
            BalanceUpdate::Increase(500) + BalanceUpdate::Decrease(300),
            BalanceUpdate::Increase(200)
        );
        assert_eq!(
            BalanceUpdate::Increase(100) + BalanceUpdate::Decrease(300),
            BalanceUpdate::Decrease(200)
        );
        assert_eq!(
            BalanceUpdate::Increase(100) + BalanceUpdate::Decrease(0),
            BalanceUpdate::Increase(100)
        );
        assert_eq!(
            BalanceUpdate::Increase(0) + BalanceUpdate::Decrease(100),
            BalanceUpdate::Decrease(100)
        );

        assert_eq!(
            BalanceUpdate::Decrease(100) + BalanceUpdate::Decrease(300),
            BalanceUpdate::Decrease(400)
        );
        assert_eq!(
            BalanceUpdate::Decrease(200) + BalanceUpdate::Increase(100),
            BalanceUpdate::Decrease(100)
        );
        assert_eq!(
            BalanceUpdate::Decrease(200) + BalanceUpdate::Increase(300),
            BalanceUpdate::Increase(100)
        );
        assert_eq!(
            BalanceUpdate::Decrease(200) + BalanceUpdate::Increase(0),
            BalanceUpdate::Decrease(200)
        );
        assert_eq!(
            BalanceUpdate::Decrease(0) + BalanceUpdate::Decrease(100),
            BalanceUpdate::Decrease(100)
        );

        assert_eq!(
            BalanceUpdate::Increase(100) + BalanceUpdate::Decrease(100),
            BalanceUpdate::Increase(0)
        );
        assert_eq!(
            BalanceUpdate::Decrease(100) + BalanceUpdate::Increase(100),
            BalanceUpdate::Decrease(0)
        );
        assert_eq!(
            BalanceUpdate::Increase(0) + BalanceUpdate::Decrease(0),
            BalanceUpdate::Increase(0)
        );
        assert_eq!(
            BalanceUpdate::Decrease(0) + BalanceUpdate::Increase(0),
            BalanceUpdate::Decrease(0)
        );

        assert_eq!(
            BalanceUpdate::Increase(u128::MAX) + BalanceUpdate::Decrease(1),
            BalanceUpdate::Increase(u128::MAX - 1)
        );

        //assert_panics!(BalanceUpdate::Increase(u128::MAX) + BalanceUpdate::Increase(1));
        //assert_panics!(BalanceUpdate::Decrease(u128::MAX) + BalanceUpdate::Decrease(1));
    }

    #[test]
    fn balance_update_to_balance_addition_works() {
        let zero = 0u32;
        assert_eq!(BalanceUpdate::Increase(100u32) + 200u32, Some(300));
        assert_eq!(BalanceUpdate::Decrease(50u32) + 100u32, Some(50));
        assert_eq!(BalanceUpdate::Decrease(50u32) + 50u32, Some(0));
        assert_eq!(BalanceUpdate::Decrease(50u32) + zero, None);
        assert_eq!(BalanceUpdate::Increase(50u32) + zero, Some(50));

        assert_eq!(BalanceUpdate::Decrease(100u32) + 50u32, None);
    }

    #[test]
    fn balance_update_safe_addition_works() {
        assert_eq!(
            BalanceUpdate::Increase(100).checked_add(&BalanceUpdate::Increase(100)),
            Some(BalanceUpdate::Increase(200))
        );
        assert_eq!(
            BalanceUpdate::Increase(500).checked_add(&BalanceUpdate::Decrease(300)),
            Some(BalanceUpdate::Increase(200))
        );
        assert_eq!(
            BalanceUpdate::Increase(100).checked_add(&BalanceUpdate::Decrease(300)),
            Some(BalanceUpdate::Decrease(200))
        );

        assert_eq!(
            BalanceUpdate::Increase(100).checked_add(&BalanceUpdate::Decrease(0)),
            Some(BalanceUpdate::Increase(100))
        );
        assert_eq!(
            BalanceUpdate::Increase(0).checked_add(&BalanceUpdate::Decrease(100)),
            Some(BalanceUpdate::Decrease(100))
        );

        assert_eq!(
            BalanceUpdate::Decrease(100).checked_add(&BalanceUpdate::Decrease(300)),
            Some(BalanceUpdate::Decrease(400))
        );
        assert_eq!(
            BalanceUpdate::Decrease(200).checked_add(&BalanceUpdate::Increase(100)),
            Some(BalanceUpdate::Decrease(100))
        );
        assert_eq!(
            BalanceUpdate::Decrease(200).checked_add(&BalanceUpdate::Increase(300)),
            Some(BalanceUpdate::Increase(100))
        );
        assert_eq!(
            BalanceUpdate::Decrease(200).checked_add(&BalanceUpdate::Increase(0)),
            Some(BalanceUpdate::Decrease(200))
        );
        assert_eq!(
            BalanceUpdate::Decrease(0).checked_add(&BalanceUpdate::Decrease(100)),
            Some(BalanceUpdate::Decrease(100))
        );

        assert_eq!(
            BalanceUpdate::Increase(100).checked_add(&BalanceUpdate::Decrease(100)),
            Some(BalanceUpdate::Increase(0))
        );
        assert_eq!(
            BalanceUpdate::Decrease(100).checked_add(&BalanceUpdate::Increase(100)),
            Some(BalanceUpdate::Decrease(0))
        );
        assert_eq!(
            BalanceUpdate::Increase(0).checked_add(&BalanceUpdate::Decrease(0)),
            Some(BalanceUpdate::Increase(0))
        );
        assert_eq!(
            BalanceUpdate::Decrease(0).checked_add(&BalanceUpdate::Increase(0)),
            Some(BalanceUpdate::Decrease(0))
        );

        assert_eq!(
            BalanceUpdate::Increase(u128::MAX).checked_add(&BalanceUpdate::Decrease(1)),
            Some(BalanceUpdate::Increase(u128::MAX - 1))
        );

        assert_eq!(
            BalanceUpdate::Increase(u128::MAX).checked_add(&BalanceUpdate::Increase(1)),
            None
        );
        assert_eq!(
            BalanceUpdate::Decrease(u128::MAX).checked_add(&BalanceUpdate::Decrease(1)),
            None
        );
    }
}
