use crate::omnipool::types::BalanceUpdate::{Decrease, Increase};
use num_traits::{CheckedAdd, CheckedSub};
use sp_arithmetic::{FixedPointNumber, FixedU128};
use sp_std::ops::{Add, Deref, Sub};

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
    pub(crate) fn price(&self) -> FixedU128 {
        FixedU128::from((self.hub_reserve.into(), self.reserve.into()))
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

/// Simple type to represent imbalance which can be positive or negative.
// Note: Simple prefix is used not to confuse with Imbalance trait from frame_support.
#[derive(Clone, Eq, PartialEq)]
pub struct SimpleImbalance<Balance> {
    pub value: Balance,
    pub negative: bool,
}

impl<Balance: Default> Default for SimpleImbalance<Balance> {
    fn default() -> Self {
        Self {
            value: Balance::default(),
            negative: true,
        }
    }
}

/// The addition operator + for SimpleImbalance.
///
/// Adds amount to imbalance.
///
/// Note that it returns Option<self> rather than Self.
///
/// Note: Implements `Add` instead of `CheckedAdd` because `CheckedAdd` requires the second parameter
/// to be the same type as the first while we want to add a `Balance` here.
///
/// # Example
///
/// ```ignore
/// let imbalance = SimpleImbalance{value: 100, negative: false} ;
/// assert_eq!(imbalance + 200 , Some(SimpleImbalance{value: 300, negative: false}));
/// ```
impl<Balance: CheckedAdd + CheckedSub + PartialOrd + Copy> Add<Balance> for SimpleImbalance<Balance> {
    type Output = Option<Self>;

    fn add(self, amount: Balance) -> Self::Output {
        let (value, sign) = if !self.negative {
            (self.value.checked_add(&amount)?, self.negative)
        } else if self.value < amount {
            (amount.checked_sub(&self.value)?, false)
        } else {
            (self.value.checked_sub(&amount)?, self.negative)
        };
        Some(Self { value, negative: sign })
    }
}

/// The subtraction operator - for SimpleImbalance.
///
/// Subtracts amount from imbalance.
///
/// Note that it returns Option<self> rather than Self.
///
/// # Example
///
/// ```ignore
/// let imbalance = SimpleImbalance{value: 200, negative: false} ;
/// assert_eq!(imbalance - 100 , Some(SimpleImbalance{value: 100, negative: false}));
/// ```
impl<Balance: CheckedAdd + CheckedSub + PartialOrd + Copy> Sub<Balance> for SimpleImbalance<Balance> {
    type Output = Option<Self>;

    fn sub(self, amount: Balance) -> Self::Output {
        let (value, sign) = if self.negative {
            (self.value.checked_add(&amount)?, self.negative)
        } else if self.value < amount {
            (amount.checked_sub(&self.value)?, true)
        } else {
            (self.value.checked_sub(&amount)?, self.negative)
        };
        Some(Self { value, negative: sign })
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

pub struct Position<Balance> {
    /// Amount of asset added to omnipool
    pub amount: Balance,
    /// Quantity of LP shares owned by LP
    pub shares: Balance,
    /// Price at which liquidity was provided
    pub price: FixedU128,
}
