use sp_arithmetic::FixedU128;
use crate::types::Balance;

/// Fee parameters - minimum and maximum fee, decay and amplification.
#[derive(Debug)]
pub struct FeeParams<Fee> {
    pub(crate) min_fee: Fee,
    pub(crate) max_fee: Fee,
    pub(crate) decay: FixedU128,
    pub(crate) amplification: FixedU128,
}

/// Oracle entry data for an asset, providing amount in and out and total liquidity of an asset.
#[derive(Debug)]
pub struct OracleEntry {
    pub amount_in: Balance,
    pub amount_out: Balance,
    pub liquidity: Balance,
}

impl OracleEntry {
    pub(super) fn net_volume(&self, direction: NetVolumeDirection) -> (Balance, bool) {
        match direction {
            NetVolumeDirection::OutIn => (
                self.amount_out.abs_diff(self.amount_in),
                self.amount_out < self.amount_in,
            ),
            NetVolumeDirection::InOut => (
                self.amount_out.abs_diff(self.amount_in),
                self.amount_out > self.amount_in,
            ),
        }
    }
}

/// Internal helper enum to indicate the direction of the liquidity.
#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) enum NetVolumeDirection {
    /// Amount Out - Amount in. Used to calculate asset fee.
    OutIn,
    /// Amount In - Amount Out. Used to calculate protocol fee.
    InOut,
}