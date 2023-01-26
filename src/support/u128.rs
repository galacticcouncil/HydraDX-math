use crate::support::traits::{CheckedAddInto, CheckedDivInner, CheckedMulInner, CheckedMulInto};
use primitive_types::U256;

impl CheckedAddInto for u128 {
    type Output = U256;

    fn checked_add_into(&self, other: &Self) -> Option<Self::Output> {
        let s = Self::Output::from(*self);
        let o = Self::Output::from(*other);
        s.checked_add(o)
    }
}

impl CheckedMulInto for u128 {
    type Output = U256;

    fn checked_mul_into(&self, other: &Self) -> Option<Self::Output> {
        let s = Self::Output::from(*self);
        let o = Self::Output::from(*other);
        s.checked_mul(o)
    }
}

impl CheckedDivInner for U256 {
    type Inner = u128;

    fn checked_div_inner(&self, other: &Self::Inner) -> Option<Self> {
        self.checked_div(Self::from(*other))
    }
}

impl CheckedMulInner for U256 {
    type Inner = u128;

    fn checked_mul_inner(&self, other: &Self::Inner) -> Option<Self> {
        self.checked_mul(Self::from(*other))
    }
}

#[test]
fn checked_add_into_works_for_u128() {
    let r = 100u128;
    let result = r.checked_add_into(&200u128).unwrap();
    assert_eq!(result, U256::from(300u128));
}

#[test]
fn checked_mul_into_works_for_u128() {
    let r = 100u128;
    let result = r.checked_mul_into(&200u128).unwrap();
    assert_eq!(result, U256::from(20000u128));
}
