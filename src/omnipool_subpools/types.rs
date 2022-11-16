use primitive_types::U256;

pub trait HpCheckedMath {
    type Output;
    fn hp_checked_add(&self, other: &Self) -> Option<Self::Output>;
    fn hp_checked_mul(&self, other: &Self) -> Option<Self::Output>;
}

pub trait CheckedMathInner: Sized {
    type Inner;

    fn checked_div_inner(&self, other: &Self::Inner) -> Option<Self>;

    fn to_inner(&self) -> Option<Self::Inner>;
}

impl HpCheckedMath for u128 {
    type Output = U256;

    fn hp_checked_add(&self, other: &Self) -> Option<Self::Output> {
        let s = U256::from(*self);
        let o = U256::from(*other);

        s.checked_add(o)
    }

    fn hp_checked_mul(&self, other: &Self) -> Option<Self::Output> {
        let s = U256::from(*self);
        let o = U256::from(*other);

        s.checked_mul(o)
    }
}

impl CheckedMathInner for U256 {
    type Inner = u128;

    fn checked_div_inner(&self, other: &Self::Inner) -> Option<Self> {
        let o = U256::from(*other);
        self.checked_div(o)
    }

    fn to_inner(&self) -> Option<Self::Inner> {
        Self::Inner::try_from(*self).ok()
    }
}

#[test]
fn checked_math_inner_should_work_when_is_max() {
    let n1 = U256::from(u128::MAX);
    assert_eq!(n1.to_inner(), Some(u128::MAX));
}

#[test]
fn checked_math_inner_should_fail_when_outside_range() {
    let n1 = U256::from(u128::MAX) + 1;
    assert!(n1.to_inner().is_none());
}
