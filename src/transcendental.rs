use core::convert::From;
use fixed::traits::FixedUnsigned;
use fixed::traits::ToFixed;
use std::ops::{AddAssign, BitOrAssign, ShlAssign, Shr, ShrAssign};

/// right-shift with rounding
fn rs<T>(operand: T) -> T
where
    T: FixedUnsigned,
{
    let lsb = T::from_num(1) >> T::FRAC_NBITS;
    (operand >> 1) + (operand & lsb)
}

/// base 2 logarithm assuming self >=1
fn log2_inner<S, D>(operand: S) -> D
where
    S: FixedUnsigned + PartialOrd<D>,
    D: FixedUnsigned,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    let two = D::from_num(2);
    let mut x = operand;
    let mut result = D::from_num(0).to_bits();
    let lsb = (D::from_num(1) >> D::FRAC_NBITS).to_bits();

    while x >= two {
        result += lsb;
        x = rs(x);
    }

    if x == D::from_num(1) {
        return D::from_num(result);
    };

    for _i in (0..D::FRAC_NBITS).rev() {
        x *= x;
        result <<= lsb;
        if x >= two {
            result |= lsb;
            x = rs(x);
        }
    }
    D::from_bits(result)
}

/// base 2 logarithm
pub fn log2<S, D>(operand: S) -> Result<D, ()>
where
    S: FixedUnsigned,
    D: FixedUnsigned + From<S>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    if operand <= S::from_num(0) {
        return Err(());
    };

    let operand = D::from(operand);
    if operand < D::from_num(1) {
        //TODO: handle this. IT needs to handle negative result but we deal only with unsigned type.
        panic!("Does not handle yet this case");
        //let inverse = D::from_num(1).checked_div(operand).unwrap();
        //return Ok(-log2_inner::<D, D>(inverse));
    };
    Ok(log2_inner::<D, D>(operand))
}

/// natural logarithm
pub fn ln<S, D>(operand: S) -> Result<D, ()>
where
    S: FixedUnsigned,
    D: FixedUnsigned + From<S>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
    S::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShrAssign + Shr,
{
    let log2_e = S::from_str("1.442695").map_err(|_| ())?;
    Ok(log2::<S, D>(operand)? / D::from(log2_e))
}

/// exponential function e^(operand)
pub fn exp<S, D>(operand: S) -> Result<D, ()>
where
    S: FixedUnsigned + PartialOrd<D>,
    D: FixedUnsigned + PartialOrd<S> + From<S>,
{
    if operand.is_zero() {
        return Ok(D::from_num(1));
    };
    if operand == S::from_num(1) {
        //TODO: make this as const somewhere
        let e = S::from_str("2.718281828459045235360287471352662497757").map_err(|_| ())?;
        return Ok(D::from(e));
    };

    let operand = D::from(operand);
    let result = operand + D::from_num(1);
    let mut term = operand;

    let result = (2..D::FRAC_NBITS).try_fold(result, |acc, i| -> Result<D, ()> {
        term = term.checked_mul(operand).ok_or(())?;
        term = term.checked_div(D::from_num(i)).ok_or(())?;
        acc.checked_add(term).ok_or(())
    })?;

    Ok(result)
}

pub fn pow<S, D>(operand: S, exponent: S) -> Result<D, ()>
where
    S: FixedUnsigned + PartialOrd<D>,
    D: FixedUnsigned + From<S>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
    S::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign + Shr + ShrAssign,
{
    if operand.is_zero() {
        return Ok(D::from_num(0));
    };
    if exponent == S::from_num(0) {
        return Ok(D::from_num(1));
    };
    if exponent == S::from_num(1) {
        return Ok(D::from(operand));
    };

    let r = if let Some(r) = ln::<S, D>(operand)?.checked_mul(exponent.into()) {
        r
    } else {
        return Err(());
    };
    let result: D = if let Ok(r) = exp(r) {
        r
    } else {
        return Err(());
    };
    let (result, oflw) = result.overflowing_to_num::<D>();
    if oflw {
        return Err(());
    };
    Ok(result)
}

/// power with integer exponent
pub fn powi<S, D>(operand: S, exponent: u32) -> Result<D, ()>
where
    S: FixedUnsigned,
    D: FixedUnsigned + From<S>,
{
    if operand == S::from_num(0) {
        return Ok(D::from_num(0));
    };
    if exponent == 0 {
        return Ok(D::from_num(1));
    };
    if exponent == 1 {
        return Ok(D::from(operand));
    };
    let operand = D::from(operand);

    let r = (1..exponent).try_fold(operand, |acc, _| acc.checked_mul(operand));

    r.ok_or(())
}

#[cfg(test)]
use fixed::types::U64F64;

#[test]
fn powi_works() {
    type S = U64F64;
    type D = U64F64;

    assert_eq!(powi(S::from_num(2), 2), Ok(D::from_num(4)));
}

#[cfg(test)]
use crate::types::FixedBalance;

#[test]
fn pow_works() {
    type S = FixedBalance;
    type D = FixedBalance;
    assert_eq!(
        pow(S::from_num(22.1234), S::from_num(2.1)),
        Ok(D::from_num(667.097035126091))
    );
}
