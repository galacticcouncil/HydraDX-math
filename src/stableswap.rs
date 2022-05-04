use crate::{
    ensure, round_up, to_balance, to_u256, MathError,
    MathError::{InsufficientOutReserve, Overflow, ZeroReserve},
};
use core::convert::TryFrom;
use primitive_types::U256;

type Balance = u128;

const FIXED_ROUND_UP: Balance = 1;
const N_COINS: i8 = 2;
const N_COINS_SIZE: usize = N_COINS as usize;


/// Calculating stableswap invariant D.
///
/// - `xp` - reserve amounts of assets
/// - `a` - (Amplifying const) * n ^ (n - 1)
///
/// Returns MathError in case of error
pub fn get_d(xp: [U256; N_COINS_SIZE], a: U256) -> Result<U256, MathError> {
    let n_coins_u256 = to_u256!(N_COINS);

    let mut s = to_u256!(0);
    for _x in xp {
        s = s.checked_add(_x).ok_or(Overflow)?;
    };
    if s == to_u256!(0) {
        return Ok(to_u256!(0));
    }
    let mut dprev = to_u256!(0);
    let mut d = s;
    let mut d_p: U256;

    let ann = a.checked_mul(n_coins_u256).ok_or(Overflow)?;

    for _i in 0..255 {
        d_p = d;
        for _x in xp {
            let x_times_n = _x.checked_mul(n_coins_u256).ok_or(Overflow)?;
            d_p = d_p.checked_mul(d).ok_or(Overflow)?
                     .checked_div(x_times_n).ok_or(Overflow)?;
        }
        dprev = d;
        // d = (ann * s + d_p * n_coins_u256) * d / ((ann - 1) * d + (n_coins_u256 + 1) * d_p);
        let n_plus_1 = n_coins_u256.checked_add(to_u256!(1)).ok_or(Overflow)?;
        let ann_minus_1 = ann.checked_sub(to_u256!(1)).ok_or(Overflow)?;
        let d_denominator = ann_minus_1.checked_mul(d).ok_or(Overflow)?
                                             .checked_add(
                                                 n_plus_1.checked_mul(d_p).ok_or(Overflow)?
                                             ).ok_or(Overflow)?;
        let ann_times_s = ann.checked_mul(s).ok_or(Overflow)?;
        let dp_times_n = d_p.checked_mul(n_coins_u256).ok_or(Overflow)?;
        let d_numerator = d.checked_mul(
            ann_times_s.checked_add(dp_times_n).ok_or(Overflow)?
        ).ok_or(Overflow)?;
        d = d_numerator.checked_div(d_denominator).ok_or(Overflow)?;

        // if d > dprev {
        //    if d - dprev <= to_u256!(1) {
        //        break;
        //    }
        // }
        // else if dprev - d <= to_u256!(1) {
        //    break;
        // }
    }

    Ok(d)
}


pub fn get_y_stableswap(i: i128, j: i128, x: U256, xp: [U256; N_COINS_SIZE], a: U256) -> Result<U256, MathError> {
    let n_coins_u256 = to_u256!(N_COINS);

    let d = get_d(xp, a).unwrap();
    let mut c = d;
    let mut s = to_u256!(0);
    let ann = a.checked_mul(n_coins_u256).ok_or(Overflow)?;

    let mut _x = to_u256!(0);
    for _i in 0..N_COINS_SIZE {
        if _i == (i as usize) {
            _x = x;
        }
        else if _i != (j as usize) {
            _x = xp[_i];
        }
        else {
            continue;
        }
        s = s.checked_add(_x).ok_or(Overflow)?;
        let denominator = _x.checked_mul(n_coins_u256).ok_or(Overflow)?;
        let numerator = c.checked_mul(d).ok_or(Overflow)?;
        c = numerator.checked_div(denominator).ok_or(Overflow)?;
    }

    let denominator = ann.checked_mul(n_coins_u256).ok_or(Overflow)?;
    let numerator = c.checked_mul(d).ok_or(Overflow)?;
    c = numerator.checked_div(denominator).ok_or(Overflow)?;

    let d_by_ann = d.checked_div(ann).ok_or(Overflow)?;
    let b = s.checked_add(d_by_ann).ok_or(Overflow)?;
    let mut y_prev = to_u256!(0);
    let mut y = d;
    for _i in 0..256 {
        y_prev = y;
        let numerator = y.checked_mul(y).ok_or(Overflow)?.checked_add(c).ok_or(Overflow)?;
        let denominator = y.checked_mul(to_u256!(2)).ok_or(Overflow)?
            .checked_add(b).ok_or(Overflow)?
            .checked_sub(d).ok_or(Overflow)?;
        y = numerator.checked_div(denominator).ok_or(Overflow)?;
        // if y > y_prev {
        //    if y - y_prev <= to_u256!(1) {
        //        break;
        //    }
        // }
        // else if y_prev - y <= to_u256!(1) {
        //    break;
        // }

    }

    Ok(y)
}

/// Calculating amount to be received from the pool given the amount to be sent to the pool and both reserves.
/// Formula : OUT_RESERVE * AMOUNT_IN / (IN_RESERVE + AMOUNT_IN)
///
/// - `in_reserve` - reserve amount of selling asset
/// - `out_reserve` - reserve amount of buying asset
/// - `amount_in` - amount
///
/// Returns MathError in case of error
pub fn calculate_out_given_in(
    in_reserve: Balance,
    out_reserve: Balance,
    amount_in: Balance,
) -> Result<Balance, MathError> {
    if amount_in == 0 {
        return Ok(0);
    };

    let (in_reserve_hp, out_reserve_hp, amount_in_hp) = to_u256!(in_reserve, out_reserve, amount_in);

    let y_stableswap = get_y_stableswap(0, 1, amount_in_hp + in_reserve_hp, [in_reserve_hp, out_reserve_hp], to_u256!(200_u128)).unwrap();

    let amount_out = out_reserve_hp.checked_sub(y_stableswap).ok_or(Overflow)?;
    //let amount_out = y_stableswap.checked_sub(out_reserve_hp).ok_or(Overflow)?;
    //assert_ne!(y_stableswap, amount_out);

    to_balance!(amount_out)
}

