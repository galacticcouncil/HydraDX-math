use crate::lbp::{calculate_in_given_out, calculate_out_given_in};
use crate::transcendental::exp;

const ONE: u128 = 1_000_000_000_000;

#[test]
fn calculate_out_given_in_should_be_accurate() {
    let reserves = (2000 * ONE, 1000 * ONE);
    let weights: (u32, u32) = (80_000_000, 20_000_000);
    let amount: u128 = 10 * ONE;

    //WOLF: -19.752478743433
    let expected: u128 = 19752478743433;
    let result = calculate_out_given_in(reserves.0, reserves.1, weights.0, weights.1, amount).unwrap();
    dbg!(result);
    dbg!(expected);

    let diff = expected.abs_diff(result);
    dbg!(diff);

    let reserves = (22222 * ONE, 6580 * ONE);
    let weights: (u32, u32) = (89_000_000, 11_000_000);
    let amount: u128 = 10123456789000;

    //WOLF: -24.20304712539086130323020840801004914773552015473671024341062946
    let expected: u128 = 24203047125390;
    let result = calculate_out_given_in(reserves.0, reserves.1, weights.0, weights.1, amount).unwrap();
    dbg!(result);
    dbg!(expected);

    let diff = expected.abs_diff(result);
    dbg!(diff);

    let reserves = (100000123456789000, 23452123456789000);
    let weights: (u32, u32) = (22_000_000, 88_000_000);
    let amount: u128 = 1000123456789000;

    //WOLF: -58.27367270221404040681493033499245384306252707454585436652
    let expected: u128 = 58273672702214;
    let result = calculate_out_given_in(reserves.0, reserves.1, weights.0, weights.1, amount).unwrap();
    dbg!(result);
    dbg!(expected);

    let diff = expected.abs_diff(result);
    dbg!(diff);
}

#[test]
fn calculate_in_given_out_should_be_accurate() {
    let reserves = (2000 * ONE, 1000 * ONE);
    let weights: (u32, u32) = (80_000_000, 20_000_000);
    let amount: u128 = 10 * ONE;

    //WOLF: 5.0314862956263066559392955788394917420334534555688279295552374892...
    let expected: u128 = 5031486295626;
    let result = calculate_in_given_out(reserves.0, reserves.1, weights.0, weights.1, amount).unwrap();
    dbg!(result);
    dbg!(expected);

    let diff = expected.abs_diff(result);
    dbg!(diff);

    let reserves = (22222 * ONE, 6580 * ONE);
    let weights: (u32, u32) = (89_000_000, 11_000_000);
    let amount: u128 = 10123456789000;

    //WOLF: 4.2292600020724036876612495828158328751959379748235212049843994330...
    let expected: u128 = 4229260002072;
    let result = calculate_in_given_out(reserves.0, reserves.1, weights.0, weights.1, amount).unwrap();
    dbg!(result);
    dbg!(expected);

    let diff = expected.abs_diff(result);
    dbg!(diff);

    let reserves = (100000123456789000, 23452123456789000);
    let weights: (u32, u32) = (22_000_000, 88_000_000);
    let amount: u128 = 1000123456789000;

    //WOLF: 19044.309012814924635150222870783961013971431425634600298042081407
    let expected: u128 = 19044309012814924;
    let result = calculate_in_given_out(reserves.0, reserves.1, weights.0, weights.1, amount).unwrap();
    dbg!(result);
    dbg!(expected);

    let diff = expected.abs_diff(result);
    dbg!(diff);
}
