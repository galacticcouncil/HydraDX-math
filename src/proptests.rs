use proptest::test_runner::{TestRunner};
use proptest::strategy::{Strategy, ValueTree};
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_fixed_a(_ in 0..1_000_000_000) {
        let minimal_failing_case = find_minimal_failing_case();

        if minimal_failing_case.is_some() {
            let val = minimal_failing_case.unwrap();

            assert_eq!(val.0, 1);
            assert!(val.1 >= 33499370958229846944519890329592825);
            assert!(val.2 >= 33499370958229846944519890329592825);
        }
    }
}


/// Trying to find minimal failing cases for #calculate_spot_price
#[allow(unused)]
fn find_minimal_failing_case() -> Option<(u128, u128, u128)> {
    let mut runner = TestRunner::default();
    let mut sell_reserve;
    let mut buy_reserve;
    let mut amount;
    let mut result;
    let mut variables;

    for _ in 0..512 {
        sell_reserve = (1u128..2u128).new_tree(&mut runner).unwrap();
        buy_reserve = (0u128..u128::MAX).new_tree(&mut runner).unwrap();
        amount = (0u128..u128::MAX).new_tree(&mut runner).unwrap();
        variables = vec![sell_reserve, buy_reserve, amount];
        result = crate::amm::calculate_spot_price(sell_reserve.current(), buy_reserve.current(), amount.current());

        if result.is_some() {
            continue;
        }

        for i in 1..3 {
            result = crate::amm::calculate_spot_price(sell_reserve.current(), buy_reserve.current(), amount.current());
            if result.is_none() {
                if !variables[i].simplify() {
                    // No more simplifications possible; we're done
                    break;
                }
            } else {
                // Passed this input, back up a bit
                if !variables[i].complicate() {
                    break;
                }
            }
        }

        //println!("A minimal failing case is {0} {1} {2}", sell_reserve.current(), buy_reserve.current(), amount.current());
        return Some((sell_reserve.current(), buy_reserve.current(), amount.current()));
    }
    return None;
}
