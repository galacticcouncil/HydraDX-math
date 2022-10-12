use super::super::test_utils::assert_eq_approx;
use crate::lbp::lbp;
use primitive_types::U256;
use proptest::prelude::*;

const MIN_START_BLOCK: u32 = 0;
const MAX_END_BLOCK: u32 = 300;

fn start_blocks() -> impl Strategy<Value = u32> {
    MIN_START_BLOCK..100u32
}

fn end_blocks() -> impl Strategy<Value = u32> {
    200..MAX_END_BLOCK
}

fn initial_weight() -> impl Strategy<Value = u32> {
    1_000_000..10_000_000u32
}

fn final_weight() -> impl Strategy<Value = u32> {
    40_000_000..60_000_000u32
}

fn block_number() -> impl Strategy<Value = u32> {
    100..200u32
}

//Spec: https://www.notion.so/Property-Tests-7b506add39ea48fc8f68ecd18391e30a#9bbed73541c84e45a9855360aeee1f9b
proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]
    #[test]
    fn calculate_linear_weights(
        start_x_block in start_blocks(),
        end_x_block in end_blocks(),
        start_y_weight in initial_weight(),
        end_y_weight in final_weight(),
        at in block_number()
    ) {
        //Arrange
        let weight  = lbp::calculate_linear_weights(start_x_block,end_x_block,start_y_weight,end_y_weight,at).unwrap();

        let a1 = U256::from(at) - U256::from(start_x_block);
        let a2 = U256::from(end_y_weight) - U256::from(start_y_weight);

        let b1 = U256::from(weight) - U256::from(start_y_weight);
        let b2 = U256::from(end_x_block) - U256::from(start_x_block);

        //Act and Assert
        assert_eq_approx!(a1*a2, b1*b2, U256::from(MAX_END_BLOCK - MIN_START_BLOCK), "The invariant does not hold")
    }
}
