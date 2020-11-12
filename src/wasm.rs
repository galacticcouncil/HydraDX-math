#[macro_export]
macro_rules! wasm_api {
    () => {
        use wasm_bindgen::prelude::*;

        fn convert_to_u128(s: &str) -> u128 {
            match s.parse::<u128>() {
                Ok(v) => v,
                Err(_) => 0,
            }
        }

        #[wasm_bindgen]
        pub fn get_spot_price(s: String, b: String, a: String) -> String {
            let sell_reserve = convert_to_u128(&s);
            let buy_reserve = convert_to_u128(&b);
            let amount = convert_to_u128(&a);

            let result = calculate_spot_price(sell_reserve, buy_reserve, amount);

            match result {
                Some(val) => val.to_string().chars().collect::<String>(),
                None => "0".chars().collect::<String>(),
            }
        }
    };
}
