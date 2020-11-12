import * as wasm from "hack-hydra-dx-math";

let f = function(){

    let a = document.querySelector('#a');
    let b = document.querySelector('#b');
    let s = document.querySelector('#s');
    let o = document.querySelector('#o');

    let r = wasm.get_spot_price(s.value.toString(),b.value.toString(),a.value.toString());

    o.value = r;
}

let button = document.querySelector('#btn');

button.addEventListener("click", f);
