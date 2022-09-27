use crate::transcendental::{exp, pow};
use crate::types::FixedBalance;
use fixed::prelude::LossyInto;
use std::str::FromStr;

fn ensure_accuracy(result: FixedBalance, expected: FixedBalance, tolerance: FixedBalance) -> bool {
    let diff = if result > expected {
        result - expected
    } else {
        expected - result
    };

    // if (result > FixedBalance::from_num(15e-1)) || (result < FixedBalance::from_num(5e-1)) {
    //     return true;
    // };

    let r = diff / expected;
    r <= tolerance
}

#[test]
fn pow_should_be_accurate() {
    type S = FixedBalance;
    type D = FixedBalance;
    let tolerance = S::from_num(10e-8);

    // numbers very close to 1 taken to high powers will be our most frequent use case
    let result: D = pow::<S, D>(S::from_num(1.01), S::from_num(20.0)).unwrap();
    let expected = S::from_str("1.2201900399479668244827490915525641902001").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.01), S::from_num(40.0)).unwrap();
    let expected = S::from_str("1.4888637335882208749712646380173829620295125678828674453466259505").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.01), S::from_num(50.0)).unwrap();
    let expected = S::from_str("1.6446318218438818999219212023843297027618124642128479392075226899").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.99), S::from_num(20.0)).unwrap();
    let expected = S::from_str("0.8179069375972308708891986605443361898001").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.99), S::from_num(40.0)).unwrap();
    let expected = S::from_str("0.6689717585696805139383385988037122114654322769148393195898110632").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.99), S::from_num(60.0)).unwrap();
    let expected = S::from_str("0.5471566423907614761947413708400061745930842888943726259279732600").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.99), S::from_num(70.0)).unwrap();
    let expected = S::from_str("0.4948386596002072598628979069820787304054003895127352976965977151").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.005), S::from_num(10.0)).unwrap();
    let expected = S::from_str("1.051140132040790642597666015625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.005), S::from_num(50.0)).unwrap();
    let expected = S::from_str("1.2832258149353700670586533926923805486020509173525849626129737972").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.005), S::from_num(100.0)).unwrap();
    let expected = S::from_str("1.6466684921165446282600673335123931068636055297235559730494365670").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.995), S::from_num(10.0)).unwrap();
    let expected = S::from_str("0.951110130465771892558603515625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.995), S::from_num(50.0)).unwrap();
    let expected = S::from_str("0.7783125570686420679754776224422212745909394450869053879050670229").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.995), S::from_num(100.0)).unwrap();
    let expected = S::from_str("0.6057704364907282158922353367345217405582623216796229641872524576").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.001), S::from_num(10.0)).unwrap();
    let expected = S::from_str("1.010045120210252210120045010001").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.001), S::from_num(50.0)).unwrap();
    let expected = S::from_str("1.0512448324347511237943934536642517200194302789481737867480029931").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.001), S::from_num(100.0)).unwrap();
    let expected = S::from_str("1.1051156977207679683791052371188401894348988003480476139953393312").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.001), S::from_num(200.0)).unwrap();
    let expected = S::from_str("1.2212807053488598010206041529512175425342504642645791616601001048").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.001), S::from_num(500.0)).unwrap();
    let expected = S::from_str("1.6483094164130387741510320575015722415830725719070958553581810817").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.999), S::from_num(10.0)).unwrap();
    let expected = S::from_str("0.990044880209748209880044990001").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.999), S::from_num(50.0)).unwrap();
    let expected = S::from_str("0.9512056281970313499834513454769261811405852193538523652397906336").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.999), S::from_num(100.0)).unwrap();
    let expected = S::from_str("0.9047921471137090420322146062399503478004884163334699292762046385").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.999), S::from_num(200.0)).unwrap();
    let expected = S::from_str("0.8186488294786357055602111397290924927485430169330959883317503095").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.999), S::from_num(500.0)).unwrap();
    let expected = S::from_str("0.6063789448611850050363609973246236495685079090784912711325476959").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));



    let result: D = pow::<S, D>(S::from_num(0.5), S::from_num(0.01)).unwrap();
    let expected = S::from_str("0.9930924954370359015332102168880745712214323654004972804695688652").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.5), S::from_num(0.1)).unwrap();
    let expected = S::from_str("0.9330329915368074159813432661499421670272299643514940389004973854").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.5), S::from_num(0.5)).unwrap();
    let expected = S::from_str("0.7071067811865475244008443621048490392848359376884740365883398689").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.5), S::from_num(0.75)).unwrap();
    let expected = S::from_str("0.5946035575013605333587499852802379576464860462319087065095011123").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.5), S::from_num(1.0)).unwrap();
    let expected = S::from_str("0.5").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.5), S::from_num(1.5)).unwrap();
    let expected = S::from_str("0.3535533905932737622004221810524245196424179688442370182941699344").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(0.01)).unwrap();
    let expected = S::from_str("0.9971273133589335063736433138321697561416509622715937703756356260").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(0.1)).unwrap();
    let expected = S::from_str("0.9716416578630735005730455612486887640126529295738304341186096827").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(0.5)).unwrap();
    let expected = S::from_str("0.8660254037844386467637231707529361834714026269051903140279034897").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(0.75)).unwrap();
    let expected = S::from_str("0.8059274488676564396650036175294479328528122153879514906666908881").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(1.0)).unwrap();
    let expected = S::from_str("0.75").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(1.5)).unwrap();
    let expected = S::from_str("0.6495190528383289850727923780647021376035519701788927355209276172").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(2.0)).unwrap();
    let expected = S::from_str("0.5625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.75), S::from_num(2.5)).unwrap();
    let expected = S::from_str("0.4871392896287467388045942835485266032026639776341695516406957129").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(0.01)).unwrap();
    let expected = S::from_str("0.9983761306100158559947980311004829357566152460099328545491436682").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(0.1)).unwrap();
    let expected = S::from_str("0.9838794565405262890851617779221820042511646481521991509941114123").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(0.5)).unwrap();
    let expected = S::from_str("0.9219544457292887310002274281762793157246805048722464008007752205").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(0.75)).unwrap();
    let expected = S::from_str("0.8852464509219426525236080073563532529674134415306102174568717413").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(1.0)).unwrap();
    let expected = S::from_str("0.85").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(1.5)).unwrap();
    let expected = S::from_str("0.7836612788698954213501933139498374183659784291414094406806589374").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(2.0)).unwrap();
    let expected = S::from_str("0.7225").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(2.5)).unwrap();
    let expected = S::from_str("0.6661120870394111081476643168573618056110816647701980245785600968").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(3.0)).unwrap();
    let expected = S::from_str("0.614125").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(3.5)).unwrap();
    let expected = S::from_str("0.5661952739834994419255146693287575347694194150546683208917760823").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(4.0)).unwrap();
    let expected = S::from_str("0.52200625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.85), S::from_num(4.5)).unwrap();
    let expected = S::from_str("0.4812659828859745256366874689294439045540065027964680727580096699").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(0.01)).unwrap();
    let expected = S::from_str("0.9994871985837377078975799407374566822258364591826758293399876070").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(0.1)).unwrap();
    let expected = S::from_str("0.9948838031081762988652584981702691935499943586161215693506918918").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(0.5)).unwrap();
    let expected = S::from_str("0.9746794344808963906838413199899600299252583900337491031991750005").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(0.75)).unwrap();
    let expected = S::from_str("0.9622606002309621588456940537583053989668830809621746604353297274").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(1.0)).unwrap();
    let expected = S::from_str("0.95").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(1.5)).unwrap();
    let expected = S::from_str("0.9259454627568515711496492539904620284289954705320616480392162505").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(2.0)).unwrap();
    let expected = S::from_str("0.9025").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(2.5)).unwrap();
    let expected = S::from_str("0.8796481896190089925921667912909389270075456970054585656372554380").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(3.0)).unwrap();
    let expected = S::from_str("0.857375").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(3.5)).unwrap();
    let expected = S::from_str("0.8356657801380585429625584517263919806571684121551856373553926661").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(4.0)).unwrap();
    let expected = S::from_str("0.81450625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(4.5)).unwrap();
    let expected = S::from_str("0.7938824911311556158144305291400723816243099915474263554876230328").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(5.0)).unwrap();
    let expected = S::from_str("0.7737809375").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(5.5)).unwrap();
    let expected = S::from_str("0.7541883665745978350237090026830687625430944919700550377132418811").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(6.0)).unwrap();
    let expected = S::from_str("0.735091890625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(6.5)).unwrap();
    let expected = S::from_str("0.7164789482458679432725235525489153244159397673715522858275797871").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(7.0)).unwrap();
    let expected = S::from_str("0.69833729609375").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(7.5)).unwrap();
    let expected = S::from_str("0.6806550008335745461088973749214695581951427790029746715362007977").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(8.0)).unwrap();
    let expected = S::from_str("0.6634204312890625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(8.5)).unwrap();
    let expected = S::from_str("0.6466222507918958188034525061753960802853856400528259379593907578").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(9.0)).unwrap();
    let expected = S::from_str("0.630249409724609375").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(9.5)).unwrap();
    let expected = S::from_str("0.6142911382523010278632798808666262762711163580501846410614212199").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(10.0)).unwrap();
    let expected = S::from_str("0.59873693923837890625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(10.5)).unwrap();
    let expected = S::from_str("0.5835765813396859764701158868232949624575605401476754090083501589").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(11.0)).unwrap();
    let expected = S::from_str("0.5688000922764599609375").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(11.5)).unwrap();
    let expected = S::from_str("0.5543977522727016776466100924821302143346825131402916385579326510").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(12.0)).unwrap();
    let expected = S::from_str("0.540360087662636962890625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(12.5)).unwrap();
    let expected = S::from_str("0.5266778646590665937642795878580237036179483874832770566300360184").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(13.0)).unwrap();
    let expected = S::from_str("0.51334208327950511474609375").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(13.5)).unwrap();
    let expected = S::from_str("0.5003439714261132640760656084651225184370509681091132037985342175").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(0.95), S::from_num(14.0)).unwrap();
    let expected = S::from_str("0.4876749791155298590087890625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(0.01)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(0.1)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(0.5)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(0.75)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(1.0)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(1.5)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(5.5)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(50.0)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1), S::from_num(99.5)).unwrap();
    let expected = S::from_str("1").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(0.01)).unwrap();
    let expected = S::from_str("1.0022339270182330724959999259594153373003507281840127222791262512").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(0.1)).unwrap();
    let expected = S::from_str("1.0225651825635729274886316472598280722066861418237486636223965919").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(0.5)).unwrap();
    let expected = S::from_str("1.1180339887498948482045868343656381177203091798057628621354486227").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(0.75)).unwrap();
    let expected = S::from_str("1.1821770112539697666271201498590187757127460032646753267648841778").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(1.0)).unwrap();
    let expected = S::from_str("1.25").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(1.5)).unwrap();
    let expected = S::from_str("1.3975424859373685602557335429570476471503864747572035776693107783").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.25), S::from_num(2.0)).unwrap();
    let expected = S::from_str("1.5625").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.5), S::from_num(0.01)).unwrap();
    let expected = S::from_str("1.0040628822999231097921678262939853106034341255439779432223661978").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.5), S::from_num(0.1)).unwrap();
    let expected = S::from_str("1.0413797439924105868461910102311153381211443341764803061983768766").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.5), S::from_num(0.5)).unwrap();
    let expected = S::from_str("1.2247448713915890490986420373529456959829737403283350642163462836").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.5), S::from_num(0.75)).unwrap();
    let expected = S::from_str("1.3554030054147672479433270793371662853330255609047152735564844293").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

    let result: D = pow::<S, D>(S::from_num(1.5), S::from_num(1.0)).unwrap();
    let expected = S::from_str("1.5").unwrap();
    assert!(ensure_accuracy(result, expected, tolerance));

}