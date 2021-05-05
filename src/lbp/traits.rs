pub trait BinomMath: Sized {
    const ONE: u128 = 1_000_000_000_000_u128;
    const POW_PRECISION: u128 = 100_000_000_u128;

    fn hdiv(&self, v: Self) -> Option<Self>;
    fn hmul(&self, v: Self) -> Option<Self>;
    fn hsub(&self, v: Self) -> Option<Self>;
    fn hadd(&self, v: Self) -> Option<Self>;
    fn htoi(&self) -> Self;
    fn hfloor(&self) -> Self;
    fn hpowi(&self, n: Self) -> Self;
    fn hpow_approx(&self, exp: Self, precision: Self) -> Option<Self>;
    fn hsub_sign(&self, b: Self) -> (Self, bool);
    fn hpow(&self, v: Self) -> Option<Self>;

    fn hsub_one(&self) -> Option<Self>;
    fn hsubr_one(&self) -> Option<Self>;
}
