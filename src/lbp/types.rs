use crate::lbp::traits::BinomMath;
use primitive_types::U256;

pub type Balance = u128;
type Balance256 = U256;
pub type LBPWeight = u128;

lazy_static! {
    static ref BONEHP: Balance256 = Balance256::from(<Balance256 as BinomMath>::ONE);
    static ref ZEROHP: Balance256 = Balance256::from(0u128);
    static ref ONEHP: Balance256 = Balance256::from(1u128);
    static ref TWOHP: Balance256 = Balance256::from(2u128);
    static ref PRECISIONHP: Balance256 = Balance256::from(<Balance256 as BinomMath>::POW_PRECISION);
}

impl BinomMath for Balance256 {
    fn hdiv(&self, v: Self) -> Option<Self> {
        self.checked_mul(*BONEHP)?.checked_add(v)?.checked_div(v)
    }

    fn hmul(&self, v: Self) -> Option<Self> {
        self.checked_mul(v)?.checked_add(*BONEHP)?.checked_div(*BONEHP)
    }

    fn hsub(&self, v: Self) -> Option<Self> {
        self.checked_sub(v)
    }

    fn hadd(&self, v: Self) -> Option<Self> {
        self.checked_add(v)
    }

    fn htoi(&self) -> Self {
        self / *BONEHP
    }

    fn hfloor(&self) -> Self {
        self.htoi() * *BONEHP
    }

    fn hpowi(&self, n: Self) -> Self {
        let mut z = if n % *TWOHP != *ZEROHP { *self } else { *BONEHP };

        let mut cond = n / *TWOHP;

        let mut a = *self;

        // TODO: revisit these unwraps! this can actually panic in some cases?!
        // After hdx math is finalized!
        while cond > *ZEROHP {
            a = a.hmul(a).unwrap();

            if cond % 2 != *ZEROHP {
                z = z.hmul(a).unwrap();
            }

            cond /= *TWOHP;
        }

        z
    }

    fn hpow_approx(&self, exp: Self, precision: Self) -> Option<Self> {
        let a = exp;
        let (x, xneg) = self.hsub_sign(*BONEHP);
        let mut term = *BONEHP;
        let mut sum = term;
        let mut negative = false;

        let mut idx: Balance256 = *ONEHP;

        while term >= precision {
            let big_k: Balance256 = idx * *BONEHP;
            let (c, cneg) = a.hsub_sign(big_k.hsub(*BONEHP)?);

            term = term.hmul(c.hmul(x)?)?;
            term = term.hdiv(big_k)?;

            if term == *ZEROHP {
                break;
            }
            if xneg {
                negative = !negative;
            }
            if cneg {
                negative = !negative;
            }

            if negative {
                sum = sum.hsub(term)?;
            } else {
                sum = sum.hadd(term)?;
            }
            idx = match idx.checked_add(*ONEHP) {
                Some(v) => v,
                None => panic!("Hello friend, should never really happen!"),
            };
        }

        Some(sum)
    }

    fn hsub_sign(&self, b: Self) -> (Self, bool) {
        if *self >= b {
            (*self - b, false)
        } else {
            (b - *self, true)
        }
    }

    fn hpow(&self, v: Self) -> Option<Self> {
        let whole = v.hfloor();
        let remain = v.hsub(whole)?;

        let whole_pow = self.hpowi(whole.htoi());

        if remain == *ZEROHP {
            return Some(whole_pow);
        }

        let partial_result = self.hpow_approx(remain, *PRECISIONHP)?;

        whole_pow.hmul(partial_result)
    }

    fn hsub_one(&self) -> Option<Self> {
        self.checked_sub(*BONEHP)
    }

    fn hsubr_one(&self) -> Option<Self> {
        BONEHP.checked_sub(*self)
    }
}
