#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

#[allow(unused)]

use crate::bls24param::BLS24Param;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Integer, Limb, NonZero, Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeLess};
use rand::Rng;
use sha3::{Shake128, Shake256};
use sha3::digest::ExtendableOutput;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>r</i></sub> &simeq; <b>&Zopf;</b>/<i>r</i><b>&Zopf;</b> finite field.
pub struct BLS24Zr<PAR: BLS24Param, const LIMBS: usize>(
    #[doc(hidden)]
    pub Uint<LIMBS>,
    #[doc(hidden)]
    pub PhantomData<PAR>,
);

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Zr<PAR, LIMBS> {
    /// Montgomery reduction of <i>t</i> = (<i>t_lo</i>, <i>t_hi</i>) in range 0..&lt;<i>r&times;2&#x02B7;</i>,
    /// where <i>r &lt; 2&#x02B7;</i> is the BLS24 group order and <i>w</i> &#x2254; <i>64&times;LIMBS</i>.
    ///
    /// Return <i>t&times;2&#8315;&#x02B7;</i> in range 0..&lt;<i>r</i>.
    #[inline]
    fn redc(t_lo: Uint<LIMBS>, t_hi: Uint<LIMBS>) -> Uint<LIMBS> {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());  // r < 2^w
        let q: Uint<LIMBS> = Uint::from_words(PAR::NEG_INV_ORD.try_into().unwrap());  // q := -1/r mod 2^w
        // m ← ((t mod s)*q) mod s = (t_lo*q) mod s:
        let (m, _) = t_lo.widening_mul(&q);
        // t ← (t + m*r) / s:
        let (mp_lo, mp_hi) = m.widening_mul(&r);
        let (_, carry) = t_lo.carrying_add(&mp_lo, Limb::ZERO);
        let (t, _) = t_hi.carrying_add(&mp_hi, carry);
        // return if t < r { t } else { t - r }
        t - Uint::conditional_select(&r, &Uint::ZERO, t.ct_lt(&r))
    }

    /// Convert an unsigned integer (Uint) value <i>w</i> to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>r</i> =
    /// redc((<i>w</i> mod <i>r</i>)&middot;(<i>s&sup2;</i> mod <i>r</i>)),
    /// where <i>s > r</i> is a power of 2.
    #[inline]
    pub fn from_uint(w: Uint<LIMBS>) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_R.try_into().unwrap());
        let (lo, hi) = w.widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert a word-sized integer <i>w</i> to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>r</i> =
    /// redc((<i>w</i> mod <i>r</i>)&middot;(<i>s&sup2;</i> mod <i>r</i>)),
    /// where <i>s > r</i> is a power of 2.
    #[inline]
    pub fn from_word(w: Word) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_R.try_into().unwrap());
        let (lo, hi) = Uint::from_word(w).widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert an integer <i>w</i> represented by s sequence of words to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>r</i> =
    /// redc((<i>w</i> mod <i>r</i>)&middot;(<i>s&sup2;</i> mod <i>r</i>)),
    /// where <i>s > r</i> is a power of 2.
    #[inline]
    pub fn from_words(v: [Word; LIMBS]) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_R.try_into().unwrap());
        let (lo, hi) = Uint::from_words(v).widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a scalar field &Zopf;<i>&#x2099;</i> element with SHAKE-128.
    ///
    /// Twice as much hash output is converted to the field element via Montgomery reduction.
    /// This ensures the deviation from uniform sampling over &Zopf;<i>&#x2099;</i>
    /// is upper-bounded by <i>n&#8315;&sup1;</i>, well below the target
    /// adversary advantage <i>O</i>(<i>n<sup>-&frac12;</sup></i>).
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let rbytelen: usize = ((r.bits() + 7) >> 3) as usize;
        let mut out = vec![0u8; 2*LIMBS*8];  // twice the space taken by a base field element
        Shake128::digest_xof(data, &mut out);
        for j in 2*rbytelen..2*LIMBS*8 {
            out[j] = 0;  // make sure the lift to &Zopf; does not exceed the squared BLS24 order r^2
        }
        let lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let hi = Uint::from_le_slice(&out[LIMBS*8..]);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a scalar field &Zopf;<i>&#x2099;</i> element with SHAKE-256.
    ///
    /// Twice as much hash output is converted to the field element via Montgomery reduction.
    /// This ensures the deviation from uniform sampling over &Zopf;<i>&#x2099;</i>
    /// is upper-bounded by <i>n&#8315;&sup1;</i>, well below the target
    /// adversary advantage <i>O</i>(<i>n<sup>-&frac12;</sup></i>).
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let rbytelen: usize = ((r.bits() + 7) >> 3) as usize;
        let mut out = vec![0u8; 2*LIMBS*8];  // twice the space taken by a base field element
        Shake256::digest_xof(data, &mut out);
        for j in 2*rbytelen..2*LIMBS*8 {
            out[j] = 0;  // make sure the lift to &Zopf; does not exceed the squared BLS24 order r^2
        }
        let lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let hi = Uint::from_le_slice(&out[LIMBS*8..]);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert an integer in Montgomery form to plain representation.
    ///
    /// NB: the plain representation of <i>m</i> = <i>w&middot;r</i> mod <i>n</i> is
    /// <i>w</i> = redc(<i>m</i>), where <i>r > n</i> is a power of 2.
    #[inline]
    pub fn to_uint(&self) -> Uint<LIMBS> {
        Self::redc(self.0, Uint::ZERO)
    }

    /// Determine if the plain representation of this element is odd.
    #[inline]
    pub fn is_odd(&self) -> Choice {
        Self::redc(self.0, Uint::ZERO).is_odd()
    }

    /// Compute <i>v</i> = `self`<i>&#x02E3;</i> mod <i>n</i>.
    #[inline]
    fn pow(&self, x: Uint<LIMBS>) -> Self {
        // this method is private, and the exponent (restricted to inversion and square roots)
        // is fixed, public, and rather sparse, hence the square-and-multiply method suffices
        // (isochronous for either of these exponents, and more efficient than a fixed-window approach):
        let mut v = Self::one();
        let w = x.as_words();  // presumed NOT to be in Montgomery form
        for i in (0..LIMBS << 6).rev() {
            v = v.sq();
            if ((w[i >> 6] >> (i & 63)) & 1) == 1 {
                v *= *self;
            }
        }
        v
    }

}

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Zr<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        Self::Output {
            0: self.0.add_mod(&rhs.0, &nzr),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        self.0 = self.0.add_mod(&rhs.0, &nzr);
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Field for BLS24Zr<PAR, LIMBS> {
    /// Convert `self` to byte array representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let binding = self.to_uint();
        let val = binding.as_words();
        assert_eq!(val.len(), LIMBS);
        let mut bytes = Vec::<u8>::with_capacity(LIMBS << 3);
        for j in 0..LIMBS {
            let u = val[j];
            bytes.push(u as u8);
            bytes.push((u >> 8) as u8);
            bytes.push((u >> 16) as u8);
            bytes.push((u >> 24) as u8);
            bytes.push((u >> 32) as u8);
            bytes.push((u >> 40) as u8);
            bytes.push((u >> 48) as u8);
            bytes.push((u >> 56) as u8);
        }
        bytes
    }

    /// Compute the value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        Self {
            0: self.0.add_mod(&self.0, &nzr),
            1: Default::default(),
        }
    }

    /// Compute <i>`self`/2</i> mod <i>n</i>.
    ///
    /// Technique: if the lift of <i>`self`</i> (either in plain or in Montgomery form)
    /// to &Zopf; is even, a right-shift does the required division;
    /// if it is odd, then <i>`self` + n</i> is even,
    /// and <i>0</i> &leq; (<i>`self` + n</i>) >> <i>1</i> < <i>n</i> is the desired value.
    #[inline]
    fn half(&self) -> Self {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        Self {
            0: Uint::conditional_select(&self.0, &self.0.add(r), self.0.is_odd()) >> 1,
            1: Default::default(),
        }
    }

    /// Compute the square of `self`.
    #[inline]
    fn sq(&self) -> Self {
        let (lo, hi) = self.0.square_wide();
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Compute the cube of `self`.
    #[inline]
    fn cb(&self) -> Self {
        let (lo, hi) = self.0.square_wide();
        let (lo, hi) = self.0.widening_mul(&Self::redc(lo, hi));
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Compute <i>r</i> = <i>u&#8315;&sup1;</i> = <i>u&#x1D56;&#8315;&sup2;</i> mod <i>n</i>
    /// for <i>u</i> &#x2254; `self`, which satisfies
    /// <i>r&times;u</i> mod <i>n</i> = <i>1</i> if <i>u &ne; 0</i>.
    ///
    /// NB: crypto_bigint::Uint seems to offer an inversion functionality, but frankly,
    /// the usage instructions are poorly documented at best, entirely missing at worst.
    #[inline]
    fn inv(&self) -> Self {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        self.pow(r - Uint::from_word(2)) // inv exponent: n - 2
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Zr<PAR, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            0: self.0.clone(),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            0: Uint::conditional_select(&a.0, &b.0, choice),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }

    #[inline]
    fn ct_ne(&self, other: &Self) -> Choice {
        self.0.ct_ne(&other.0)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Zr<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Zr<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Zr<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        /*
        // signed format:
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        let half_n = r.shr(1);
        let val = Self::redc(self.0, Uint::ZERO);
        let str = if val <= half_n {
            val.to_string_radix_vartime(10)
        } else {
            "-".to_string() + val.neg_mod(&nzr).to_string_radix_vartime(10).as_str()
        };
        write!(f, "{}", str)
        // */
        write!(f, "{}", Self::redc(self.0, Uint::ZERO).to_string_radix_vartime(10))
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul for BLS24Zr<PAR, LIMBS> {
    type Output = Self;

    /// Compute a product in &Zopf;<i>&#x2099;</i>.
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let (lo, hi) = self.0.widening_mul(&rhs.0);
        Self::Output {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Zr<PAR, LIMBS>> for Word {
    type Output = BLS24Zr<PAR, LIMBS>;

    /// Compute the product of a small integer left factor
    /// by a right factor from &Zopf;<i>&#x2099;</i>.
    #[inline]
    fn mul(self, rhs: BLS24Zr<PAR, LIMBS>) -> Self::Output {
        assert!(self < 1 << 4);  // only meant for very small factors
        let mut val = Self::Output::zero();
        let mut fac = self as u8;
        let mut add = rhs;
        for _ in 0..4 {
            val = BLS24Zr::conditional_select(&val, &(val + add), Choice::from(fac & 1));
            fac >>= 1;
            add += add;
        }
        //assert_eq!(val, BLS24Zr::from_word(self)*rhs);
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Zr<PAR, LIMBS>> for i64 {
    type Output = BLS24Zr<PAR, LIMBS>;

    /// Compute the product of a single-precision, signed integer left factor
    /// by a right factor from &Zopf;<i>&#x2099;</i>.
    ///
    /// This is a naïve implementation that treats the word-sized factor as a full-sized value.
    /// It would greatly benefit from dedicated i64&times;Int and/or i64&times;Uint functions.
    #[inline]
    fn mul(self, rhs: BLS24Zr<PAR, LIMBS>) -> Self::Output {
        let u = BLS24Zr::from_word(self.unsigned_abs())*rhs;
        Self::Output::conditional_select(&u, &(-u), Choice::from((self < 0) as u8))
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Zr<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Zr<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from &Zopf;<i>&#x2099;</i>.
    #[inline]
    fn mul(self, rhs: BLS24Zr<PAR, LIMBS>) -> Self::Output {
        BLS24Zr::from_uint(self)*rhs
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        let (lo, hi) = self.0.widening_mul(&rhs.0);
        self.0 = Self::redc(lo, hi);
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Zr<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        Self::Output {
            0: self.0.neg_mod(&nzr),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> One for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn one() -> Self {
        let r2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_R.try_into().unwrap());
        Self {
            0: Self::redc(r2, Uint::ZERO),  // (1*r) mod n
            1: Default::default(),
        }
    }

    fn is_one(&self) -> Choice {
        Self::redc(self.0, Uint::ZERO).ct_eq(&Uint::ONE)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq for BLS24Zr<PAR, LIMBS> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }

    fn ne(&self, other: &Self) -> bool {
        self.0.ct_ne(&other.0).into()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Zr<PAR, LIMBS> {
    /// Pick a uniform element from &Zopf;<i>&#x2099;</i> by rejection sampling mod <i>n</i>.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let rbits = r.bits();
        let top: usize = (((rbits + 63) >> 6) - 1) as usize;
        let mask = (1 << (rbits & 63)) - 1;
        let mut w: [Word; LIMBS] = [0; LIMBS];
        loop {
            // uniformly sample the bit capacity of the modulus:
            rng.fill(&mut w);
            w[top] &= mask;
            for j in top + 1..LIMBS {
                w[j] = 0;
            }
            // rejection sampling for the most significant word:
            while w[top].cmp(&PAR::ORDER[top]).is_gt() {  // this means the whole value exceeds the modulus
                w[top] = rng.next_u64() & mask;
            }
            // rejection sampling for the whole value:
            let v = Uint::from_words(w);
            if v.cmp(&r).is_lt() {
                return Self::from_uint(v);
            }
        }
    }

    /// Try to pick a uniform element from &Zopf;<i>&#x2099;</i> by rejection sampling mod <i>n</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let top = PAR::ORDER.len() - 1;
        let mask = (1 << 62) - 1; // modulus bitlength is always 64*LIMBS - 2
        let mut w: [Word; LIMBS] = [0; LIMBS];
        loop {
            // uniformly sample the bit capacity of the modulus:
            for wi in &mut w {
                *wi = rng.try_next_u64()?
            }
            w[top] &= mask;
            // rejection sampling for the most significant word:
            while w[top].cmp(&PAR::ORDER[top]).is_gt() {  // this means the whole value exceeds the modulus
                w[top] = rng.try_next_u64()? & mask;
            }
            // rejection sampling for the whole value:
            let v = Uint::from_words(w);
            if v.cmp(&r).is_lt() {
                return Ok(Self::from_uint(v));
            }
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Zr<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        Self::Output {
            0: self.0.sub_mod(&rhs.0, &nzr),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();
        self.0 = self.0.sub_mod(&rhs.0, &nzr);
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Zr<PAR, LIMBS> {
    #[inline]
    fn zero() -> Self {
        Self {
            0: Uint::ZERO,  // (0*r) mod n
            1: Default::default(),
        }
    }

    #[inline]
    fn is_zero(&self) -> Choice {
        self.0.is_zero()
    }

    fn set_zero(&mut self) {
        self.0.set_zero()
    }
}


#[cfg(test)]
mod tests {
    use crate::bls24param::{
        BLS24317Param, BLS24324Param, BLS24329Param, BLS24339Param, BLS24341Param,
        BLS24342Param, BLS24343Param, BLS24347Param, BLS24348Param, BLS24349Param,
        BLS24358Param, BLS24362Param, BLS24365Param, BLS24379Param, BLS24380Param,
        BLS24407Param, BLS24409Param, BLS24429Param, BLS24449Param, BLS24454Param,
        BLS24459Param, BLS24469Param, BLS24470Param, BLS24471Param, BLS24472Param,
        BLS24477Param, BLS24481Param, BLS24485Param, BLS24489Param, BLS24507Param,
        BLS24519Param, BLS24520Param, BLS24529Param, BLS24539Param, BLS24549Param,
        BLS24559Param, BLS24569Param, BLS24571Param, BLS24587Param, BLS24589Param,
        BLS24600Param, BLS24605Param, BLS24609Param, BLS24617Param, BLS24619Param,
        BLS24623Param, BLS24627Param, BLS24629Param, BLS24631Param, BLS24639Param,
    };
    use crypto_bigint::NonZero;
    use crypto_bigint::rand_core::RngCore;
    use rand::Rng;
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BLS24Zr test template.
    #[allow(non_snake_case)]
    fn BLS24Zr_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let nzr = NonZero::new(r).unwrap();

        println!();
        println!("Performing {} BLS24-{:03}Zr test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BLS24Zr::zero());
        assert!(bool::from(BLS24Zr::<PAR, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BLS24Zr::one());
        assert!(bool::from(BLS24Zr::<PAR, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // Montgomery form:
            let v1: Word = rng.next_u64() & 0xF;
            //println!("v1 = {}", v1);
            let m1: BLS24Zr<PAR, LIMBS> = BLS24Zr::from_word(v1);
            //println!("m1 ? {}", m1);
            assert_eq!(Uint::from_word(v1), m1.to_uint());

            let e1: BLS24Zr<PAR, LIMBS> = BLS24Zr::random(&mut rng);
            //println!("e1     = {}", e1);
            //println!("e1 + 0 = {}", e1 + BLS24Zr::ZERO);
            assert_eq!(e1 + BLS24Zr::zero(), e1);
            //println!("e1*1   = {}", e1*BLS24Zr::ONE);
            assert_eq!(e1*BLS24Zr::one(), e1);

            // addition vs subtraction:
            //println!("-e1      = {}", -e1);
            //println!("e1 - e1  = {}", e1 - e1);
            //println!("e1+(-e1) = {}", e1 + (-e1));
            assert!(bool::from((e1 - e1).is_zero()));
            assert!(bool::from((e1 + (-e1)).is_zero()));

            // double and half:
            //println!("2*e1   = {}", e1.double());
            //println!("e1/2   = {}", e1.half());
            assert_eq!(e1.double().half(), e1);
            assert_eq!(e1.half().double(), e1);
            assert_eq!(e1.double()*e1.half(), e1.sq());

            // square and cube:
            //println!("e1^2   = {}", e1.sq());
            //println!("e1^2 = e1*e1 ? {}", e1.sq() == e1*e1);
            assert_eq!(e1.sq(), e1*e1);
            //println!("e1^3   = {}", e1.cb());
            //println!("e1^3 = e1*e1*e1 ? {}", e1.cb() == e1*e1*e1);
            assert_eq!(e1.cb(), e1*e1*e1);

            // field inversion:
            //println!("e1^-1  = {}", e1.inv());
            //println!("e1*e1^-1 = {}", e1*e1.inv());
            assert!(bool::from((e1*e1.inv()).is_one() | e1.is_zero()));

            // hybrid multiplication (Word*BLS24Zr and Uint*BLS24Zr):
            let k1: Word = rng.next_u64() & 0xF;
            //println!("k1*e1 = {}", k1*e1);
            //println!("k1*e1 ? {}", BLS24Zr::from_word(k1)*e1);
            assert_eq!(k1*e1, BLS24Zr::from_word(k1)*e1);
            let mut w1: [Word; LIMBS] = [0; LIMBS];
            rng.fill(&mut w1);
            let u1 = Uint::from_words(w1).rem(&nzr);
            //println!("u1 = {}", u1.to_string_radix_vartime(10));
            //println!("u1*e1 = {}", u1*e1);
            //println!("u1*e1 ? {}", BLS24Zr::from_words(w1)*e1);
            assert_eq!(u1*e1, BLS24Zr::from_words(w1)*e1);

            let f1 = BLS24Zr::random(&mut rng);
            //println!("f1     = {}", f1);
            let g1 = BLS24Zr::random(&mut rng);
            //println!("g1     = {}", g1);

            // commutativity of addition and multiplication:
            //println!("e1 + f1 = {}", e1 + f1);
            //println!("f1 + e1 = {}", f1 + e1);
            assert_eq!(e1 + f1, f1 + e1);
            assert_eq!(e1*f1, f1*e1);

            // associativity:
            //println!("(e1 + f1) + g1 = {}", (e1 + f1) + g1);
            //println!("e1 + (f1 + g1) = {}", e1 + (f1 + g1));
            assert_eq!((e1 + f1) + g1, e1 + (f1 + g1));
            //println!("(e1*f1)*g1 = {}", (e1*f1)*g1);
            //println!("e1*(f1*g1) = {}", e1*(f1*g1));
            assert_eq!((e1*f1)*g1, e1*(f1*g1));
        }
        match now.elapsed() {
            Ok(elapsed) => {
                println!("Elapsed time: {} ms.", (elapsed.as_micros() as f64)/1000.0);
            }
            Err(e) => {
                println!("Error: {e:?}");
            }
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24317Zr_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Zr_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Zr_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Zr_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Zr_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Zr_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Zr_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Zr_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Zr_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Zr_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Zr_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Zr_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Zr_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Zr_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Zr_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Zr_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Zr_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Zr_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Zr_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Zr_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Zr_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Zr_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Zr_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Zr_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Zr_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Zr_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Zr_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Zr_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Zr_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Zr_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Zr_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Zr_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Zr_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Zr_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Zr_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Zr_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Zr_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Zr_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Zr_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Zr_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Zr_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Zr_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Zr_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Zr_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Zr_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Zr_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Zr_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Zr_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Zr_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Zr_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Zr_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Zr_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Zr_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Zr_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Zr_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Zr_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Zr_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Zr_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Zr_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Zr_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Zr_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Zr_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Zr_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Zr_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Zr_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Zr_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Zr_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Zr_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Zr_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Zr_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Zr_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Zr_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Zr_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Zr_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Zr_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Zr_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Zr_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Zr_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Zr_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Zr_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Zr_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Zr_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Zr_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Zr_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Zr_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Zr_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Zr_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Zr_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Zr_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Zr_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Zr_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Zr_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Zr_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Zr_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Zr_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Zr_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Zr_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Zr_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Zr_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Zr_test::<BLS24639Param, LIMBS>();
    }

}
