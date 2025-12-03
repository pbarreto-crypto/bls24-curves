#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24param::BLS24Param;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Integer, Limb, NonZero, Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeLess};
use sha3::{Shake128, Shake256};
use sha3::digest::ExtendableOutput;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p</i></sub> &simeq; <b>&Zopf;</b>/<i>p</i><b>&Zopf;</b> finite field.
pub struct BLS24Fp<PAR: BLS24Param, const LIMBS: usize>(
    #[doc(hidden)]
    pub Uint<LIMBS>,
    #[doc(hidden)]
    pub PhantomData<PAR>,
);

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Fp<PAR, LIMBS> {
    /// Montgomery reduction of <i>t</i> = (<i>t_lo</i>, <i>t_hi</i>) in range 0..&lt;<i>p&times;2&#x02B7;</i>,
    /// where <i>p &lt; 2&#x02B7;</i> is the BLS24 modulus and <i>w</i> &#x2254; <i>64&times;LIMBS</i>.
    ///
    /// Return <i>t&times;2&#8315;&#x02B7;</i> in range 0..&lt;<i>p</i>.
    #[inline]
    fn redc(t_lo: Uint<LIMBS>, t_hi: Uint<LIMBS>) -> Uint<LIMBS> {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());  // p < 2^w
        let q: Uint<LIMBS> = Uint::from_words(PAR::NEG_INV_MOD.try_into().unwrap());  // q := -1/p mod 2^w
        // m ← ((t mod s)*q) mod s = (t_lo*q) mod s:
        let (m, _) = t_lo.widening_mul(&q);
        // t ← (t + m*p) / s:
        let (mp_lo, mp_hi) = m.widening_mul(&p);
        let (_, carry) = t_lo.carrying_add(&mp_lo, Limb::ZERO);
        let (t, _) = t_hi.carrying_add(&mp_hi, carry);
        // return if t < p { t } else { t - p }
        t - Uint::conditional_select(&p, &Uint::ZERO, t.ct_lt(&p))
    }

    /// Convert an unsigned integer (Uint) value <i>w</i> to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>p</i> =
    /// redc((<i>w</i> mod <i>p</i>)&middot;(<i>s&sup2;</i> mod <i>p</i>)),
    /// where <i>s > p</i> is a power of 2.
    #[inline]
    pub fn from_uint(w: Uint<LIMBS>) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_P.try_into().unwrap());
        let (lo, hi) = w.widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert a word-sized integer <i>w</i> to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>p</i> =
    /// redc((<i>w</i> mod <i>p</i>)&middot;(<i>s&sup2;</i> mod <i>p</i>)),
    /// where <i>s > p</i> is a power of 2.
    #[inline]
    pub fn from_word(w: Word) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_P.try_into().unwrap());
        let (lo, hi) = Uint::from_word(w).widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert an integer <i>w</i> represented by a sequence of words to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>p</i> =
    /// redc((<i>w</i> mod <i>p</i>)&middot;(<i>s&sup2;</i> mod <i>p</i>)),
    /// where <i>s > p</i> is a power of 2.
    #[inline]
    pub(crate) fn from_words(v: [Word; LIMBS]) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_P.try_into().unwrap());
        let (lo, hi) = Uint::from_words(v).widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a field element with SHAKE-128.
    ///
    /// Twice as much hash output is converted to the field element via Montgomery reduction.
    /// This ensures the deviation from uniform sampling over <b>F</b><sub><i>p</i></sub>
    /// is upper-bounded by <i>p&#8315;&sup1;</i>, well below the target
    /// adversary advantage <i>O</i>(<i>p<sup>-&frac12;</sup></i>).
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        let mut out = vec![0u8; 2*LIMBS*8];  // twice the space taken by a base field element
        Shake128::digest_xof(data, &mut out);
        out[2*LIMBS*8 - 1] = 0;  // make sure the lift to Z does not exceed the squared BLS24 modulus p^2
        let lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let hi = Uint::from_le_slice(&out[LIMBS*8..]);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a field element with SHAKE-256.
    ///
    /// Twice as much hash output is converted to the field element via Montgomery reduction.
    /// This ensures the deviation from uniform sampling over <b>F</b><sub><i>p</i></sub>
    /// is upper-bounded by <i>p&#8315;&sup1;</i>, well below the target
    /// adversary advantage <i>O</i>(<i>p<sup>-&frac12;</sup></i>).
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        let mut out = vec![0u8; 2*LIMBS*8];  // twice the space taken by a base field element
        Shake256::digest_xof(data, &mut out);
        out[2*LIMBS*8 - 1] = 0;  // make sure the lift to Z does not exceed the squared BLS24 modulus p^2
        let lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let hi = Uint::from_le_slice(&out[LIMBS*8..]);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a list of base field elements with SHAKE-128.
    #[inline]
    pub(crate) fn shake128list(data: &[u8], k: usize) -> Vec<Self> {
        let mut out: Vec<Self> = Vec::with_capacity(k);
        let mut buf = vec![0u8; 2*k*LIMBS*8];  // twice the space taken by k base field elements
        Shake128::digest_xof(data, &mut buf);
        for j in 0..k {
            buf[2*(j + 1)*LIMBS*8 - 1] = 0;  // make sure the lift of this chunk to Z does not exceed the squared BLS24 modulus p^2
            let lo: Uint<LIMBS> = Uint::from_le_slice(&buf[2*j*LIMBS*8..(2*j + 1)*LIMBS*8]);
            let hi: Uint<LIMBS> = Uint::from_le_slice(&buf[(2*j + 1)*LIMBS*8..2*(j + 1)*LIMBS*8]);
            out.push(Self { 0: Self::redc(lo, hi), 1: Default::default() });
        }
        out
    }

    /// Hash input data into a list of base field elements with SHAKE-128.
    #[inline]
    pub(crate) fn shake256list(data: &[u8], k: usize) -> Vec<Self> {
        let mut out: Vec<Self> = Vec::with_capacity(k);
        let mut buf = vec![0u8; 2*k*LIMBS*8];  // twice the space taken by k base field elements
        Shake256::digest_xof(data, &mut buf);
        for j in 0..k {
            buf[2*(j + 1)*LIMBS*8 - 1] = 0;  // make sure the lift of this chunk to Z does not exceed the squared BLS24 modulus p^2
            let lo: Uint<LIMBS> = Uint::from_le_slice(&buf[2*j*LIMBS*8..(2*j + 1)*LIMBS*8]);
            let hi: Uint<LIMBS> = Uint::from_le_slice(&buf[(2*j + 1)*LIMBS*8..2*(j + 1)*LIMBS*8]);
            out.push(Self { 0: Self::redc(lo, hi), 1: Default::default() });
        }
        out
    }

    /// Convert an integer in Montgomery form to plain representation.
    ///
    /// NB: the plain representation of <i>m</i> = <i>w&middot;r</i> mod <i>p</i> is
    /// <i>w</i> = redc(<i>m</i>), where <i>r > p</i> is a power of 2.
    #[inline]
    pub(crate) fn to_uint(&self) -> Uint<LIMBS> {
        Self::redc(self.0, Uint::ZERO)
    }

    /// Compute <i>v</i> = `self`<i>&#x02E3;</i> mod <i>p</i>.
    #[inline]
    fn pow(&self, x: Uint<LIMBS>) -> Self {
        // this method is private, and the exponent (restricted to square root and inversion only)
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

    /// Determine if the plain representation of `self` is odd.
    #[inline]
    pub(crate) fn is_odd(&self) -> Choice {
        Self::redc(self.0, Uint::ZERO).is_odd()
    }

    /// Compute <i>r</i> = <i>&radic;`self`</i> = <i>`self`<sup>(p+1)/4</sup></i> mod <i>p</i>,
    /// which satisfies <i>r&sup2;</i> mod <i>p</i> = <i>`self`</i> if <i>`self`</i> is a quadratic residue mod <i>p</i>.
    #[inline]
    pub(crate) fn sqrt(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        self.pow((p + Uint::ONE).shr(2)) // sqrt exponent: (p + 1)/4
    }

    /// Compute <i>r</i> = <i>1/&radic;`self`</i> = <i>`self`</i><sup>(<i>p</i>+1)/4 - 1</sup> mod <i>p</i>,
    /// which satisfies <i>`self`&times;r&sup2;</i> mod <i>p = 1</i> if <i>`self` &ne; 0</i> and
    /// <i>`self`</i> is a quadratic residue mod <i>p</i>.
    #[inline]
    pub(crate) fn inv_sqrt(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        self.pow((p + Uint::ONE).shr(2) - Uint::ONE) // exponent: (p + 1)/4 - 1
    }

    /// Compute the Legendre symbol (<i>`self`/p</i>) in isochronous fashion:<br>
    /// &nbsp;   +1      if <i>`self`</i> is a nonzero quadratic residue mod <i>p</i>,<br>
    /// &nbsp;   &nbsp;0 if <i>`self`</i> = <i>0</i><br>
    /// &nbsp;   -1      if <i>`self`</i> is a nonzero quadratic non-residue mod <i>p</i>.
    ///
    /// NB: The Bernstein-Yang-based <a href="https://ia.cr/2021/1271">algorithm</a> by M. Hamburg
    /// is likely to be more efficient while also being isochronous, but its author claimed
    /// it is covered by a patent.  For that reason, that algorithm is entirely bypassed in this crate.
    #[inline]
    pub(crate) fn legendre(&self) -> isize {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        // (v/p) = v^((p - 1)/2) mod p for prime p
        let m = self.pow((p - Uint::ONE) >> 1).to_uint();
        // take the two least significant bits of m:
        let r = (m.as_words()[0] & 3) as isize;  // (v/p) = p-1, 0, 1
        // NB: since p = 3 (mod 4), it follows that -1 = 2 (mod 4)
        let val = -(r >> 1) + (r & 1);
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Fp<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self::Output {
            0: self.0.add_mod(&rhs.0, &nzp),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        self.0 = self.0.add_mod(&rhs.0, &nzp);
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Field for BLS24Fp<PAR, LIMBS> {
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
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self {
            0: self.0.add_mod(&self.0, &nzp),
            1: Default::default(),
        }
    }

    /// Compute `self`/2 mod <i>p</i>.
    ///
    /// Technique: if the lift of `self` (either in plain or in Montgomery form)
    /// to &Zopf; is even, a right-shift does the required division;
    /// if it is odd, then `self` + <i>p</i> is even,
    /// and hence 0 &leq; (`self` + <i>p</i>) &gt;&gt; 1 =
    /// (`self` &gt;&gt; 1) + (<i>p</i> + 1) &gt;&gt; 1 &lt; <i>p</i>
    /// is the desired value.
    #[inline]
    fn half(&self) -> Self {
        let hp: Uint<LIMBS> = (Uint::from_words(PAR::MODULUS.try_into().unwrap()) + Uint::ONE) >> 1;
        let hs = self.0 >> 1;
        Self {
            0: Uint::conditional_select(&hs, &hs.add(hp), self.0.is_odd()),
            1: Default::default(),
        }
    }

    /// Compute the square of a field element.
    #[inline]
    fn sq(&self) -> Self {
        let (lo, hi) = self.0.square_wide();
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Compute the cube of a field element.
    #[inline]
    fn cb(&self) -> Self {
        let (lo, hi) = self.0.square_wide();
        let (lo, hi) = self.0.widening_mul(&Self::redc(lo, hi));
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Compute <i>r</i> = <i>u&#8315;&sup1;</i> = <i>u&#x1D56;&#8315;&sup2;</i> mod <i>p</i>
    /// for <i>u</i> &#x2254; `self`, which satisfies
    /// <i>r&times;u</i> mod <i>p</i> = <i>1</i> if <i>u &ne; 0</i>.
    ///
    /// NB: crypto_bigint::Uint seems to offer an inversion functionality, but frankly,
    /// the usage instructions are poorly documented at best, entirely missing at worst.
    #[inline]
    fn inv(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        self.pow(p - Uint::from_word(2)) // inv exponent: p - 2
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Fp<PAR, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            0: self.0.clone(),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            0: Uint::conditional_select(&a.0, &b.0, choice),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }

    #[inline]
    fn ct_ne(&self, other: &Self) -> Choice {
        self.0.ct_ne(&other.0)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Fp<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Fp<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Fp<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        /*
        // signed format:
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let half_p= p.shr(1);
        let val = Self::redc(self.0, Uint::ZERO);
        let str = if val <= half_p {
            val.to_string_radix_vartime(10)
        } else {
            "-".to_string() + val.neg_mod(&p).to_string_radix_vartime(10).as_str()
        };
        write!(f, "{}", str)
        // */
        write!(f, "{}", Self::redc(self.0, Uint::ZERO).to_string_radix_vartime(10))
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul for BLS24Fp<PAR, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p</i></sub>.
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let (lo, hi) = self.0.widening_mul(&rhs.0);
        Self::Output {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp<PAR, LIMBS>> for Word {
    type Output = BLS24Fp<PAR, LIMBS>;

    /// Compute the product of a small integer left factor
    /// by a right factor from <b>F</b><sub><i>p</i></sub>.
    #[inline]
    fn mul(self, rhs: BLS24Fp<PAR, LIMBS>) -> Self::Output {
        assert!(self < 1 << 4);  // only meant for very small factors
        let mut val = Self::Output::zero();
        let mut fac = self as u8;
        let mut add = rhs;
        for _ in 0..4 {
            val = BLS24Fp::conditional_select(&val, &(val + add), Choice::from(fac & 1));
            fac >>= 1;
            add += add;
        }
        //assert_eq!(val, BLS24Fp::from_word(self)*rhs);
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp<PAR, LIMBS>> for i64 {
    type Output = BLS24Fp<PAR, LIMBS>;

    /// Compute the product of a single-precision, signed integer left factor
    /// by a right factor from <b>F</b><sub><i>p</i></sub>.
    ///
    /// This is a naïve implementation that treats the word-sized factor as a full-sized value.
    /// It would greatly benefit from dedicated i64&times;Int and/or i64&times;Uint functions.
    #[inline]
    fn mul(self, rhs: BLS24Fp<PAR, LIMBS>) -> Self::Output {
        let u = BLS24Fp::from_word(self.unsigned_abs())*rhs;
        Self::Output::conditional_select(&u, &(-u), Choice::from((self < 0) as u8))
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Fp<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p</i></sub>.
    #[inline]
    fn mul(self, rhs: BLS24Fp<PAR, LIMBS>) -> Self::Output {
        BLS24Fp::from_uint(self)*rhs
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        let (lo, hi) = self.0.widening_mul(&rhs.0);
        self.0 = Self::redc(lo, hi);
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Fp<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self::Output {
            0: self.0.neg_mod(&nzp),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> One for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn one() -> Self {
        let r2: Uint<LIMBS> = Uint::from_words(PAR::MONTY_P.try_into().unwrap());
        Self {
            0: Self::redc(r2, Uint::ZERO),  // (1*r) mod p
            1: Default::default(),
        }
    }

    fn is_one(&self) -> Choice {
        Self::redc(self.0, Uint::ZERO).ct_eq(&Uint::ONE)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq for BLS24Fp<PAR, LIMBS> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }

    fn ne(&self, other: &Self) -> bool {
        self.0.ct_ne(&other.0).into()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Fp<PAR, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p</i></sub> by rejection sampling mod <i>p</i>.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let top = PAR::MODULUS.len() - 1;
        let mask = (1 << (p.bits() & 63)) - 1;
        let mut w: [Word; LIMBS] = [0; LIMBS];
        loop {
            // uniformly sample the bit capacity of the modulus:
            //rng.fill(&mut w);  // deimplementing this useful function from crypto_bigint was a lusterless decision
            for i in 0..LIMBS {
                w[i] = rng.next_u64();
            }
            w[top] &= mask;
            // rejection sampling for the most significant word:
            while w[top].cmp(&PAR::MODULUS[top]).is_gt() {  // this means the whole value exceeds the modulus
                w[top] = rng.next_u64() & mask;
            }
            // rejection sampling for the whole value:
            let r = Uint::from_words(w);
            if r.cmp(&p).is_lt() {
                return Self::from_uint(r);
            }
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p</i></sub> by rejection sampling mod <i>p</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> where R: TryRngCore {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let top = PAR::MODULUS.len() - 1;
        let mask = (1 << (p.bits() & 63)) - 1;
        let mut w: [Word; LIMBS] = [0; LIMBS];
        loop {
            // uniformly sample the bit capacity of the modulus:
            for wi in &mut w {
                *wi = rng.try_next_u64()?
            }
            w[top] &= mask;
            // rejection sampling for the most significant word:
            while w[top].cmp(&PAR::MODULUS[top]).is_gt() {  // this means the whole value exceeds the modulus
                w[top] = rng.try_next_u64()? & mask;
            }
            // rejection sampling for the whole value:
            let r = Uint::from_words(w);
            if r.cmp(&p).is_lt() {
                return Ok(Self::from_uint(r));
            }
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Fp<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self::Output {
            0: self.0.sub_mod(&rhs.0, &nzp),
            1: Default::default(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        self.0 = self.0.sub_mod(&rhs.0, &nzp);
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Fp<PAR, LIMBS> {
    #[inline]
    fn zero() -> Self {
        Self {
            0: Uint::ZERO,  // (0*r) mod p
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
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BLS24Fp test template.
    #[allow(non_snake_case)]
    fn BLS24Fp_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();
        let nzp = NonZero::new(p).unwrap();

        println!();
        println!("Performing {} BLS24-{:03}Fp test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BLS24Fp::zero());
        assert!(bool::from(BLS24Fp::<PAR, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BLS24Fp::one());
        assert!(bool::from(BLS24Fp::<PAR, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // Montgomery form:
            let v1: Word = rng.next_u64() & 0xF;
            //println!("v1 = {}", v1);
            let m1: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_word(v1);
            //println!("m1 ? {}", m1);
            assert_eq!(Uint::from_word(v1), m1.to_uint());

            let e1: BLS24Fp<PAR, LIMBS> = BLS24Fp::random(&mut rng);
            //println!("e1     = {}", e1);
            //println!("e1 + 0 = {}", e1 + BLS24Fp::zero());
            assert_eq!(e1 + BLS24Fp::zero(), e1);
            //println!("e1*1   = {}", e1*BLS24Fp::one());
            assert_eq!(e1*BLS24Fp::one(), e1);

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

            // square roots:
            let sr1 = e1.sqrt();
            //println!("leg(e1)    = {}", e1.legendre());
            //println!("sqrt(e1)   = {}", sr1);
            //println!("sqrt(e1)^2 = {}", sr1.sq());
            assert!(sr1.sq() == e1 || e1.legendre() < 0 && sr1.sq() == -e1);
            let inv_sr1 = e1.inv_sqrt();
            //println!("1/sqrt(e1) = {}", inv_sr1);
            //println!("e1*(1/sqrt(e1))^2 = {}", e1*inv_sr1.sq());
            assert!(bool::from((e1*inv_sr1.sq()).is_one() | e1.is_zero()) || e1.legendre() < 0);

            // hybrid multiplication (Word*BLS24Fp and Uint*BLS24Fp):
            let k1: Word = rng.next_u64() & 0xF;
            //println!("k1*e1 = {}", k1*e1);
            //println!("k1*e1 ? {}", BLS24Fp::from_word(k1)*e1);
            assert_eq!(k1*e1, BLS24Fp::from_word(k1)*e1);
            let mut w1: [Word; LIMBS] = [0; LIMBS];
            //rng.fill(&mut w1);  // deimplementing this useful function from crypto_bigint was a lusterless decision
            for i in 0..LIMBS {
                w1[i] = rng.next_u64();
            }
            let u1 = Uint::from_words(w1).rem(&nzp);
            //println!("u1 = {}", u1.to_string_radix_vartime(10));
            //println!("u1*e1 = {}", u1*e1);
            //println!("u1*e1 ? {}", BLS24Fp::from_words(w1)*e1);
            assert_eq!(u1*e1, BLS24Fp::from_words(w1)*e1);

            let f1 = BLS24Fp::random(&mut rng);
            //println!("f1     = {}", f1);
            let g1 = BLS24Fp::random(&mut rng);
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
    fn BLS24317Fp_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Fp_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Fp_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Fp_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Fp_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Fp_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Fp_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Fp_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Fp_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Fp_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Fp_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Fp_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Fp_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Fp_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Fp_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Fp_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Fp_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Fp_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Fp_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Fp_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Fp_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Fp_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Fp_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Fp_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Fp_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Fp_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Fp_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Fp_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Fp_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Fp_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Fp_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Fp_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Fp_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Fp_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Fp_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Fp_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Fp_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Fp_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Fp_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Fp_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Fp_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Fp_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Fp_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Fp_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Fp_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Fp_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Fp_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Fp_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Fp_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Fp_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Fp_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Fp_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Fp_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Fp_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Fp_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Fp_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Fp_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Fp_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Fp_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Fp_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Fp_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Fp_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Fp_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Fp_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Fp_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Fp_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Fp_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Fp_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Fp_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Fp_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Fp_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Fp_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Fp_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Fp_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Fp_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Fp_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Fp_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Fp_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Fp_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Fp_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Fp_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Fp_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Fp_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Fp_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Fp_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Fp_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Fp_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Fp_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Fp_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Fp_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Fp_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Fp_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Fp_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Fp_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Fp_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Fp_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Fp_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Fp_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Fp_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Fp_test::<BLS24639Param, LIMBS>();
    }

}
