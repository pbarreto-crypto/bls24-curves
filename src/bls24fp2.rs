#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24fp::BLS24Fp;
use crate::bls24param::BLS24Param;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p&sup2;</i></sub> &simeq; <b>F</b><sub><i>p</i></sub>&lbrack;<i>i</i>&rbrack;/&lt;<i>i&sup2;</i> + 1&gt;
/// extension field.  NB: <i>i&sup2;</i> = -1.
pub struct BLS24Fp2<PAR: BLS24Param, const LIMBS: usize> {
    pub(crate) re: BLS24Fp<PAR, LIMBS>,
    pub(crate) im: BLS24Fp<PAR, LIMBS>,
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Fp2<PAR, LIMBS> {
    /// Convert an <b>F</b><sub><i>p</i></sub> element to its <b>F</b><sub><i>p&sup2;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp(re: BLS24Fp<PAR, LIMBS>) -> Self {
        Self {
            re,
            im: BLS24Fp::zero(),
        }
    }

    /// Convert a word-sized integer <i>w</i> to its <b>F</b><sub><i>p&sup2;</i></sub> counterpart.
    #[inline]
    pub fn from_word(w: Word) -> Self {
        Self {
            re: BLS24Fp::from_word(w),
            im: BLS24Fp::zero(),
        }
    }

    /// Convert an <b>F</b><sub><i>p</i></sub> element to its <b>F</b><sub><i>p&sup2;</i></sub> imaginary counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp_i(im: BLS24Fp<PAR, LIMBS>) -> Self {
        Self {
            re: BLS24Fp::zero(),
            im,
        }
    }

    /// Convert a word-sized integer <i>w</i> to its <b>F</b><sub><i>p&sup2;</i></sub> imaginary counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_word_i(w: Word) -> Self {
        Self {
            re: BLS24Fp::zero(),
            im: BLS24Fp::from_word(w),
        }
    }

    /// Assemble an <b>F</b><sub><i>p&sup2;</i></sub> element
    /// from its <b>F</b><sub><i>p</i></sub> components.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp_pair(re: BLS24Fp<PAR, LIMBS>, im: BLS24Fp<PAR, LIMBS>) -> Self {
        Self {
            re,
            im,
        }
    }

    /// Assemble an <b>F</b><sub><i>p&sup2;</i></sub> element
    /// from word-sized integers <i>w&#x1D63;&#x2091;</i> and <i>w&#x1D62;&#x2098;</i>.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_word_pair(w_re: Word, w_im: Word) -> Self {
        Self {
            re: BLS24Fp::from_word(w_re),
            im: BLS24Fp::from_word(w_im),
        }
    }

    /// Hash input data into a field element with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        let pair = BLS24Fp::shake128list(data, 2);
        Self {
            re: pair[0],
            im: pair[1],
        }
    }

    /// Hash input data into a field element with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        let pair = BLS24Fp::shake256list(data, 2);
        Self {
            re: pair[0],
            im: pair[1],
        }
    }

    #[inline]
    pub(crate) fn is_odd(&self) -> Choice {
        self.re.is_odd()
    }

    /// Complex conjugate of `self` in <b>F</b><sub><i>p&sup2;</i></sub>
    /// over <b>F</b><sub><i>p</i></sub>, i.e. if `self` = <i>a + bi</i>, return <i>a - bi</i>.
    /// This is the same as applying the Frobenius endomorphism to `self`,
    /// i.e. computing `self`<i>&#x1D56;</i> in <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    pub(crate) fn conj(&self) -> Self {
        Self { re: self.re, im: -self.im, }
    }

    /// <b>F</b><sub><i>p</i></sub>-norm of this <b>F</b><sub><i>p&sup2;</i></sub> element,
    /// namely, if this element is <i>u + vi</i>, return <i>u&sup2; + v&sup2;</i>.
    #[inline]
    pub(crate) fn norm(&self) -> BLS24Fp<PAR, LIMBS> {
        self.re.sq() + self.im.sq()
    }

    /// Compute the product of a field element <i>x + yi</i> by <i>i</i>.
    #[inline]
    pub(crate) fn mul_i(&self) -> Self {
        // (x + yi)i = (-y + xi)
        Self { re: -self.im, im: self.re, }
    }

    /// Compute the product of `self` = <i>x</i> + <i>yi</i> by <i>&xi;</i> &#x2254; 1 + <i>i</i>.
    #[inline]
    pub(crate) fn mul_xi(&self) -> Self {
        // (x + yi)*(1 + i) = (x - y) + (x + y)i
        Self {
            re: self.re - self.im,
            im: self.re + self.im,
        }
    }

    /// Compute the product of `self` = <i>x</i> + <i>yi</i> by <i>conj</i>(<i>&xi;</i>) &#x2254; 1 - <i>i</i>.
    #[inline]
    pub(crate) fn mul_ix(&self) -> Self {
        // (x + yi)*(1 - i) = (x + y) + (y - x)i
        Self {
            re: self.re + self.im,
            im: self.im - self.re,
        }
    }

    /// Compute the quotient of a field element <i>x + yi</i> by <i>&xi; := 1 + i</i>.
    #[inline]
    pub(crate) fn div_xi(&self) -> Self {
        // (x + yi)/(1 + i) = (x + yi)(1 - i)/((1 + i)*(1 - i)) = (x + yi)(1 - i)/2
        // = (x + yi)/2 - (xi - y)/2 = (x + y)/2 + (y - x)i/2
        Self {
            re: (self.re + self.im).half(),
            im: (self.im - self.re).half(),
        }
    }

    /// Compute a square root √<i>c</i> of this element <i>c</i> &#x2254; <i>a</i> + <i>bi</i> &in; <b>F</b><sub><i>p&sup2;</i></sub>
    /// if <i>c</i> is a quadratic residue, otherwise compute √(<i>c&xi;</i>)/&ldquo;√<i>&xi;</i>&rdquo;
    /// where &ldquo;√<i>&xi;</i>&rdquo; &#x2254; <i>&xi;</i><sup>(<i>p&sup2;</i> + 7)/16</sup>
    /// is the formal square root of <i>&xi;</i> within <b>F</b><sub><i>p&sup2;</i></sub> (a normalization factor).
    ///
    /// References:
    ///
    /// * P. Friedland. Algorithm 312: Absolute value and square root of a complex number.
    /// Communications of the ACM, 10(10):665, 1967.
    ///
    /// * M. Scott, ``Implementing cryptographic pairings'' (invited talk),
    /// International Conference on Pairing-Based Cryptography -- Pairing 2007,
    /// Lecture Notes in Computer Science, vol. 4575, pp. 177--196, Springer, 2007.
    /// https://link.springer.com/book/10.1007/978-3-540-73489-5
    #[inline]
    pub(crate) fn sqrt(&self) -> Self {
        let lambda: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::NEG_SQRT_NEG_2.try_into().unwrap());
        let omega: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::QNR_SCALE.try_into().unwrap());
        let one: BLS24Fp<PAR, LIMBS> = BLS24Fp::one();
        let n = self.norm();  // n = (a^2 + b^2) mod p
        let inv_m = n.inv_sqrt();
        let mut m = n*inv_m;
        let qcn = m*inv_m;  // quadratic character of n: qcn in {-1 mod p, 0, 1}
        let sqn = qcn.is_zero() | qcn.is_one();  // whether or not n is a square
        let a: BLS24Fp<PAR, LIMBS> = BLS24Fp::conditional_select(&(self.re - self.im), &self.re, sqn);
        let b: BLS24Fp<PAR, LIMBS> = BLS24Fp::conditional_select(&(self.re + self.im), &self.im, sqn);
        m *= BLS24Fp::conditional_select(&lambda, &one, sqn);
        let tau = BLS24Fp::conditional_select(&omega, &one, sqn);
        let z = BLS24Fp::conditional_select(&(a + m).half(), &a, b.is_zero());
        let t = z.inv_sqrt();
        let r = z*t;
        let s = b*t.half();
        let qcz = r*t;  // quadratic character of z: qcz in {-1 mod p, 0, 1}
        let sqz = qcz.is_zero() | qcz.is_one();  // whether or not z is a square
        let rho = BLS24Fp::conditional_select(&s, &r, sqz)*tau;
        let sigma = BLS24Fp::conditional_select(&(-r), &s, sqz)*tau;
        BLS24Fp2::from_Fp_pair(rho, sigma)
    }

    /// Compute an inverse square root 1/√<i>c</i> of this element <i>c</i> &#x2254; <i>a</i> + <i>bi</i> &in; <b>F</b><sub><i>p&sup2;</i></sub>
    /// if <i>c</i> is a nonzero quadratic residue, or &ldquo;√<i>&xi;</i>&rdquo;/√(<i>c&xi;</i>)
    /// if <i>c</i> is a quadratic non-residue, or simply zero if <i>c</i> = 0,
    /// where &ldquo;√<i>&xi;</i>&rdquo; &#x2254; <i>&xi;</i><sup>(<i>p&sup2;</i> + 7)/16</sup>
    /// is the formal square root of <i>&xi;</i> within <b>F</b><sub><i>p&sup2;</i></sub> (a normalization factor).
    #[inline]
    pub(crate) fn inv_sqrt(&self) -> Self {
        let lambda: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::NEG_SQRT_NEG_2.try_into().unwrap());
        let omega: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::QNR_SCALE.try_into().unwrap());
        let one: BLS24Fp<PAR, LIMBS> = BLS24Fp::one();
        let n = self.norm();  // n = (a^2 + b^2) mod p
        let inv_m = n.inv_sqrt();
        let mut m = n*inv_m;
        let qcn = m*inv_m;  // quadratic character of n: qcn in {-1 mod p, 0, 1}
        let sqn = qcn.is_zero() | qcn.is_one();  // whether or not n is a square
        let a: BLS24Fp<PAR, LIMBS> = BLS24Fp::conditional_select(&(self.re - self.im), &self.re, sqn);
        let b: BLS24Fp<PAR, LIMBS> = BLS24Fp::conditional_select(&(self.re + self.im), &self.im, sqn);
        m *= BLS24Fp::conditional_select(&lambda, &one, sqn);
        let tau = BLS24Fp::conditional_select(&omega, &one, sqn);
        let z = BLS24Fp::conditional_select(&(a + m).half(), &a, b.is_zero());
        let t = z.inv_sqrt();
        let r = z*t;
        let s = b*t.half();
        let qcz = r*t;  // quadratic character of z: qcz in {-1 mod p, 0, 1}
        let sqz = qcz.is_zero() | qcz.is_one();  // whether or not z is a square
        let rho = BLS24Fp::conditional_select(&s, &r, sqz)*tau;
        let sigma = BLS24Fp::conditional_select(&(-r), &s, sqz)*tau;
        let fudge = BLS24Fp::conditional_select(&(inv_m*omega), &inv_m, sqn);
        fudge.sq()*BLS24Fp2::from_Fp_pair(rho, sigma)*BLS24Fp2::from_Fp_pair(a, -b)
    }

    /// Compute the generalized Legendre symbol (<i>u</i>/<b>F</b><sub><i>p&sup2;</sub></i>):<br>
    /// &nbsp;   +1      if <i>u</i> is a nonzero quadratic residue in <b>F</b><sub><i>p&sup2;</i></sub>,<br>
    /// &nbsp;   &nbsp;0 if <i>u</i> = <i>0</i><br>
    /// &nbsp;   -1      if <i>u</i> is a nonzero quadratic non-residue in <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    pub(crate) fn legendre(&self) -> isize {
        self.norm().legendre()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Fp2<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.re += rhs.re;
        self.im += rhs.im;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Field for BLS24Fp2<PAR, LIMBS> {
    /// Convert `self` to byte array representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let mut rev = self.re.to_bytes();
        let mut imv = self.im.to_bytes();
        rev.append(&mut imv);
        rev
    }

    /// Compute the value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        Self {
            re: self.re.double(),
            im: self.im.double(),
        }
    }

    /// Compute the value of half this element.
    #[inline]
    fn half(&self) -> Self {
        Self {
            re: self.re.half(),
            im: self.im.half(),
        }
    }

    /// Compute the square of this <b>F</b><sub><i>p&sup2;</i></sub> element.
    #[inline]
    fn sq(&self) -> Self {
        // (u + vi)^2 = u^2 - v^2 + 2uvi = (u + v)*(u - v) + 2uvi
        let repim = self.re + self.im;
        let remim = self.re - self.im;
        let retim = self.re*self.im;
        Self {
            re: repim*remim,
            im: retim + retim
        }
    }

    /// Compute the cube of this <b>F</b><sub><i>p&sup2;</i></sub> element.
    #[inline]
    fn cb(&self) -> Self {
        // (u + vi)^3 = u*(u^2 - 3*v^2) + v*(3*u^2 - v^2) i
        let re2 = self.re.sq();
        let im2 = self.im.sq();
        let d = re2 - im2;
        Self {
            re: self.re*(d - im2 - im2),
            im: self.im*(re2 + re2 + d)
        }
    }

    /// Compute the inverse of `self` in <b>F</b><sub><i>p&sup2;</i></sub>
    /// (or 0, if `self` is itself 0).
    #[inline]
    fn inv(&self) -> Self {
        // (u + vi)^-1 = (u^2 + v^2)^-1*(u - vi) = norm^-1*conj.
        self.norm().inv()*self.conj()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn clone(&self) -> Self {
        Self { re: self.re.clone(), im: self.im.clone() }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            re: BLS24Fp::conditional_select(&a.re, &b.re, choice),
            im: BLS24Fp::conditional_select(&a.im, &b.im, choice),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.re.ct_eq(&other.re) & self.im.ct_eq(&other.im)
    }

    #[inline]
    fn ct_ne(&self, other: &Self) -> Choice {
        self.re.ct_ne(&other.re) | self.im.ct_ne(&other.im)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Fp2<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Fp2<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Fp2<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.im.is_zero()) {
            write!(f, "{}",
                   self.re.to_string()
            )
        } else if bool::from(self.re.is_zero()) {
            if bool::from(self.im.is_one()) {
                write!(f, "i")
            } else if bool::from((-self.im).is_one()) {
                write!(f, "-i")
            } else {
                write!(f, "{}*i",
                       self.im.to_string()
                )
            }
        } else {
            if bool::from(self.im.is_one()) {
                write!(f, "{} + i", self.re.to_string())
            } else if bool::from((-self.im).is_one()) {
                write!(f, "{} - i", self.re.to_string())
            } else {
                let strim = self.im.to_string();
                if strim.chars().next() != Some('-') {
                    write!(f, "{} + {}*i",
                           self.re.to_string(),
                           strim
                    )
                } else {
                    write!(f, "{} - {}*i",
                           self.re.to_string(),
                           &strim[1..].to_string()
                    )
                }
            }
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul for BLS24Fp2<PAR, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp2<PAR, LIMBS>> for Word {
    type Output = BLS24Fp2<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: BLS24Fp2<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp2<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Fp2<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: BLS24Fp2<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp2<PAR, LIMBS>> for BLS24Fp<PAR, LIMBS> {
    type Output = BLS24Fp2<PAR, LIMBS>;

    /// Compute the product of a left factor from <b>F</b><sub><i>p</i></sub>
    /// by a right factor from <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: BLS24Fp2<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        // (a + bi)*(u + vi) = au - bv + (av + bu)i
        // (a + b)*(u + v) - au - bv = av + bu
        let re2 = self.re*rhs.re;
        let im2 = self.im*rhs.im;
        let mix = (self.re + self.im)*(rhs.re + rhs.im);
        self.re = re2 - im2;
        self.im = mix - re2 - im2;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Fp2<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::Output {
            re: -self.re,
            im: -self.im,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> One for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn one() -> Self {
        BLS24Fp2::from_word(1)
    }

    #[inline]
    fn is_one(&self) -> Choice {
        self.re.is_one() & self.im.is_zero()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    #[inline]
    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Fp2<PAR, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&sup2;</i></sub> by rejection sampling.
    #[inline]
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            re: BLS24Fp::random(rng),
            im: BLS24Fp::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&sup2;</i></sub> by rejection sampling.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> where R: TryRngCore {
        let try_re = match BLS24Fp::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;
        let try_im = match BLS24Fp::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;
        Ok(Self { re: try_re, im: try_im })
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Fp2<PAR, LIMBS> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.re -= rhs.re;
        self.im -= rhs.im;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Fp2<PAR, LIMBS> {
    #[inline]
    fn zero() -> Self {
        Self {
            re: BLS24Fp::zero(),
            im: BLS24Fp::zero(),
        }
    }

    #[inline]
    fn is_zero(&self) -> Choice {
        self.re.is_zero() & self.im.is_zero()
    }

    #[inline]
    fn set_zero(&mut self) {
        self.re.set_zero();
        self.im.set_zero()
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
    use crypto_bigint::{NonZero, RandomMod};
    use crypto_bigint::rand_core::RngCore;
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BLS24Fp2 test template.
    #[allow(non_snake_case)]
    fn BLS24Fp2_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let msqrt_m2: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::NEG_SQRT_NEG_2.try_into().unwrap());
        let sqrti: BLS24Fp2<PAR, LIMBS> = -BLS24Fp2::from_Fp(msqrt_m2).div_xi();

        let mut rng = rand::rng();

        println!();
        println!("Performing {} BLS24-{:03}Fp2 test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BLS24Fp2::zero());
        assert!(bool::from(BLS24Fp2::<PAR, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BLS24Fp2::one());
        assert!(bool::from(BLS24Fp2::<PAR, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e2: BLS24Fp2<PAR, LIMBS> = BLS24Fp2::random(&mut rng);
            //println!("e2 = {}", e2);
            //println!("e2 + 0 = {}", e2 + BLS24Fp2::zero());
            assert_eq!(e2 + BLS24Fp2::zero(), e2);
            //println!("e2*1 = {}", e2*BLS24Fp2::one());
            assert_eq!(e2*BLS24Fp2::one(), e2);

            // addition vs subtraction:
            //println!("-e1      = {}", -e1);
            //println!("e1 - e1  = {}", e1 - e1);
            //println!("e1+(-e1) = {}", e1 + (-e1));
            assert!(bool::from((e2 - e2).is_zero()));
            assert!(bool::from((e2 + (-e2)).is_zero()));

            // double and half:
            //println!("2*e1   = {}", e1.double());
            //println!("e1/2   = {}", e1.half());
            assert_eq!(e2.double().half(), e2);
            assert_eq!(e2.half().double(), e2);
            assert_eq!(e2.double()*e2.half(), e2.sq());

            // square and cube:
            //println!("e2^2       = {}", e2.sq());
            //println!("e2^2 = e2*e2 ? {}", e2.sq() == e2*e2);
            assert_eq!(e2.sq(), e2*e2);
            //println!("e2^3       = {}", e2.cb());
            //println!("e2^3 = e2*e2*e2 ? {}", e2.cb() == e2*e2*e2);
            assert_eq!(e2.cb(), e2*e2*e2);

            // norm:
            //println!("|e2| = {}", e2.norm());
            //println!("|e2| = e2*e2.conj() ? {}", bool::from((e2*e2.conj()).re.ct_eq(&e2.norm()) & (e2*e2.conj()).im.is_zero()));
            assert!(bool::from((e2*e2.conj()).re.ct_eq(&e2.norm()) & (e2*e2.conj()).im.is_zero()));

            // field inversion:
            //println!("e2^-1 = {}", e2.inv());
            //println!("e2*e2^-1 = {}", e2*e2.inv());
            assert!(bool::from((e2*e2.inv()).is_one()));

            // square roots:
            let e1: BLS24Fp2<PAR, LIMBS> = BLS24Fp2::from_Fp(BLS24Fp::random(&mut rng));
            let sr1 = e1.sqrt();
            assert!(e1.legendre() >= 0);
            assert!(bool::from(!sr1.is_zero() | e1.is_zero()));  // square root of Fp value always exists in Fp2
            assert_eq!(sr1.sq(), e1);
            let sr2 = e2.sqrt();
            assert!(bool::from(sr2.sq() == e2 || sr2.sq() == -e2.mul_i()*sqrti));
            let inv_sr2 = e2.inv_sqrt();
            //println!("p          = {}", p.to_string_radix_vartime(10));
            //println!("e2         = {}", e2);
            //println!("sqrt(e2)   = {}", sr2);
            //println!("1/sqrt(e2) = {}", inv_sr2);
            assert!(bool::from((sr2*inv_sr2).is_one() | e2.is_zero()));
            if e2.legendre() >= 0 {
                assert_eq!(e2, sr2.sq());
                assert!(bool::from((e2*inv_sr2.sq()).is_one() | e2.is_zero()));
            } else {
                assert_eq!(e2, sqrti*sr2.sq());
                assert_eq!(e2*inv_sr2.sq(), sqrti);
            }

            // subgroup multiplication (Word*BLS24Fp2, Uint*BLS24Fp2, and BLS24Fp*BLS24Fp2):
            let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
            let k2: Word = rng.next_u64() & 0xF;
            //println!("k2*e2 = {}", k2*e2);
            //println!("k2*e2 ? {}", BLS24Fp::from_word(k2)*e2);
            assert_eq!(k2*e2, BLS24Fp::from_word(k2)*e2);
            let u2 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u2 = {}", u2.to_string_radix_vartime(20));
            //println!("u2*e2 = {}", u2*e2);
            assert_eq!(u2*e2, BLS24Fp::from_uint(u2)*e2);
            assert_eq!(u2*e2, BLS24Fp2::from_Fp_pair(BLS24Fp::from_uint(u2), BLS24Fp::zero())*e2);

            let e3 = BLS24Fp2::random(&mut rng);
            //println!("e3 = {}", e3);

            // norm homomorphism:
            //println!("|e3| = {}", e3.norm());
            //println!("|e2*e3| = |e2|*|e3| ? {}", (e2*e3).norm() == e2.norm()*e3.norm());
            assert_eq!((e2*e3).norm(), e2.norm()*e3.norm());

            let f2 = BLS24Fp2::random(&mut rng);
            //println!("f2     = {}", f2);
            let g2 = BLS24Fp2::random(&mut rng);
            //println!("g2     = {}", g2);

            // commutativity of addition and multiplication:
            //println!("e2 + f2 = {}", e2 + f2);
            //println!("f2 + e2 = {}", f2 + e2);
            assert_eq!(e2 + f2, f2 + e2);
            assert_eq!(e2*f2, f2*e2);

            // associativity:
            //println!("(e2 + f2) + g2 = {}", (e2 + f2) + g2);
            //println!("e2 + (f2 + g2) = {}", e2 + (f2 + g2));
            assert_eq!((e2 + f2) + g2, e2 + (f2 + g2));
            //println!("(e2*f2)*g2 = {}", (e2*f2)*g2);
            //println!("e2*(f2*g2) = {}", e2*(f2*g2));
            assert_eq!((e2*f2)*g2, e2*(f2*g2));
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
    fn BLS24317Fp2_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Fp2_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Fp2_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Fp2_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Fp2_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Fp2_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Fp2_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Fp2_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Fp2_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Fp2_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Fp2_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Fp2_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Fp2_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Fp2_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Fp2_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Fp2_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Fp2_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Fp2_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Fp2_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Fp2_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Fp2_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Fp2_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Fp2_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Fp2_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Fp2_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Fp2_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Fp2_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Fp2_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Fp2_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Fp2_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Fp2_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Fp2_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Fp2_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Fp2_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Fp2_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Fp2_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Fp2_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Fp2_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Fp2_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Fp2_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Fp2_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Fp2_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Fp2_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Fp2_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Fp2_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Fp2_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Fp2_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Fp2_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Fp2_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Fp2_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Fp2_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Fp2_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Fp2_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Fp2_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Fp2_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Fp2_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Fp2_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Fp2_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Fp2_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Fp2_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Fp2_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Fp2_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Fp2_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Fp2_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Fp2_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Fp2_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Fp2_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Fp2_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Fp2_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Fp2_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Fp2_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Fp2_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Fp2_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Fp2_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Fp2_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Fp2_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Fp2_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Fp2_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Fp2_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Fp2_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Fp2_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Fp2_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Fp2_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Fp2_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Fp2_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Fp2_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Fp2_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Fp2_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Fp2_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Fp2_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Fp2_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Fp2_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Fp2_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Fp2_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Fp2_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Fp2_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Fp2_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Fp2_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Fp2_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Fp2_test::<BLS24639Param, LIMBS>();
    }

}
