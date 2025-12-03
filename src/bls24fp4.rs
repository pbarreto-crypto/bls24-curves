#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24fp::BLS24Fp;
use crate::bls24fp2::BLS24Fp2;
use crate::bls24param::BLS24Param;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p&#x2074;</i></sub> &simeq;
/// <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>v</i>&rbrack;/&lt;<i>v&sup2;</i> + <i>&xi;</i>&gt;
/// extension field, with <i>&xi;</i> = 1 + <i>i</i>.  NB: <i>v&sup2;</i> = -<i>&xi;</i>.
pub struct BLS24Fp4<PAR: BLS24Param, const LIMBS: usize> {
    pub(crate) re: BLS24Fp2<PAR, LIMBS>,
    pub(crate) im: BLS24Fp2<PAR, LIMBS>,
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Fp4<PAR, LIMBS> {
    /// Convert an <b>F</b><sub><i>p&sup2;</i></sub> element to its <b>F</b><sub><i>p&#x2074;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp2(re: BLS24Fp2<PAR, LIMBS>) -> Self {
        Self {
            re,
            im: BLS24Fp2::zero(),
        }
    }

    /// Convert an <b>F</b><sub><i>p</i></sub> element to its <b>F</b><sub><i>p&#x2074;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp(re: BLS24Fp<PAR, LIMBS>) -> Self {
        Self {
            re: BLS24Fp2::from_Fp(re),
            im: BLS24Fp2::zero(),
        }
    }

    /// Convert a word-sized integer <i>w</i> to its <b>F</b><sub><i>p&#x2074;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_word(w: Word) -> Self {
        Self {
            re: BLS24Fp2::from_word(w),
            im: BLS24Fp2::zero(),
        }
    }

    /// Assemble an <b>F</b><sub><i>p&#x2074;</i></sub> element
    /// from its <b>F</b><sub><i>p&sup2;</i></sub> components.
    #[inline]
    pub(crate) fn from(re: BLS24Fp2<PAR, LIMBS>, im: BLS24Fp2<PAR, LIMBS>) -> Self {
        Self {
            re,
            im,
        }
    }

    /// Hash input data into a field element with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        let tuple = BLS24Fp::shake128list(data, 4);
        Self {
            re: BLS24Fp2::from_Fp_pair(tuple[0], tuple[1]),
            im: BLS24Fp2::from_Fp_pair(tuple[2], tuple[3]),
        }
    }

    /// Hash input data into a field element with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        let tuple = BLS24Fp::shake256list(data, 4);
        Self {
            re: BLS24Fp2::from_Fp_pair(tuple[0], tuple[1]),
            im: BLS24Fp2::from_Fp_pair(tuple[2], tuple[3]),
        }
    }

    /// Create an instance of the element <i>v</i> &in; <b>F</b><sub><i>p&#x2074;</i></sub>.
    #[inline]
    pub(crate) fn v() -> Self {
        Self {
            re: BLS24Fp2::zero(),
            im: BLS24Fp2::one(),
        }
    }

    #[inline]
    pub(crate) fn is_odd(&self) -> Choice {
        self.re.is_odd()
    }

    /// Apply the Frobenius endomorphism to `self`,
    /// i.e. compute `self`<i>&#x1D56;</i> in <b>F</b><sub><i>p&#x2074;</i></sub>.
    #[inline]
    pub(crate) fn frob(&self) -> Self {
        let c: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::NEG_SQRT_NEG_2.try_into().unwrap()).half();  // c := -sqrt(-2)/2
        Self {
            re: self.re.conj(),
            im: c*self.im.conj().mul_xi(),
        }
    }

    /// Conjugate of `self` in <b>F</b><sub><i>p&#x2074;</i></sub>
    /// over <b>F</b><sub><i>p&sup2;</i></sub>, namely, `self`<sup><i>p</i>&sup2;</sup>.
    #[inline]
    pub(crate) fn conj(&self) -> Self {
        Self {
            re: self.re,
            im: -self.im,
        }
    }

    /// Product of `self` = <i>a</i> + <i>b</i><i>v</i> by <i>i</i>.
    #[inline]
    pub(crate) fn mul_i(&self) -> Self {
        // (a + bv)*i = (a*i) + (b*i)*v
        Self {
            re: self.re.mul_i(), im: self.im.mul_i(),
        }
    }

    /// Product of `self` = <i>a</i> + <i>b</i><i>v</i> by <i>&xi;</i> &#x2254; 1 + <i>i</i>.
    #[inline]
    pub(crate) fn mul_xi(&self) -> Self {
        // (a + bv)*xi = (a*xi) + (b*xi)v
        Self {
            re: self.re.mul_xi(),
            im: self.im.mul_xi(),
        }
    }

    /// Product of `self` = <i>a</i> + <i>b</i><i>v</i> by <i>conj</i>(<i>&xi;</i>) &#x2254; 1 - <i>i</i>.
    #[inline]
    pub(crate) fn mul_ix(&self) -> Self {
        // (a + bv)*conj(xi) = (a*conj(xi)) + (b*conj(xi))v
        Self {
            re: self.re.mul_ix(),
            im: self.im.mul_ix(),
        }
    }

    /// Quotient of `self` = <i>a</i> + <i>b</i><i>v</i> by <i>&xi; := 1 + i</i>.
    #[inline]
    pub(crate) fn div_xi(&self) -> Self {
        // (a + bv)/xi = (a/xi) + (b/xi)v
        Self {
            re: self.re.div_xi(),
            im: self.im.div_xi(),
        }
    }

    /// Product of `self` = <i>a</i> + <i>b</i><i>v</i> by <i>v</i>.
    #[inline]
    pub(crate) fn mul_v(&self) -> Self {
        // (a, b)*v = (a + b*v)*v = -b*ξ + a*v = (-b*ξ, a)
        Self {
            re: -self.im.mul_xi(), im: self.re,
        }
    }

    /// Quotient of `self` = <i>a</i> + <i>b</i><i>v</i> by <i>v</i>.
    #[inline]
    pub(crate) fn div_v(&self) -> Self {
        // (a, b)/v = (a + b*v)*v/v^2 = -(-b*ξ + a*v)/ξ = b - (a/ξ)*v = (b, -a/ξ)
        Self {
            re: self.im, im: -self.re.div_xi(),
        }
    }

    /// <b>F</b><sub><i>p&sup2;</i></sub>-norm of this <b>F</b><sub><i>p&#x2074;</i></sub> element,
    /// namely, if `self` <i>a + bv</i>, return <i>a&sup2; + b&sup2;&xi;</i>.
    #[inline]
    pub(crate) fn norm(&self) -> BLS24Fp2<PAR, LIMBS> {
        // (a + b*v)*(a - b*v) = a^2 - b^2*v^2 = a^2 + b^2*xi
        self.re.sq() + self.im.sq().mul_xi()
    }

    /// Compute the square root of this element <i>a</i> + <i>bv</i> &in; <b>F</b><sub><i>p&#x2074;</i></sub>,
    /// with a "real" part with a specified least-significant bit (`lsb`), if such a root exists
    /// (otherwise return zero).
    ///
    /// Reference:
    ///
    /// *; M. Scott, ``Implementing cryptographic pairings'' (invited talk),
    /// International Conference on Pairing-Based Cryptography -- Pairing 2007,
    /// Lecture Notes in Computer Science, vol. 4575, pp. 177--196, Springer, 2007.
    /// https://link.springer.com/book/10.1007/978-3-540-73489-5
    #[inline]
    pub(crate) fn sqrt(&self) -> Self {
        let omega: BLS24Fp2<PAR, LIMBS> = BLS24Fp2::from_Fp(BLS24Fp::from_words(PAR::QNR_SCALE.try_into().unwrap()));
        let n = self.norm();  // n = a^2 + b^2*xi
        let m = n.sqrt();  // m^2 in {n, n/sqrt(i)}
        let sqn = m.sq().ct_eq(&n);  // whether or not n is a square
        let z = BLS24Fp2::conditional_select(&(self.re + m).half(), &self.re, self.im.is_zero());
        let t = z.inv_sqrt();
        let qcz = z*t.sq();  // quadratic character of z: qcz in {sqrt(i), 0, 1}
        let sqz = qcz.is_zero() | qcz.is_one();  // whether or not z is a square
        let r = z*t;
        let s = self.im*t.half();
        let rho = BLS24Fp2::conditional_select(&(omega.double().div_xi()*s), &r, sqz);
        let sigma = BLS24Fp2::conditional_select(&(omega.mul_i()*r), &s, sqz);
        BLS24Fp4::conditional_select(&BLS24Fp4::zero(), &BLS24Fp4::from(rho, sigma), sqn)
    }

    /// Compute the generalized Legendre symbol (<i>u</i>/<b>F</b><sub><i>p&#x2074;</sub></i>):<br>
    /// &nbsp;   +1      if <i>u</i> is a nonzero quadratic residue in <b>F</b><sub><i>p&#x2074;</i></sub>,<br>
    /// &nbsp;   &nbsp;0 if <i>u</i> = <i>0</i><br>
    /// &nbsp;   -1      if <i>u</i> is a nonzero quadratic non-residue in <b>F</b><sub><i>p&#x2074;</i></sub>.
    #[inline]
    pub(crate) fn legendre(&self) -> isize {
        self.norm().legendre()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Fp4<PAR, LIMBS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Fp4<PAR, LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.re += rhs.re;
        self.im += rhs.im;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Field for BLS24Fp4<PAR, LIMBS> {
    /// Convert `self` to serialized (byte array) representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let mut rev = self.re.to_bytes();
        let mut imv = self.im.to_bytes();
        rev.append(&mut imv);
        rev
    }

    /// Value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        Self {
            re: self.re.double(),
            im: self.im.double(),
        }
    }

    /// Value of half this element.
    #[inline]
    fn half(&self) -> Self {
        Self {
            re: self.re.half(),
            im: self.im.half(),
        }
    }

    /// Compute the square of this <b>F</b><sub><i>p&#x2074;</i></sub> element.
    #[inline]
    fn sq(&self) -> Self {
        // (a + b*v)^2 = a^2 - b^2*xi + 2*a*b*v = (a^2 - b^2*xi) + ((a + b)^2 - a^2 - b^2)*w
        let a2 = self.re.sq();
        let b2 = self.im.sq();
        let ab = (self.re + self.im).sq();
        Self {
            re: a2 - b2.mul_xi(),
            im: ab - a2 - b2
        }
    }

    /// Compute the cube of this <b>F</b><sub><i>p&sup2;</i></sub> element.
    #[inline]
    fn cb(&self) -> Self {
        // (a + b*v)^3 = a^3 + 3*a^2*b*v - 3*a*b^2*xi - b^3*xi*v
        // = a*((a^2 - b^2*xi) - 2*b^2*xi) + (2*a^2 + (a^2 - b^2*xi))*b*v
        let re2 = self.re.sq();
        let im2 = self.im.sq().mul_xi();
        let d = re2 - im2;
        Self {
            re: self.re*(d - im2 - im2),
            im: self.im*(re2 + re2 + d)
        }
    }

    /// Compute the inverse of this <b>F</b><sub><i>p&#x2074;</i></sub> element
    /// (or 0, if this element is itself 0).
    #[inline]
    fn inv(&self) -> Self {
        // (a + b*v)^-1 = (a - b*v)/(a^2 + b^2*xi) = norm^-1*conj.
        self.norm().inv()*self.conj()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Fp4<PAR, LIMBS> {
    fn clone(&self) -> Self {
        Self { re: self.re.clone(), im: self.im.clone() }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Fp4<PAR, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            re: BLS24Fp2::conditional_select(&a.re, &b.re, choice),
            im: BLS24Fp2::conditional_select(&a.im, &b.im, choice),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Fp4<PAR, LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.re.ct_eq(&other.re) & self.im.ct_eq(&other.im)
    }

    fn ct_ne(&self, other: &Self) -> Choice {
        self.re.ct_ne(&other.re) | self.im.ct_ne(&other.im)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Fp4<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Fp4<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Fp4<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.im.is_zero()) {
            write!(f, "{}", self.re)
        } else if bool::from(self.re.is_zero()) {
            write!(f, "({})*v", self.im)
        } else {
            write!(f, "({}) + ({})*v", self.re, self.im)
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul for BLS24Fp4<PAR, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp4<PAR, LIMBS>> for Word {
    type Output = BLS24Fp4<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp4<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp4<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Fp4<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp4<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp4<PAR, LIMBS>> for BLS24Fp<PAR, LIMBS> {
    type Output = BLS24Fp4<PAR, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp4<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp4<PAR, LIMBS>> for BLS24Fp2<PAR, LIMBS> {
    type Output = BLS24Fp4<PAR, LIMBS>;

    /// Compute the product of a left factor from <b>F</b><sub><i>p&sup2;</i></sub>
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp4<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign for BLS24Fp4<PAR, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        // (a + b*v)*(c + d*v) = a*c - b*d*xi + (a*d + b*c)*v
        // (a + b)*(c + d) - a*c - b*d = a*d + b*c
        let re2 = self.re*rhs.re;
        let im2 = self.im*rhs.im;
        let mix = (self.re + self.im)*(rhs.re + rhs.im);
        self.re = re2 - im2.mul_xi();
        self.im = mix - re2 - im2;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Fp4<PAR, LIMBS> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Output {
            re: -self.re,
            im: -self.im,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> One for BLS24Fp4<PAR, LIMBS> {
    #[inline]
    fn one() -> Self {
        Self {
            re: BLS24Fp2::one(),
            im: BLS24Fp2::zero(),
        }
    }

    fn is_one(&self) -> Choice {
        self.re.is_one() & self.im.is_zero()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq for BLS24Fp4<PAR, LIMBS> {
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Fp4<PAR, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&#x2074;</i></sub> by rejection sampling.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            re: BLS24Fp2::random(rng),
            im: BLS24Fp2::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&#x2074;</i></sub> by rejection sampling.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> where R: TryRngCore {
        let try_re = match BLS24Fp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;
        let try_im = match BLS24Fp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;
        Ok(Self { re: try_re, im: try_im })
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Fp4<PAR, LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Fp4<PAR, LIMBS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.re -= rhs.re;
        self.im -= rhs.im;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Fp4<PAR, LIMBS> {
    fn zero() -> Self {
        Self {
            re: BLS24Fp2::zero(),
            im: BLS24Fp2::zero(),
        }
    }

    fn is_zero(&self) -> Choice {
        self.re.is_zero() & self.im.is_zero()
    }

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

    /// General BLS24Fp4 test template.
    #[allow(non_snake_case)]
    fn BLS24Fp4_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BLS24-{:03}Fp4 test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BLS24Fp4::zero());
        assert!(bool::from(BLS24Fp4::<PAR, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BLS24Fp4::one());
        assert!(bool::from(BLS24Fp4::<PAR, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e4: BLS24Fp4<PAR, LIMBS> = BLS24Fp4::random(&mut rng);
            //println!("e4 = {}", e4);
            //println!("e4 + 0 = {}", e4 + BLS24Fp4::zero());
            assert_eq!(e4 + BLS24Fp4::zero(), e4);
            //println!("e4*1 = {}", e4*BLS24Fp4::one());
            assert_eq!(e4*BLS24Fp4::one(), e4);
            let e2: BLS24Fp2<PAR, LIMBS> = BLS24Fp2::random(&mut rng);
            assert_eq!(BLS24Fp4::from_Fp2(e2), BLS24Fp4::from(e2, BLS24Fp2::zero()));

            // addition vs subtraction:
            //println!("-e4      = {}", -e4);
            //println!("e4 - e4  = {}", e4 - e4);
            //println!("e4+(-e4) = {}", e4 + (-e4));
            assert!(bool::from((e4 - e4).is_zero()));
            assert!(bool::from((e4 + (-e4)).is_zero()));

            // double and half:
            //println!("2*e4   = {}", e4.double());
            //println!("e4/2   = {}", e4.half());
            assert_eq!(e4.double().half(), e4);
            assert_eq!(e4.half().double(), e4);
            assert_eq!(e4.double()*e4.half(), e4.sq());

            // square and cube:
            //println!("e4^2       = {}", e4.sq());
            //println!("e4^2 = e4*e4 ? {}", e4.sq() == e4*e4);
            assert_eq!(e4.sq(), e4*e4);
            //println!("e4^3       = {}", e4.cb());
            //println!("e4^3 = e4*e4*e4 ? {}", e4.cb() == e4*e4*e4);
            assert_eq!(e4.cb(), e4*e4*e4);

            // norm and conjugates:
            //println!("|e4| = {}", e4.norm());
            //println!("|e4| = e4*e4.conj() ? {}", bool::from((e4*e4.conj()).re.ct_eq(&e4.norm()) & (e4*e4.conj()).im.is_zero()));
            //println!("e4.conj(1) = {}", e4.conj(1));
            //println!("e4.conj(2) = {}", e4.conj(2));
            //println!("e4.conj(3) = {}", e4.conj(3));
            assert!(bool::from((e4*e4.conj()).re.ct_eq(&e4.norm()) & (e4*e4.conj()).im.is_zero()));
            assert_eq!(e4.frob().frob(), e4.conj());
            assert_eq!(e4.frob().conj(), e4.conj().frob());
            assert_eq!(e4.conj().conj(), e4);
            let e5 = BLS24Fp4::random(&mut rng);
            //println!("e5 = {}", e5);
            //println!("|e5| = {}", e5.norm());
            //println!("|e4*e5| = |e4|*|e5| ? {}", (e4*e5).norm() == e4.norm()*e5.norm());
            assert_eq!((e4*e5).norm(), e4.norm()*e5.norm());
            assert_eq!((e4*e5).frob(), e4.frob()*e5.frob());
            assert_eq!((e4*e5).conj(), e4.conj()*e5.conj());


            // field inversion:
            //println!("e4^-1 = {}", e4.inv());
            //println!("e4*e4^-1 = {}", e4*e4.inv());
            assert!(bool::from((e4*e4.inv()).is_one()));

            // square roots:
            let sr4 = e4.sqrt();
            if bool::from(!sr4.is_zero() | e2.is_zero()) {
                //println!("sqrt(e4) = {}", sr);
                //println!("sqrt(e4)^2 = e4 ? {}", bool::from(sr.sq().ct_eq(&e4)));
                assert_eq!(sr4.sq(), e4);
            } else {
                //println!("no sqrt");
                assert!(e4.legendre() < 0);
            }
            let e42 = e4.sq();  // guaranteed to be a square
            assert!(e42.legendre() >= 0);
            let sr42 = e42.sqrt();
            assert_eq!(sr42.sq(), e42);
            let e42 = e42.mul_v();  // guaranteed to be a non-square
            assert!(e42.legendre() < 0);
            let sr42 = e42.sqrt();
            assert!(bool::from(sr42.is_zero()));

            // subgroup multiplication (Word*BLS24Fp4, Uint*BLS24Fp4, BLS24Fp*BLS24Fp4, and BLS24Fp2*BLS24Fp4):
            let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
            let k4: Word = rng.next_u64() & 0xF;
            //println!("k4*e4 = {}", k4*e4);
            //println!("k4*e4 ? {}", BLS24Fp::from_word(k4)*e4);
            assert_eq!(k4*e4, BLS24Fp::from_word(k4)*e4);
            let u4 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u4 = {}", u4.to_string_radix_vartime(20));
            //println!("u4*e4 = {}", u4*e4);
            assert_eq!(u4*e4, BLS24Fp::from_uint(u4)*e4);
            assert_eq!(u4*e4, BLS24Fp2::from_Fp(BLS24Fp::from_uint(u4))*e4);

            let f4 = BLS24Fp4::random(&mut rng);
            //println!("f4     = {}", f4);
            let g4 = BLS24Fp4::random(&mut rng);
            //println!("g4     = {}", g4);

            // commutativity of addition and multiplication:
            //println!("e4 + f4 = {}", e4 + f4);
            //println!("f4 + e4 = {}", f4 + e4);
            assert_eq!(e4 + f4, f4 + e4);
            assert_eq!(e4*f4, f4*e4);

            // associativity:
            //println!("(e4 + f4) + g4 = {}", (e4 + f4) + g4);
            //println!("e4 + (f4 + g4) = {}", e4 + (f4 + g4));
            assert_eq!((e4 + f4) + g4, e4 + (f4 + g4));
            //println!("(e4*f4)*g4 = {}", (e4*f4)*g4);
            //println!("e4*(f4*g4) = {}", e4*(f4*g4));
            assert_eq!((e4*f4)*g4, e4*(f4*g4));
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
    fn BLS24317Fp4_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Fp4_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Fp4_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Fp4_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Fp4_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Fp4_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Fp4_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Fp4_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Fp4_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Fp4_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Fp4_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Fp4_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Fp4_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Fp4_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Fp4_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Fp4_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Fp4_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Fp4_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Fp4_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Fp4_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Fp4_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Fp4_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Fp4_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Fp4_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Fp4_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Fp4_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Fp4_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Fp4_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Fp4_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Fp4_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Fp4_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Fp4_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Fp4_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Fp4_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Fp4_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Fp4_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Fp4_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Fp4_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Fp4_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Fp4_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Fp4_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Fp4_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Fp4_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Fp4_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Fp4_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Fp4_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Fp4_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Fp4_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Fp4_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Fp4_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Fp4_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Fp4_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Fp4_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Fp4_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Fp4_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Fp4_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Fp4_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Fp4_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Fp4_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Fp4_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Fp4_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Fp4_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Fp4_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Fp4_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Fp4_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Fp4_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Fp4_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Fp4_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Fp4_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Fp4_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Fp4_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Fp4_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Fp4_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Fp4_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Fp4_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Fp4_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Fp4_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Fp4_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Fp4_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Fp4_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Fp4_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Fp4_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Fp4_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Fp4_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Fp4_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Fp4_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Fp4_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Fp4_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Fp4_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Fp4_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Fp4_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Fp4_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Fp4_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Fp4_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Fp4_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Fp4_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Fp4_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Fp4_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Fp4_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Fp4_test::<BLS24639Param, LIMBS>();
    }

}
