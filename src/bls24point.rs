#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24fp::BLS24Fp;
use crate::bls24param::BLS24Param;
use crate::bls24zr::BLS24Zr;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Random, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The group <b>G&#x2081;</b> &#x2254; <i>E</i>&lbrack;<i>r</i>&rbrack;(<b>F</b><sub><i>p</i></sub>)
/// of <b>F</b><sub><i>p</i></sub>-rational <i>r</i>-torsion points on the curve <i>E</i>/<b>F</b><sub><i>p</i></sub>.
pub struct BLS24Point<PAR: BLS24Param, const LIMBS: usize> {
    pub(crate) x: BLS24Fp<PAR, LIMBS>,
    pub(crate) y: BLS24Fp<PAR, LIMBS>,
    pub(crate) z: BLS24Fp<PAR, LIMBS>,
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Point<PAR, LIMBS> {

    /// Create a normalized point on a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// from a given affine <i>x</i>-coordinate and the least significant bit (LSB) of the <i>y</i>-coordinate.
    ///
    /// NB: specify y_lsb as Choice::FALSE if LSB==0 and as Choice::TRUE if LSB==1.
    #[inline]
    pub(crate) fn new(x: BLS24Fp<PAR, LIMBS>, y_lsb: Choice) -> Self {
        let y2 = x.cb() + BLS24Fp::from_word(PAR::CURVE_B);
        let mut y = y2.sqrt();
        assert_eq!(y.sq(), y2);
        y = BLS24Fp::conditional_select(&y, &(-y), y.is_odd() ^ y_lsb);
        Self { x, y, z: BLS24Fp::one() }
    }

    /// Determine if a given field element <i>x</i> &in; <b>F</b><sub><i>p</i></sub>
    /// corresponds to the affine abscissa of some point on a BLS24 curve.
    #[inline]
    pub fn is_abscissa(x: BLS24Fp<PAR, { LIMBS }>) -> Choice {
        // affine curve equation: y^2 = x^3 + b
        let qc = (x.cb() + BLS24Fp::from_word(PAR::CURVE_B)).legendre();
        qc.ct_eq(&0) | qc.ct_eq(&1)  // RHS quadratic character >= 0
    }

    /// Determine if given projective coordinates <i>X</i>, <i>Y</i>, and <i>Z</i>
    /// specify a point on a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    #[inline]
    pub fn is_point(x: BLS24Fp<PAR, LIMBS>, y: BLS24Fp<PAR, LIMBS>, z: BLS24Fp<PAR, LIMBS>) -> Choice {
        // projective curve equation: Y^2*Z = X^3 + b*Z^3
        (y.sq()*z).ct_eq(&(x.cb() + BLS24Fp::from_word(PAR::CURVE_B)*z.cb()))
    }

    /// Create a normalized point on a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// from given affine coordinates <i>x</i> and <i>y</i>.
    #[inline]
    fn from_affine(x: BLS24Fp<PAR, LIMBS>, y: BLS24Fp<PAR, LIMBS>) -> Self {
        assert!(bool::from(Self::is_point(x, y, BLS24Fp::one())));
        Self { x, y, z: BLS24Fp::one() }
    }

    /// Create a point on a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// from given projective coordinates <i>X</i>, <i>Y</i>, and <i>Z</i>.
    #[inline]
    pub(crate) fn from_proj(x: BLS24Fp<PAR, LIMBS>, y: BLS24Fp<PAR, LIMBS>, z: BLS24Fp<PAR, LIMBS>) -> Self {
        // projective curve equation: Y^2*Z = X^3 + b*Z^3
        assert!(bool::from(Self::is_point(x, y, z)));
        Self { x, y, z }
    }

    /// Hash input data into a point on the (base field) <i>r</i>-torsion group
    /// <i><b>G</b>&#x2081;</i> &#x2254; <i>E</i>&lbrack;<i>r</i>&rbrack;(<b>F</b><sub><i>p</i></sub>)
    /// of a BLS24 curve <i>E</i>/<b>F</b><sub><i>p</i></sub>:
    /// <i>Y&sup2;Z</i> = <i>X&sup3;</i> + <i>bZ&sup3;</i> with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        Self::point_factory(BLS24Fp::shake128(data)).elim_cof()
    }

    /// Hash input data into a point on the (base field) <i>r</i>-torsion group
    /// <i><b>G</b>&#x2081;</i> &#x2254; <i>E</i>&lbrack;<i>r</i>&rbrack;(<b>F</b><sub><i>p</i></sub>)
    /// of a BLS24 curve <i>E</i>/<b>F</b><sub><i>p</i></sub>:
    /// <i>Y&sup2;Z</i> = <i>X&sup3;</i> + <i>bZ&sup3;</i> with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        Self::point_factory(BLS24Fp::shake256(data)).elim_cof()
    }

    /// Compute a normalized (i.e. affine) point equivalent to this
    /// on a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    #[inline]
    pub(crate) fn normalize(&self) -> Self {
        let ch = self.z.is_zero();
        let inv = BLS24Fp::conditional_select(&self.z, &self.y, ch).inv();
        Self {
            x: self.x*inv,
            y: self.y*inv,
            z: BLS24Fp::conditional_select(&BLS24Fp::one(), &BLS24Fp::zero(), ch),
        }
    }

    /// Compute <i>&lbrack;2&#x1D57;&rbrack;P</i> for a BLS24 curve point
    /// <i>P &in; E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// (i.e. double <i>t</i> times) via complete elliptic point doubling.
    #[inline]
    pub fn double(&self, t: usize) -> Self {
        let mut d = self.clone();
        d.double_self(t);
        d
    }

    /// Compute <i>&lbrack;2&#x1D57;&rbrack;P</i> for a BLS24 curve point
    /// <i>P &in; E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// (i.e. double <i>t</i> times) via complete elliptic point doubling.
    ///
    /// Reference:
    ///
    /// *; Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 9), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    #[inline]
    pub(crate) fn double_self(&mut self, t: usize) {
        let mut x = self.x;
        let mut y = self.y;
        let mut z = self.z;

        let mut t0: BLS24Fp<PAR, LIMBS>;
        let mut t1: BLS24Fp<PAR, LIMBS>;
        let mut t2: BLS24Fp<PAR, LIMBS>;
        let mut x3: BLS24Fp<PAR, LIMBS>;
        let mut y3: BLS24Fp<PAR, LIMBS>;
        let mut z3: BLS24Fp<PAR, LIMBS>;
        let b3 = 3*PAR::CURVE_B;

        for _ in 0..t {
            t0 = y.sq();
            z3 = t0+t0;
            z3 = z3+z3;

            z3 = z3+z3;
            t1 = y*z;
            t2 = z*z;

            t2 = b3*t2;
            x3 = t2*z3;
            y3 = t0+t2;

            z3 = t1*z3;
            t1 = t2+t2;
            t2 = t1+t2;

            t0 = t0-t2;
            y3 = t0*y3;
            y3 = x3+y3;

            t1 = x*y;
            x3 = t0*t1;
            x3 = x3+x3;

            x = x3;
            y = y3;
            z = z3;
        }
        self.x = x;
        self.y = y;
        self.z = z;
    }

    /// Map a field element <i>t &in; <b>F</b><sub>p</sub></i> to a point on this BLS24 curve
    /// using the isochronous Shallue-van de Woestijne method.
    ///
    /// Reference:
    ///
    /// *; Andrew Shallue, Christiaan E. van de Woestijne:
    /// "Construction of rational points on elliptic curves over finite fields."
    /// In: Hess, F., Pauli, S., Pohst, M. E. (eds.), <i>Algorithmic Number Theory -- ANTS-VII</i>,
    /// Lecture Notes in Computer Science, vol. 4076, pp. 510--524, 2006.
    /// Springer, Berlin Heidelberg, 2006.
    /// https://doi.org/10.1007/11792086_36
    #[inline]
    pub fn point_factory(t: BLS24Fp<PAR, LIMBS>) -> BLS24Point<PAR, LIMBS> {
        let one = BLS24Fp::one();
        let b = BLS24Fp::from_word(PAR::CURVE_B);
        let sqrt_m3 = BLS24Fp::from_words(PAR::SQRT_NEG_3.try_into().unwrap());
        let num = sqrt_m3*t;  // sqrt(-3)*t
        let den = one + b + t.sq();  // 1 + b + t^2
        // Montgomery's trick to use a single inversion, (num*den)^-1, to compute
        // the inverse of num = den*(num*den)^-1 and the inverse of den = num*(num*den)^-1:
        let monty = (num*den).inv();

        let w = num.sq()*monty;  // sqrt(-3)*t/(1 + b + t^2)
        let inv_w = den.sq()*monty;
        let svdw = BLS24Fp::from_words(PAR::SVDW.try_into().unwrap());  // (-1 + sqrt(-3))/2

        // candidate x-coordinates:
        let x0 = svdw - t*w;  // (-1 + sqrt(-3))/2 - t*w
        let x1 = -(one + x0); // -1 - x_0
        let x2 = one + inv_w.sq(); // 1 + 1/w^2

        // quadratic characters of the corresponding curve equation RHS:
        let q0 = (x0.cb() + b).legendre();  // legendre((x0^3 + b), p)
        assert_ne!(q0, 0);  // no point of order 2 exists on any supported BLS24 curve (-b is not a cube in Fp)
        let q1 = (x1.cb() + b).legendre();  // legendre((x1^3 + b), p)
        assert_ne!(q1, 0);  // no point of order 2 exists on any supported BLS24 curve (-b is not a cube in Fp)

        // constant-time sequential search for the proper choice of x:
        let mut xc = x2;
        xc = BLS24Fp::conditional_select(&xc, &x1, q1.ct_eq(&1));
        xc = BLS24Fp::conditional_select(&xc, &x0, q0.ct_eq(&1));
        let leg = t.legendre();

        // point construction:
        BLS24Point::new(xc, leg.ct_ne(&0) & leg.ct_ne(&1))
    }

    /// Compute &lbrack;<i>u</i>&rbrack;<i>`self`</i>.
    #[allow(non_snake_case)]
    #[inline]
    fn mul_u(&self) -> Self {
        // since the coefficient u is public and fixed, the simple double-and-add method suffices:
        let mut u = PAR::UD;
        let mut m = 0;
        let mut P = self.clone();
        let mut V = Self::zero();
        for _ in 0..8 {
            let k = u & 0xFF; u >>= 8; // extract term degree
            if k >= 128 {
                P = P.double((256 - k - m) as usize); m = 256 - k;
                V -= P;
            } else if k > 0 {
                P = P.double((k - m) as usize); m = k;
                V += P;
            } else {
                break;
            }
        }
        V
    }

    /// Eliminate the cofactor from `self`, yielding a point of <i>n</i>-torsion
    /// <i>P'</i> &in; <b>G</b><i>&#x2081;</i> &#x2254;
    /// <i>E</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p</i></sub>).
    ///
    /// This operation does <i>not</i> involve multiplication by the full cofactor
    /// <i>c</i> &#x2254; (<i>u</i> - 1)<i>&sup2;</i>/3, but by the much less expensive
    /// sub-cofactor <i>c'</i> &#x2254; <i>u</i> - 1, since the whole (2-dimensional)
    /// <i>c'</i>-torsion is contained in <b>G</b><i>&#x2081;</i>.
    /// This clever technique was first noticed by Mike Scott (personal communication, 2019).
    #[allow(non_snake_case)]
    #[inline]
    pub fn elim_cof(&self) -> Self {
        let P = *self;
        P.mul_u() - P  // [u-1]P
    }

    /// Convert `self` to byte array representation.
    /// This is the ANSI X9.62 Point-to-Octet-String Conversion primitive, compressed form.
    #[allow(non_snake_case)]
    #[inline]
    pub fn to_bytes(&self) -> Vec<u8> {
        let N = self.normalize();
        // ANSI X9.62 'compressed' prefix: 0x02 | lsb(N.y)
        let mut cp = 0x2u8;  // lsb(N.y) == 0
        cp.conditional_assign(&0x3u8, N.y.is_odd());  // lsb(N.y) == 1
        let mut bytes = Vec::new();
        bytes.push(cp);
        let mut next = N.x.to_bytes(); bytes.append(&mut next);
        bytes
    }

}

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Point<PAR, LIMBS> {
    type Output = Self;

    /// Complete elliptic point addition
    /// for a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference: Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 7), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    fn add(self, other: Self) -> Self::Output {
        let mut point = self;
        point += other;
        point
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Point<PAR, LIMBS> {

    /// Complete elliptic point addition
    /// for a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference: Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 7), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    fn add_assign(&mut self, pair: Self) {
        let x1 = self.x;
        let y1 = self.y;
        let z1 = self.z;
        let x2 = pair.x;
        let y2 = pair.y;
        let z2 = pair.z;

        let mut t0: BLS24Fp<PAR, LIMBS>;
        let mut t1: BLS24Fp<PAR, LIMBS>;
        let mut t2: BLS24Fp<PAR, LIMBS>;
        let mut t3: BLS24Fp<PAR, LIMBS>;
        let mut t4: BLS24Fp<PAR, LIMBS>;
        let mut x3: BLS24Fp<PAR, LIMBS>;
        let mut y3: BLS24Fp<PAR, LIMBS>;
        let mut z3: BLS24Fp<PAR, LIMBS>;

        t0 = x1*x2;
        t1 = y1*y2;
        t2 = z1*z2;

        t3 = x1 + y1;
        t4 = x2 + y2;
        t3 = t3*t4;

        t4 = t0 + t1;
        t3 = t3 - t4;
        t4 = y1 + z1;

        x3 = y2 + z2;
        t4 = t4*x3;
        x3 = t1 + t2;

        t4 = t4 - x3;
        x3 = x1 + z1;
        y3 = x2 + z2;

        x3 = x3*y3;
        y3 = t0 + t2;
        y3 = x3 - y3;

        x3 = t0 + t0;
        t0 = x3 + t0;
        t2 = (3*PAR::CURVE_B)*t2;

        z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = (3*PAR::CURVE_B)*y3;

        x3 = t4*y3;
        t2 = t3*t1;
        x3 = t2 - x3;

        y3 = y3*t0;
        t1 = t1*z3;
        y3 = t1 + y3;

        t0 = t0*t3;
        z3 = z3*t4;
        z3 = z3 + t0;

        self.x = x3;
        self.y = y3;
        self.z = z3;
    }

}

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Point<PAR, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Point<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Point<PAR, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let x = BLS24Fp::conditional_select(&a.x, &b.x, choice);
        let y = BLS24Fp::conditional_select(&a.y, &b.y, choice);
        let z = BLS24Fp::conditional_select(&a.z, &b.z, choice);
        Self { x, y, z }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Point<PAR, LIMBS> {
    fn ct_eq(&self, pair: &Self) -> Choice {
        // x/z = pair.x/pair.z <=> x*pair.z = pair.x*z
        // y/z = pair.y/pair.z <=> y*pair.z = pair.y*z
        (self.x*pair.z).ct_eq(&(pair.x*self.z)) &
            (self.y*pair.z).ct_eq(&(pair.y*self.z))
    }

    fn ct_ne(&self, pair: &Self) -> Choice {
        // x/z != pair.x/pair.z <=> x*pair.z != pair.x*z
        // y/z != pair.y/pair.z <=> y*pair.z != pair.y*z
        (self.x*pair.z).ct_ne(&(pair.x*self.z)) |
            (self.y*pair.z).ct_ne(&(pair.y*self.z))
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Point<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Point<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let normal = self.normalize();
        /*
        // signed format:
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let half_p= p.shr(1);
        let x = if normal.x.to_uint() <= half_p {
            normal.x.to_string()
        } else {
            "-".to_string() + (-normal.x).to_string().as_str()
        };
        let y = if normal.y.to_uint() <= half_p {
            normal.y.to_string()
        } else {
            "-".to_string() + (-normal.y).to_string().as_str()
        };
        let z = if normal.z.to_uint() <= half_p {
            normal.z.to_string()
        } else {
            "-".to_string() + (-normal.z).to_string().as_str()
        };
        // */
        //*
        let x = normal.x.to_string();
        let y = normal.y.to_string();
        let z = normal.z.to_string();
        // */
        write!(f, "[{} : {} : {}]", x, y, z)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Point<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Point<PAR, LIMBS>;

    fn mul(self, point: BLS24Point<PAR, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self;
        v
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Point<PAR, LIMBS>> for BLS24Zr<PAR, LIMBS> {
    type Output = BLS24Point<PAR, LIMBS>;

    fn mul(self, point: BLS24Point<PAR, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self.to_uint();
        v
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign<Uint<LIMBS>> for BLS24Point<PAR, LIMBS> {

    /// Multiply a scalar (mod n) and a point via fixed-window multiplication.
    ///
    /// Reference:
    ///
    /// *; Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone,
    /// <a href="https://cacr.uwaterloo.ca/hac/">"Handbook of Applied Cryptography"</a>,
    /// CRC Press (1997), section 14.6 (Exponentiation), algorithm 14.82.
    fn mul_assign(&mut self, scalar: Uint<LIMBS>) {
        // prepare a table such that t[d] = d*P, where 0 <= d < 16:
        let mut t = [Self::zero(); 16];
        t[1] = self.clone();
        for d in 1..8 {
            t[2*d] = t[d].double(1);  // (2*d)*P = 2*(d*P)
            t[2*d + 1] = t[2*d].clone() + *self;  // (2*d + 1)*P = 2*(d*P) + P
        }

        // perform fixed-window multiplication by scalar, one hex digit at a time:
        let mut v = Self::zero();  // accumulator
        let s = scalar.as_words();  // scalar
        for j in (0..s.len() << 4).rev() {  // scan the scalar from most to least significant nybble
            v.double_self(4);  // multiply the accumulator by 16
            let d = ((s[j >> 4] >> ((j & 0xF) << 2)) & 0xF) as usize;  // hex digit at index k
            // perform constant-time sequential search on t to extract t[d]:
            let mut w = Self::zero();
            for e in 0..16 {  // t[] contains 16 points...
                w = Self::conditional_select(&w, &t[e], e.ct_eq(&d)); // ... (of which only the d-th is to be kept)
            }
            v += w;  // accumulate pt[d] into v
        }
        *self = v
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Point<PAR, LIMBS> {
    type Output = Self;

    /// Compute the opposite of a point on a BLS24 curve.
    fn neg(self) -> Self::Output {
        Self::Output {
            x: self.x,
            y: self.y.neg(),
            z: self.z,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq<Self> for BLS24Point<PAR, LIMBS> {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(&other).into()
    }

    fn ne(&self, other: &Self) -> bool {
        self.ct_ne(&other).into()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Point<PAR, LIMBS> {
    /// Pick a uniform point from the <i>n</i>-torsion of the BLS24 curve
    /// <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self::point_factory(BLS24Fp::random(rng))
    }

    /// Try to pick a uniform point from the <i>n</i>-torsion of the BLS24 curve
    /// <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> where R: TryRngCore {
        match BLS24Fp::try_random(rng) {
            Ok(val) => Ok(Self::point_factory(val)),
            Err(e) => Err(e),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Point<PAR, LIMBS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut point = self;
        point -= other;
        point
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Point<PAR, LIMBS> {
    fn sub_assign(&mut self, pair: Self) {
        self.add_assign(pair.neg())
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Point<PAR, LIMBS> {
    /// Create an instance of the neutral element ("point at infinity") on a BLS24 curve
    /// <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// in projective coordinates, hence <i>&lbrack;0 : 1 : 0&rbrack;</i>.
    fn zero() -> Self {
        Self { x: BLS24Fp::zero(), y: BLS24Fp::one(), z: BLS24Fp::zero() }
    }

    /// Determine if this projective point is the neutral element
    /// on a BLS24 curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    fn is_zero(&self) -> Choice {
        self.z.is_zero()
    }

    fn set_zero(&mut self) {
        self.x.set_zero();  // otherwise the curve equation Y^2*Z = X^3 + b*Z^3 is not satisfied
        self.z.set_zero()
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
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BLS24Point test template.
    #[allow(non_snake_case)]
    fn BLS24Point_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BLS24-{:03}Point test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral element:
        let O1: BLS24Point<PAR, LIMBS> = BLS24Point::zero();
        //println!("O1 = {} is zero ? {}", O1, bool::from(O1.is_zero()));
        assert!(bool::from(O1.is_zero()));

        // default generator, one of (±1, *), (±2, *), (±3, *), (±4, *), then elim_cof:
        let mut x0: BLS24Fp<PAR, LIMBS> = BLS24Fp::zero();
        for w in 1..=4 {
            x0 = BLS24Fp::from_word(w);
            if bool::from(BLS24Point::is_abscissa(x0)) {
                break;
            }
            x0 = -x0;
            if bool::from(BLS24Point::is_abscissa(x0)) {
                break;
            }
        }
        let G0: BLS24Point<PAR, LIMBS> = BLS24Point::new(x0, Choice::from(0));
        //println!("G0 = {}", G0);
        let G1: BLS24Point<PAR, LIMBS> = G0.elim_cof();
        //println!("G1 = {}", G1);
        //println!("[r]G1 = {}", r*G1);
        assert!(bool::from((r*G1).is_zero()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // hashing to G_1:
            let P1: BLS24Point<PAR, LIMBS> = BLS24Point::point_factory(BLS24Fp::random(&mut rng)).elim_cof();
            //println!("P1 = {}", P1);
            let P2: BLS24Point<PAR, LIMBS> = BLS24Point::point_factory(BLS24Fp::random(&mut rng)).elim_cof();
            //println!("P2 = {}", P2);
            let P3: BLS24Point<PAR, LIMBS> = BLS24Point::point_factory(BLS24Fp::random(&mut rng)).elim_cof();
            //println!("P3 = {}", P3);

            // point construction:
            assert_eq!(P1, BLS24Point::from_proj(P1.x, P1.y, P1.z));
            let P1N = P1.normalize();
            assert_eq!(P1, BLS24Point::from_affine(P1N.x, P1N.y));
            assert_eq!(P2, BLS24Point::from_proj(P2.x, P2.y, P2.z));
            let P2N = P2.normalize();
            assert_eq!(P2, BLS24Point::from_affine(P2N.x, P2N.y));
            assert_eq!(P3, BLS24Point::from_proj(P3.x, P3.y, P3.z));
            let P3N = P3.normalize();
            assert_eq!(P3, BLS24Point::from_affine(P3N.x, P3N.y));

            // point order:
            //println!("[n]P1 = O1 ? {}", bool::from((n*P1).is_zero()));
            assert!(bool::from((r*P1).is_zero()));
            //println!("[n]P2 = O1 ? {}", bool::from((n*P2).is_zero()));
            assert!(bool::from((r*P2).is_zero()));
            //println!("[n]P3 = O1 ? {}", bool::from((n*P3).is_zero()));
            assert!(bool::from((r*P3).is_zero()));

            // opposite point:
            //println!("P1 + (-P1) = O1 ? {}", bool::from((P1 + (-P1)).is_zero()));
            assert!(bool::from((P1 + (-P1)).is_zero()));
            //println!("P2 + (-P2) = O1 ? {}", bool::from((P2 + (-P2)).is_zero()));
            assert!(bool::from((P2 + (-P2)).is_zero()));
            //println!("P3 + (-P3) = O1 ? {}", bool::from((P3 + (-P3)).is_zero()));
            assert!(bool::from((P3 + (-P3)).is_zero()));

            // point doubling:
            //println!("[2]P1 = P1 + P1 ? {}", P1.double(1) == P1 + P1);
            assert_eq!(P1.double(1), P1 + P1);
            //println!("[2]P2 = P2 + P2 ? {}", P2.double(1) == P2 + P2);
            assert_eq!(P2.double(1), P2 + P2);
            //println!("[2]P3 = P3 + P3 ? {}", P3.double(1) == P3 + P3);
            assert_eq!(P3.double(1), P3 + P3);

            // commutativity:
            //println!("P1 + P2 = P2 + P1 ? {}", P1 + P2 == P2 + P1);
            assert_eq!(P1 + P2, P2 + P1);
            //println!("P1 + P3 = P3 + P1 ? {}", P1 + P3 == P3 + P1);
            assert_eq!(P1 + P3, P3 + P1);
            //println!("P2 + P3 = P3 + P2 ? {}", P2 + P3 == P3 + P2);
            assert_eq!(P2 + P3, P3 + P2);

            // associativity:
            //println!("(P1 + P2) + P3 = P1 + (P2 + P3) ? {}", (P1 + P2) + P3 == P1 + (P2 + P3));
            assert_eq!((P1 + P2) + P3, P1 + (P2 + P3));
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
    fn BLS24317Point_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Point_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Point_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Point_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Point_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Point_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Point_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Point_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Point_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Point_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Point_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Point_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Point_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Point_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Point_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Point_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Point_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Point_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Point_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Point_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Point_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Point_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Point_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Point_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Point_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Point_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Point_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Point_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Point_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Point_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Point_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Point_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Point_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Point_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Point_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Point_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Point_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Point_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Point_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Point_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Point_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Point_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Point_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Point_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Point_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Point_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Point_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Point_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Point_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Point_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Point_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Point_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Point_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Point_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Point_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Point_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Point_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Point_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Point_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Point_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Point_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Point_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Point_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Point_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Point_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Point_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Point_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Point_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Point_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Point_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Point_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Point_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Point_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Point_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Point_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Point_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Point_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Point_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Point_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Point_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Point_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Point_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Point_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Point_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Point_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Point_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Point_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Point_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Point_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Point_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Point_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Point_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Point_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Point_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Point_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Point_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Point_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Point_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Point_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Point_test::<BLS24639Param, LIMBS>();
    }

}
