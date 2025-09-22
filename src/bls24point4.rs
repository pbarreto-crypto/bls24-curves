#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24fp::BLS24Fp;
use crate::bls24fp4::BLS24Fp4;
use crate::bls24param::BLS24Param;
use crate::bls24zr::BLS24Zr;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Random, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::TryRngCore;
use rand::Rng;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub struct BLS24Point4<PAR: BLS24Param, const LIMBS: usize> {
    pub(crate) x: BLS24Fp4<PAR, LIMBS>,
    pub(crate) y: BLS24Fp4<PAR, LIMBS>,
    pub(crate) z: BLS24Fp4<PAR, LIMBS>,
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Point4<PAR, LIMBS> {

    /// Create a normalized point on a BLS24 curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// from a given affine <i>X'</i>-coordinate and the least significant bit (LSB) of the <i>Y'</i>-coordinate.
    ///
    /// NB: specify y_lsb as Choice::FALSE if LSB==0 and as Choice::TRUE if LSB==1.
    #[inline]
    pub(crate) fn new(x: BLS24Fp4<PAR, LIMBS>, y_lsb: Choice) -> Self {
        let bt = PAR::CURVE_B*BLS24Fp4::v();
        let y2 = x.cb() + bt;
        let mut y = y2.sqrt();
        assert_eq!(y.sq(), y2);
        y = BLS24Fp4::conditional_select(&y, &(-y), y.is_odd() ^ y_lsb);
        Self { x, y, z: BLS24Fp4::one() }
    }

    /// Determine if a given field element <i>x</i> &in; <b>F</b><sub><i>p&#x2074;</i></sub>
    /// corresponds to the affine abscissa of some point on a BLS24 curve twist.
    #[inline]
    pub fn is_abscissa(x: BLS24Fp4<PAR, LIMBS>) -> Choice {
        // affine curve equation: y'^2 = x'^3 + b'
        let qc = (x.cb() + PAR::CURVE_B*BLS24Fp4::v()).legendre();
        qc.ct_eq(&0) | qc.ct_eq(&1)  // RHS quadratic character >= 0
    }

    /// Determine if given projective coordinates <i>X'</i>, <i>Y'</i>, and <i>Z'</i>
    /// specify a point on a BLS24 curve twist <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    #[inline]
    pub fn is_point(x: BLS24Fp4<PAR, LIMBS>, y: BLS24Fp4<PAR, LIMBS>, z: BLS24Fp4<PAR, LIMBS>) -> Choice {
        // projective curve equation: Y'^2*Z' = X'^3 + b'*Z'^3 where b' = b*v
        (y.sq()*z).ct_eq(&(x.cb() + PAR::CURVE_B*BLS24Fp4::v()*z.cb()))
    }

    /// Create a normalized point on a BLS24 curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// from given affine coordinates <i>X'</i> and <i>Y'</i>.
    #[inline]
    fn from_affine(x: BLS24Fp4<PAR, LIMBS>, y: BLS24Fp4<PAR, LIMBS>) -> Self {
        assert!(bool::from(Self::is_point(x, y, BLS24Fp4::one())));
        Self { x, y, z: BLS24Fp4::one() }
    }

    /// Create a point on a BLS24 curve twist <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// from given projective coordinates <i>X'</i>, <i>Y'</i>, and <i>Z'</i>.
    #[inline]
    pub(crate) fn from_proj(x: BLS24Fp4<PAR, LIMBS>, y: BLS24Fp4<PAR, LIMBS>, z: BLS24Fp4<PAR, LIMBS>) -> Self {
        assert!(bool::from(Self::is_point(x, y, z)));
        Self { x: x.clone(), y: y.clone(), z: z.clone() }
    }

    /// Hash input data into a point on the (quadratic extension field) <i>r</i>-torsion group
    /// <b>G</b><i>&#x2082;</i> &#x2254; <i>E'</i>&lbrack;<i>r</i>&rbrack;(<b>F</b><sub><i>p&#x2074;</i></sub>)
    /// of a BLS24 curve twist <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        Self::point_factory(BLS24Fp4::shake128(data)).elim_cof()
    }

    /// Hash input data into a point on the (quadratic extension field) <i>r</i>-torsion group
    /// <b>G</b><i>&#x2082;</i> &#x2254; <i>E'</i>&lbrack;<i>r</i>&rbrack;(<b>F</b><sub><i>p&#x2074;</i></sub>)
    /// of a BLS24 curve twist <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        Self::point_factory(BLS24Fp4::shake256(data)).elim_cof()
    }

    /// Compute a normalized (i.e. affine) point equivalent to this
    /// on a BLS24 curve twist <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    #[inline]
    pub(crate) fn normalize(&self) -> Self {
        let ch = self.z.is_zero();
        let inv = BLS24Fp4::conditional_select(&self.z, &self.y, ch).inv();
        Self {
            x: self.x*inv,
            y: self.y*inv,
            z: BLS24Fp4::conditional_select(&BLS24Fp4::one(), &BLS24Fp4::zero(), ch),
        }
    }

    /// Compute &lbrack;<i>2&#x1D48;</i>&rbrack;<i>Q&#x1D57;</i> for a BLS24 curve twist point
    /// <i>Q&#x1D57;</i> &in; <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// (i.e. double <i>d</i> times) via complete elliptic point doubling.
    #[inline]
    pub fn double(&self, d: usize) -> Self {
        let mut ds = self.clone();
        ds.double_self(d);
        ds
    }

    /// Compute &lbrack;<i>2&#x1D48;</i>&rbrack;<i>Q&#x1D57;</i> for a BLS24 curve twist point
    /// <i>Q&#x1D57;</i> &in; <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// (i.e. double <i>d</i> times) via complete elliptic point doubling.
    ///
    /// Reference:
    ///
    /// * Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 9), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    #[inline]
    pub(crate) fn double_self(&mut self, d: usize) {
        let mut x = self.x;
        let mut y = self.y;
        let mut z = self.z;

        let mut t0: BLS24Fp4<PAR, LIMBS>;
        let mut t1: BLS24Fp4<PAR, LIMBS>;
        let mut t2: BLS24Fp4<PAR, LIMBS>;
        let mut x3: BLS24Fp4<PAR, LIMBS>;
        let mut y3: BLS24Fp4<PAR, LIMBS>;
        let mut z3: BLS24Fp4<PAR, LIMBS>;
        let b3 = 3*PAR::CURVE_B;

        for _ in 0..d {
            t0 = y.sq();
            z3 = t0+t0;
            z3 = z3+z3;

            z3 = z3+z3;
            t1 = y*z;
            t2 = z*z;

            t2 = b3*t2.mul_v();
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

    /// Map a field element <i>t</i> &in; <b>F</b><sub><i>p&#x2074;</i></sub> to a point on this BLS24 curve twist
    /// using the isochronous Shallue-van de Woestijne method.
    ///
    /// NB: the output point is only guaranteed to be on the curve,
    /// <i>not</i> in the (quadratic extension field) <i>r</i>-torsion group
    /// <b>G</b><i>&#x2082;</i> &#x2254; <i>E'</i>&lbrack;<i>r</i>&rbrack;(<b>F</b><sub><i>p&#x2074;</i></sub>),
    /// that is, cofactor multiplication is not implicitly applied here.
    ///
    /// If a point in <b>G</b><i>&#x2082;</i> is required, either resort to explicit
    /// cofactor multiplication or use method BLS24Point4::shake256(.) instead.
    ///
    /// Reference:
    ///
    /// * Andrew Shallue, Christiaan E. van de Woestijne:
    /// "Construction of rational points on elliptic curves over finite fields."
    /// In: Hess, F., Pauli, S., Pohst, M. E. (eds.), <i>Algorithmic Number Theory -- ANTS-VII</i>,
    /// Lecture Notes in Computer Science, vol. 4076, pp. 510--524, 2006.
    /// Springer, Berlin Heidelberg, 2006.
    /// https://doi.org/10.1007/11792086_36
    #[inline]
    pub fn point_factory(t: BLS24Fp4<PAR, LIMBS>) -> BLS24Point4<PAR, LIMBS> {
        let one = BLS24Fp4::one();
        let bt = PAR::CURVE_B*BLS24Fp4::v();
        let sqrt_m3 = BLS24Fp::from_words(PAR::SQRT_NEG_3.try_into().unwrap());
        let num = sqrt_m3*t;  // sqrt(-3)*t
        let den = one + bt + t.sq();  // 1 + b + t^2
        // Montgomery's trick to use a single inversion, (num*den)^-1, to compute
        // the inverse of num = den*(num*den)^-1 and the inverse of den = num*(num*den)^-1:
        let monty = (num*den).inv();

        let w = num.sq()*monty;  // sqrt(-3)*t/(1 + b + t^2)
        let inv_w = den.sq()*monty;
        let svdw0 = BLS24Fp::from_words(PAR::SVDW.try_into().unwrap());
        let svdw = BLS24Fp4::from_Fp(svdw0);  // (-1 + sqrt(-3))/2

        // candidate x-coordinates:
        let x0 = svdw - t*w;  // (-1 + sqrt(-3))/2 - t*w
        let x1 = -(one + x0); // -1 - x_0
        let x2 = one + inv_w.sq(); // 1 + 1/w^2

        // quadratic characters of the corresponding curve equation RHS:
        let q0 = (x0.cb() + bt).legendre();  // legendre((x0^3 + b'), p)
        let q1 = (x1.cb() + bt).legendre();  // legendre((x1^3 + b'), p)
        let q2 = (x2.cb() + bt).legendre();  // legendre((x2^3 + b'), p)

        // constant-time sequential search for the proper choice of x:
        let mut xc = x2;
        xc = BLS24Fp4::conditional_select(&xc, &x1, q2.ct_ne(&1) & q1.ct_ne(&(-1)));
        xc = BLS24Fp4::conditional_select(&xc, &x0, q0.ct_eq(&1));
        assert!((xc.cb() + bt).legendre() >= 0);
        let leg = t.legendre();

        // point construction:
        BLS24Point4::new(xc, leg.ct_ne(&0) & leg.ct_ne(&1))
    }

    /// Compute the <i>k</i>-th Frobenius endomorphism on the BLS24 curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>,
    /// namely the map <i>&psi;&#x1D4F;</i> : <i>E'</i> &#8594; <i>E'</i> defined as
    /// the composition <i>&psi;&#x1D4F;</i> &#x2254; <i>&phi;&#x207B;&sup1;</i>&nbsp;o&nbsp;<i>&pi;&#x1D4F;</i>&nbsp;o&nbsp;<i>&phi;</i>,
    /// where <i>&phi;</i> : <i>E'</i> &#8594; <i>E</i> is the embedding
    /// <i>&phi;</i>(<i>x'</i>, <i>y'</i>) = (<i>x' v<sup>-&frac13;</sup></i>, <i>y' v<sup>-&half;</sup></i>) and
    /// <i>&pi;</i> : <i>E</i> &#8594; <i>E</i> is the Frobenius endomorphism on <i>E</i>,
    /// <i>&pi;</i>(<i>x</i>, <i>y</i>) &#x2254; (<i>x&#x1D56;</i>, <i>y&#x1D56;</i>), with <i>0&leq;k&lt;24</i>.
    /// NB: <i>v<sup>&frac13;</sup></i> = <i>i&thinsp;z&sup3;</i>, <i>v<sup>&half;</sup></i> = -<i>&zeta;&thinsp;z&sup2;</i>.
    #[inline]
    pub(crate) fn psi(&self, k: usize) -> Self {
        let o1: BLS24Fp<PAR, LIMBS> = BLS24Fp::one();
        let zeta: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::ZETA.try_into().unwrap());
        let theta1: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::THETA1.try_into().unwrap());
        let theta2: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::THETA2.try_into().unwrap());
        let theta3: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::THETA3.try_into().unwrap());
        let c: BLS24Fp<PAR, LIMBS> = BLS24Fp::from_words(PAR::NEG_SQRT_NEG_2.try_into().unwrap()).half();
        assert!(k < 24);
        //     function psi(P', k)
        //         // ψᵏ : E' → E' is the composition ψᵏ ≔ φ⁻¹ o πᵏ o φ
        //         return Et![L3[k % 12]*x^(p^(k mod 4)), L2[k & 7]*yt^(p^(k mod 4))];
        //     end function;
        match k {
            //    1, theta1*xi,    zeta + 1, c*xi,
            //    1, theta3*xi*v, -i,       -theta3*(1 - i)*v,
            0 => Self {
                x: self.x,
                y: self.y,
                z: self.z,
            },
            1 => Self {
                x: theta1*self.x.frob().mul_xi(),
                y: theta3*self.y.frob().mul_xi().mul_v(),
                z: self.z.frob(),
            },
            2 => Self {
                x: (zeta + o1)*self.x.conj(),
                y: -self.y.conj().mul_i(),
                z: self.z.conj(),
            },
            3 => Self {
                x: c*self.x.conj().frob().mul_xi(),
                y: -theta3*self.y.conj().frob().mul_ix().mul_v(),
                z: self.z.conj().frob(),
            },

            //    zeta, theta2*xi,   -1, -theta1*xi,
            //   -1,   -theta3*xi*v,  i,  theta3*(1 - i)*v,
            4 => Self {
                x: zeta*self.x,
                y: -self.y,
                z: self.z,
            },
            5 => Self {
                x: theta2*self.x.frob().mul_xi(),
                y: -theta3*self.y.frob().mul_xi().mul_v(),
                z: self.z.frob(),
            },
            6 => Self {
                x: -self.x.conj(),
                y: self.y.conj().mul_i(),
                z: self.z.conj(),
            },
            7 => Self {
                x: -theta1*self.x.conj().frob().mul_xi(),
                y: theta3*self.y.conj().frob().mul_ix().mul_v(),
                z: self.z.conj().frob(),
            },

            //   -zeta - 1, -c*xi,        -zeta, -theta2*xi,
            //    1,         theta3*xi*v, -i,    -theta3*(1 - i)*v,
            8 => Self {
                x: -(zeta + o1)*self.x,
                y: self.y,
                z: self.z,
            },
            9 => Self {
                x: -c*self.x.frob().mul_xi(),
                y: theta3*self.y.frob().mul_xi().mul_v(),
                z: self.z.frob(),
            },
            10 => Self {
                x: -zeta*self.x.conj(),
                y: -self.y.conj().mul_i(),
                z: self.z.conj(),
            },
            11 => Self {
                x: -theta2*self.x.conj().frob().mul_xi(),
                y: -theta3*self.y.conj().frob().mul_ix().mul_v(),
                z: self.z.conj().frob(),
            },

            //    1,  theta1*xi,   zeta + 1, c*xi,
            //   -1, -theta3*xi*v, i,        theta3*(1 - i)*v,
            12 => Self {
                x: self.x,
                y: -self.y,
                z: self.z,
            },
            13 => Self {
                x: theta1*self.x.frob().mul_xi(),
                y: -theta3*self.y.frob().mul_xi().mul_v(),
                z: self.z.frob(),
            },
            14 => Self {
                x: (zeta + o1)*self.x.conj(),
                y: self.y.conj().mul_i(),
                z: self.z.conj(),
            },
            15 => Self {
                x: c*self.x.conj().frob().mul_xi(),
                y: theta3*self.y.conj().frob().mul_ix().mul_v(),
                z: self.z.conj().frob(),
            },

            //    zeta, theta2*xi,   -1, -theta1*xi,
            //    1,    theta3*xi*v, -i, -theta3*(1 - i)*v,
            16 => Self {
                x: zeta*self.x,
                y: self.y,
                z: self.z,
            },
            17 => Self {
                x: theta2*self.x.frob().mul_xi(),
                y: theta3*self.y.frob().mul_xi().mul_v(),
                z: self.z.frob(),
            },
            18 => Self {
                x: -self.x.conj(),
                y: -self.y.conj().mul_i(),
                z: self.z.conj(),
            },
            19 => Self {
                x: -theta1*self.x.conj().frob().mul_xi(),
                y: -theta3*self.y.conj().frob().mul_ix().mul_v(),
                z: self.z.conj().frob(),
            },

            //   -zeta - 1, -c*xi,        -zeta, -theta2*xi,
            //   -1,        -theta3*xi*v,  i,     theta3*(1 - i)*v,
            20 => Self {
                x: -(zeta + o1)*self.x,
                y: -self.y,
                z: self.z,
            },
            21 => Self {
                x: -c*self.x.frob().mul_xi(),
                y: -theta3*self.y.frob().mul_xi().mul_v(),
                z: self.z.frob(),
            },
            22 => Self {
                x: -zeta*self.x.conj(),
                y: self.y.conj().mul_i(),
                z: self.z.conj(),
            },
            23 => Self {
                x: -theta2*self.x.conj().frob().mul_xi(),
                y: theta3*self.y.conj().frob().mul_ix().mul_v(),
                z: self.z.conj().frob(),
            },

            _ => self.clone(),  // just to make the compiler happy
        }
    }

    /// Compute &lbrack;<i>u</i>&rbrack;<i>`self`</i>.
    #[allow(non_snake_case)]
    #[inline]
    fn mul_u(&self) -> Self {
        // since the scalar factor u is public and fixed, the simple double-and-add method suffices:
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

    /// Compute &lbrack;<i>p</i>&rbrack;<i>`self`</i>.
    ///
    /// This is efficiently carried out as
    /// &lbrack;<i>p</i>&rbrack;<i>`self`</i> = &lbrack;<i>u</i> + 1&rbrack;<i>&psi;</i>(<i>`self`</i>) - <i>&psi;</i>&sup2;(<i>`self`</i>).
    #[allow(non_snake_case)]
    #[inline]
    fn mul_p(&self) -> Self {
        let psiQ = self.psi(1);
        psiQ.mul_u() + psiQ - self.psi(2)
    }

    /// Eliminate the cofactor from `self` &in; <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub>,
    /// yielding a point of <i>n</i>-torsion <i>Q&#x1D57;</i> &in; <b>G</b><i>&#x2082;</i> &#x2254;
    /// <i>E'</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p&#x2074;</i></sub>).
    ///
    /// NB: This operation is carried out through the efficient Frobenius endomorphism,
    /// <i>not</i> by cofactor multiplication, which would be more computationally expensive.
    ///
    /// Specifically, the cofactor for <b>G</b><i>&#x2082;</i> can be efficiently carried out by noticing that
    /// <i>h'</i> &#x2254; ((<i>u</i> - 1)&times;<i>p&sup3;</i>
    ///        + (<i>u&sup2;</i> - <i>u</i>)&times;<i>p&sup2;</i>
    ///        + (<i>u&sup3;</i> - <i>u&sup2;</i> - <i>u </i>+ 1)&times;<i>p</i>
    ///        + (<i>u&#x2079;</i> - <i>u&#x2078;</i> - 2<i>u&#x2077;</i> + 2<i>u</i>&#x2076;</i> + <i>u&#x2075;</i> + 2<i>u&sup2;</i> - <i>u</i> + 1))&times;(<i>u</i> - 1)/3
    ///        - <i>p</i> + 2,
    /// and that multiplication by <i>p</i> is efficiently done as
    /// &lbrack;<i>p</i>&rbrack;<i>Q</i> = &lbrack;<i>u</i> + 1&rbrack;<i>&psi;</i>(<i>Q</i>) - <i>&psi;</i>&sup2;(<i>Q</i>).
    ///
    /// The actual resulting point is &lbrack;3<i>h'</i>&rbrack;<i>Q</i>,
    /// which involves a simpler Frobenius decomposition and still yields a point of <i>r</i>-th torsion
    /// because the extra factor 3 is coprime with <i>r</i>.
    ///
    /// References:
    ///
    /// * Mike Scott, Naomi Benger, Manuel Charlemagne, Luís J. Domínguez-Pérez, Ezekiel J. Kachisa:
    /// "Fast Hashing to <b>G</b><i>&#x2082;</i> on Pairing-Friendly Curves."
    /// In: Shacham, H., Waters, B. (eds.),
    /// <i>Pairing-Based Cryptography -- Pairing 2009</i>.
    /// Lecture Notes in Computer Science, vol. 5671, pp. 102–113.
    /// Springer, Berlin Heidelberg (2009).
    /// https://doi.org/10.1007/978-3-642-03298-1_8
    ///
    /// * Steven D. Galbraith, Mike Scott:
    /// "Exponentiation in Pairing-Friendly Groups Using Homomorphisms."
    /// In: Galbraith, S.D., Paterson, K.G. (eds.),
    /// <i>Pairing-Based Cryptography -- Pairing 2008</i>.
    /// Lecture Notes in Computer Science, vol. 5209, pp. 211--224.
    /// Springer, Berlin Heidelberg (2008).
    /// https://doi.org/10.1007/978-3-540-85538-5_15
    #[allow(non_snake_case)]
    #[inline]
    pub fn elim_cof(&self) -> Self {
        // uQ := u*Q; u2Q := u*uQ; u3Q := u*u2Q;
        // u4Q := u*u3Q; u5Q := u*u4Q; u6Q := u*u5Q;
        // u7Q := u*u6Q; u8Q := u*u7Q; u9Q := u*u8Q;
        // m1Q := mul_p(uQ - Q, 1);
        // m2Q := mul_p(m1Q + u2Q - uQ, 1);
        // m3Q := mul_p(m2Q + u3Q - u2Q - uQ + Q, 1);
        // QQ := m3Q + (u9Q - u8Q - 2*(u7Q - u6Q - u3Q) + u5Q - uQ + Q);
        // RR := 2*Q - mul_p(Q, 1)
        // return u*QQ - QQ + 2*RR + RR;
        let Q = *self;
        let uQ = Q.mul_u();  // [u]Q
        let u2Q = uQ.mul_u();  // [u^2]Q
        let u3Q = u2Q.mul_u();  // [u^3]Q
        let u4Q = u3Q.mul_u();  // [u^4]Q
        let u5Q = u4Q.mul_u();  // [u^5]Q
        let u6Q = u5Q.mul_u();  // [u^6]Q
        let u7Q = u6Q.mul_u();  // [u^7]Q
        let u8Q = u7Q.mul_u();  // [u^8]Q
        let u9Q = u8Q.mul_u();  // [u^9]Q
        let m1Q = (uQ - Q).mul_p();
        let m2Q = (m1Q + u2Q - uQ).mul_p();
        let m3Q = (m2Q + u3Q - u2Q - uQ + Q).mul_p();
        let QQ = m3Q + (u9Q - u8Q - (u7Q - u6Q - u3Q).double(1) + u5Q - uQ + Q);
        let RR = Q.double(1) - Q.mul_p();
        QQ.mul_u() - QQ + RR.double(1) + RR
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

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Point4<PAR, LIMBS> {
    type Output = Self;

    /// Complete elliptic point addition
    /// for a BLS24 curve <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference:
    ///
    /// * Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 7), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    fn add(self, other: Self) -> Self::Output {
        let mut point = self;
        point += other;
        point
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Point4<PAR, LIMBS> {

    /// Complete elliptic point addition
    /// for a BLS24 curve <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference:
    ///
    /// * Joost Renes, Craig Costello, Lejla Batina:
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

        let mut t0: BLS24Fp4<PAR, LIMBS>;
        let mut t1: BLS24Fp4<PAR, LIMBS>;
        let mut t2: BLS24Fp4<PAR, LIMBS>;
        let mut t3: BLS24Fp4<PAR, LIMBS>;
        let mut t4: BLS24Fp4<PAR, LIMBS>;
        let mut x3: BLS24Fp4<PAR, LIMBS>;
        let mut y3: BLS24Fp4<PAR, LIMBS>;
        let mut z3: BLS24Fp4<PAR, LIMBS>;
        let b3 = 3*PAR::CURVE_B;

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
        t2 = b3*t2.mul_v();

        z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = b3*y3.mul_v();

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

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Point4<PAR, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Point4<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Point4<PAR, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let x = BLS24Fp4::conditional_select(&a.x, &b.x, choice);
        let y = BLS24Fp4::conditional_select(&a.y, &b.y, choice);
        let z = BLS24Fp4::conditional_select(&a.z, &b.z, choice);
        Self { x, y, z }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Point4<PAR, LIMBS> {
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

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Point4<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Point4<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let normal = self.normalize();
        write!(f, "[{} : {} : {}]", normal.x, normal.y, normal.z)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Point4<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Point4<PAR, LIMBS>;

    fn mul(self, point: BLS24Point4<PAR, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self;
        v
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Point4<PAR, LIMBS>> for BLS24Zr<PAR, LIMBS> {
    type Output = BLS24Point4<PAR, LIMBS>;

    fn mul(self, point: BLS24Point4<PAR, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self.to_uint();
        v
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign<Uint<LIMBS>> for BLS24Point4<PAR, LIMBS> {

    /// Multiply a scalar (mod <i>n</i>) and a point via fixed-window multiplication.
    ///
    /// Reference:
    ///
    /// * Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone,
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

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Point4<PAR, LIMBS> {
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

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq<Self> for BLS24Point4<PAR, LIMBS> {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(&other).into()
    }

    fn ne(&self, other: &Self) -> bool {
        self.ct_ne(&other).into()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Point4<PAR, LIMBS> {
    /// Pick a uniform point from the <i>n</i>-torsion of the BLS24 curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    fn random<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self::point_factory(BLS24Fp4::random(rng)).elim_cof()
    }

    /// Try to pick a uniform point from the <i>n</i>-torsion of the BLS24 curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&#x2074;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(Self::point_factory(val).elim_cof()),
            Err(e) => Err(e),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Point4<PAR, LIMBS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut point = self;
        point -= other;
        point
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Point4<PAR, LIMBS> {
    fn sub_assign(&mut self, pair: Self) {
        self.add_assign(pair.neg())
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Point4<PAR, LIMBS> {
    /// Create an instance of the neutral element ("point at infinity") on a BLS24 curve
    /// <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>
    /// in projective coordinates, hence &lbrack;<i>0</i> : <i>1</i> : <i>0</i>&rbrack;.
    fn zero() -> Self {
        Self { x: BLS24Fp4::zero(), y: BLS24Fp4::one(), z: BLS24Fp4::zero() }
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
    use crate::bls24fp2::BLS24Fp2;
    use super::*;

    const TESTS: usize = 10;

    /// General BNPoint test template.
    #[allow(non_snake_case)]
    fn BLS24Point4_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let t: Uint<LIMBS> = p + Uint::ONE - r;

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BLS24-{:03}Point4 test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral element:
        let O2: BLS24Point4<PAR, LIMBS> = BLS24Point4::zero();
        //println!("O2 = {} is zero ? {}", O2, bool::from(O2.is_zero()));
        assert!(bool::from(O2.is_zero()));

        // default generator, one of (1, *), (i, *), (2, *), (2*i, *), (1 + i, *), then elim_cof:
        let mut x0: BLS24Fp4<PAR, LIMBS> = BLS24Fp4::zero();
        let mut found = false;
        for w in [BLS24Fp2::one(), BLS24Fp2::from_word_i(1), BLS24Fp2::from_word(2), BLS24Fp2::from_word_i(2), BLS24Fp2::from_word_pair(1, 1)] {
            x0 = BLS24Fp4::from_Fp2(w);
            if bool::from(BLS24Point4::is_abscissa(x0)) {
                //println!("found x_0' = {}", x0);
                found = true;
                break;
            }
        }
        assert!(found);
        let Gt0: BLS24Point4<PAR, LIMBS> = BLS24Point4::new(x0, Choice::from(0));
        //println!("G'_0 = {}", Gt0);
        //println!("[2]G'_0   = {}", Gt0.double(1));
        //println!("G'_0+G'_0 = {}", Gt0 + Gt0);

        //println!("[p]G'_0   = {}", p*Gt0);
        //println!("[p]G'_0   ? {}", Gt0.mul_p());
        assert_eq!(p*Gt0, Gt0.mul_p());

        let Gt = Gt0.elim_cof();
        //println!("G' = {}", Gt);
        //println!("[r]G' = {}", r*Gt);
        assert!(bool::from((r*Gt).is_zero()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // hashing to G_2:
            let Q1: BLS24Point4<PAR, LIMBS> = BLS24Point4::point_factory(BLS24Fp4::random(&mut rng)).elim_cof();
            //println!("Q1 = {}", Q1);
            let Q2: BLS24Point4<PAR, LIMBS> = BLS24Point4::point_factory(BLS24Fp4::random(&mut rng)).elim_cof();
            //println!("Q2 = {}", Q2);
            let Q3: BLS24Point4<PAR, LIMBS> = BLS24Point4::point_factory(BLS24Fp4::random(&mut rng)).elim_cof();
            //println!("Q3 = {}", Q3);

            // point construction:
            assert_eq!(Q1, BLS24Point4::from_proj(Q1.x, Q1.y, Q1.z));
            let P1N = Q1.normalize();
            assert_eq!(Q1, BLS24Point4::from_affine(P1N.x, P1N.y));
            assert_eq!(Q2, BLS24Point4::from_proj(Q2.x, Q2.y, Q2.z));
            let P2N = Q2.normalize();
            assert_eq!(Q2, BLS24Point4::from_affine(P2N.x, P2N.y));
            assert_eq!(Q3, BLS24Point4::from_proj(Q3.x, Q3.y, Q3.z));
            let P3N = Q3.normalize();
            assert_eq!(Q3, BLS24Point4::from_affine(P3N.x, P3N.y));

            // point order:
            //println!("[n]Q1 = O1 ? {}", bool::from((n*Q1).is_zero()));
            assert!(bool::from((r *Q1).is_zero()));
            //println!("[n]Q2 = O1 ? {}", bool::from((n*Q2).is_zero()));
            assert!(bool::from((r *Q2).is_zero()));
            //println!("[n]Q3 = O1 ? {}", bool::from((n*Q3).is_zero()));
            assert!(bool::from((r *Q3).is_zero()));

            // opposite point:
            //println!("Q1 + (-Q1) = O1 ? {}", bool::from((Q1 + (-Q1)).is_zero()));
            assert!(bool::from((Q1 + (-Q1)).is_zero()));
            //println!("Q2 + (-Q2) = O1 ? {}", bool::from((Q2 + (-Q2)).is_zero()));
            assert!(bool::from((Q2 + (-Q2)).is_zero()));
            //println!("Q3 + (-Q3) = O1 ? {}", bool::from((Q3 + (-Q3)).is_zero()));
            assert!(bool::from((Q3 + (-Q3)).is_zero()));

            // point doubling:
            //println!("[2]Q1 = Q1 + Q1 ? {}", Q1.double(1) == Q1 + Q1);
            assert_eq!(Q1.double(1), Q1 + Q1);
            //println!("[2]Q2 = Q2 + Q2 ? {}", Q2.double(1) == Q2 + Q2);
            assert_eq!(Q2.double(1), Q2 + Q2);
            //println!("[2]Q3 = Q3 + Q3 ? {}", Q3.double(1) == Q3 + Q3);
            assert_eq!(Q3.double(1), Q3 + Q3);

            // commutativity:
            //println!("Q1 + Q2 = Q2 + Q1 ? {}", Q1 + Q2 == Q2 + Q1);
            assert_eq!(Q1 + Q2, Q2 + Q1);
            //println!("Q1 + Q3 = Q3 + Q1 ? {}", Q1 + Q3 == Q3 + Q1);
            assert_eq!(Q1 + Q3, Q3 + Q1);
            //println!("Q2 + Q3 = Q3 + Q2 ? {}", Q2 + Q3 == Q3 + Q2);
            assert_eq!(Q2 + Q3, Q3 + Q2);

            // associativity:
            //println!("(Q1 + Q2) + Q3 = Q1 + (Q2 + Q3) ? {}", (Q1 + Q2) + Q3 == Q1 + (Q2 + Q3));
            assert_eq!((Q1 + Q2) + Q3, Q1 + (Q2 + Q3));

            // Frobenius endomorphism:
            //println!("psi^2(Q1) - [t]psi(Q1) + [p]Q1 = {}", Q1.psi(2) - t*Q1.psi(1) + p*Q1);
            assert!(bool::from((Q1.psi(2) - t*Q1.psi(1) + Q1.mul_p()).is_zero()));
            for k in 0..12usize {
                let mut Qpk = Q1;
                for _ in 0..k {
                    Qpk = Qpk.psi(1);
                }
                assert_eq!(Qpk, Q1.psi(k));
            }
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
    fn BLS24317Point4_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Point4_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Point4_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Point4_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Point4_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Point4_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Point4_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Point4_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Point4_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Point4_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Point4_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Point4_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Point4_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Point4_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Point4_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Point4_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Point4_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Point4_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Point4_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Point4_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Point4_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Point4_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Point4_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Point4_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Point4_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Point4_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Point4_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Point4_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Point4_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Point4_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Point4_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Point4_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Point4_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Point4_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Point4_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Point4_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Point4_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Point4_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Point4_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Point4_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Point4_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Point4_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Point4_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Point4_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Point4_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Point4_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Point4_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Point4_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Point4_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Point4_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Point4_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Point4_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Point4_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Point4_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Point4_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Point4_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Point4_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Point4_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Point4_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Point4_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Point4_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Point4_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Point4_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Point4_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Point4_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Point4_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Point4_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Point4_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Point4_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Point4_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Point4_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Point4_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Point4_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Point4_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Point4_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Point4_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Point4_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Point4_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Point4_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Point4_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Point4_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Point4_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Point4_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Point4_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Point4_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Point4_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Point4_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Point4_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Point4_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Point4_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Point4_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Point4_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Point4_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Point4_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Point4_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Point4_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Point4_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Point4_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Point4_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Point4_test::<BLS24639Param, LIMBS>();
    }

}
