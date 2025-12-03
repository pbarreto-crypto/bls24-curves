#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24fp::BLS24Fp;
use crate::bls24fp2::BLS24Fp2;
use crate::bls24fp4::BLS24Fp4;
use crate::bls24param::BLS24Param;
use crate::traits::{BLS24Field, One};
use crypto_bigint::{Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> &simeq;
/// <b>F</b><sub><i>p&#x2074;</i></sub>&lbrack;<i>z</i>&rbrack;/&lt;<i>z&#x2076;</i> + <i>v</i>&gt;
/// extension field.
/// NB: <i>z&#x2076;</i> = -<i>v</i>.
pub struct BLS24Fp24<PAR: BLS24Param, const LIMBS: usize> {
    pub(crate) a0: BLS24Fp4<PAR, LIMBS>,
    pub(crate) a1: BLS24Fp4<PAR, LIMBS>,
    pub(crate) a2: BLS24Fp4<PAR, LIMBS>,
    pub(crate) a3: BLS24Fp4<PAR, LIMBS>,
    pub(crate) a4: BLS24Fp4<PAR, LIMBS>,
    pub(crate) a5: BLS24Fp4<PAR, LIMBS>,
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Fp24<PAR, LIMBS> {
    /// Convert an <b>F</b><sub><i>p&#x2074;</i></sub> element to its <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp4(a0: BLS24Fp4<PAR, LIMBS>) -> Self {
        Self {
            a0,
            a1: BLS24Fp4::zero(),
            a2: BLS24Fp4::zero(),
            a3: BLS24Fp4::zero(),
            a4: BLS24Fp4::zero(),
            a5: BLS24Fp4::zero()
        }
    }

    /// Convert an <b>F</b><sub><i>p&sup2;</i></sub> element to its <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp2(a0: BLS24Fp2<PAR, LIMBS>) -> Self {
        Self {
            a0: BLS24Fp4::from_Fp2(a0),
            a1: BLS24Fp4::zero(),
            a2: BLS24Fp4::zero(),
            a3: BLS24Fp4::zero(),
            a4: BLS24Fp4::zero(),
            a5: BLS24Fp4::zero()
        }
    }

    /// Convert an <b>F</b><sub><i>p</i></sub> element to its <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> counterpart.
    #[allow(non_snake_case)]
    #[inline]
    pub(crate) fn from_Fp(a0: BLS24Fp<PAR, LIMBS>) -> Self {
        Self {
            a0: BLS24Fp4::from_Fp(a0),
            a1: BLS24Fp4::zero(),
            a2: BLS24Fp4::zero(),
            a3: BLS24Fp4::zero(),
            a4: BLS24Fp4::zero(),
            a5: BLS24Fp4::zero()
        }
    }

    /// Assemble an <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> element
    /// from its <b>F</b><sub><i>p&#x2074;</i></sub> components.
    #[inline]
    pub(crate) fn from(a: [BLS24Fp4<PAR, LIMBS>; 6]) -> Self {
        Self {
            a0: a[0],
            a1: a[1],
            a2: a[2],
            a3: a[3],
            a4: a[4],
            a5: a[5],
        }
    }

    /// Apply the Frobenius endomorphism to `self`,
    /// i.e. compute `self`<i>&#x1D56;</i> in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    #[inline]
    pub fn frob(&self) -> Self {
        // x^p =
        //      a[0]^p +
        //      (zeta0*theta3)* a[1]^p *ix *v *z +
        //      -theta2* a[2]^p *ix *z^2 +
        //      -qnr_scale* a[3]^p *i *v *z^3 +
        //      zeta0*a[4]^p *i *z^4 +
        //      (zeta1*theta3)*a[5]^p *xi *v *z^5
        let zeta0 = BLS24Fp::from_words(PAR::ZETA.try_into().unwrap());
        let zeta1 = -(zeta0 + BLS24Fp::one());
        let qnr_scale = BLS24Fp::from_words(PAR::QNR_SCALE.try_into().unwrap());
        let theta2 = BLS24Fp::from_words(PAR::THETA2.try_into().unwrap());
        let theta3 = BLS24Fp::from_words(PAR::THETA3.try_into().unwrap());
        Self {
            a0: self.a0.frob(),
            a1: (zeta0 * theta3) * self.a1.frob().mul_ix().mul_v(),
            a2: -theta2 * self.a2.frob().mul_ix(),
            a3: -qnr_scale * self.a3.frob().mul_i().mul_v(),
            a4: zeta0 * self.a4.frob().mul_i(),
            a5: (zeta1 * theta3) * self.a5.frob().mul_xi().mul_v(),
        }
    }

    /// Compute <i>`self`</i><sup>(<i>p&#x2074;</i>)<i>&#x1D50;</i></sup>,
    /// the <i>m</i>-th conjugate in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> of `self`
    /// over <i><b>F</b><sub>p&#x2074;</sub></i>, <i>0 &leq; m &lt; 6</i>.
    #[inline]
    pub fn conj(&self, m: usize) -> Self {
        /*
         * z^(p^4)  = -zeta*z
         * z^(p^8)  = -(zeta+1)*z
         * z^(p^12) = -z
         * z^(p^16) = zeta*z
         * z^(p^20) = (zeta+1)*z
         *
         * v        = v_0 + v_1*z          + v_2*z^2          + v_3*z^3 + v_4*z^4          + v_5*z^5 =>
         * v^(p^4)  = v_0 - v_1*zeta*z     - v_2*(zeta+1)*z^2 - v_3*z^3 + v_4*zeta*z^4     + v_5*(zeta+1)*z^5
         * v^(p^8)  = v_0 - v_1*(zeta+1)*z + v_2*zeta*z^2     + v_3*z^3 - v_4*(zeta+1)*z^4 + v_5*zeta*z^5
         * v^(p^12) = v_0 - v_1*z          + v_2*z^2          - v_3*z^3 + v_4*z^4          - v_5*z^5
         * v^(p^16) = v_0 + v_1*zeta*z     - v_2*(zeta+1)*z^2 + v_3*z^3 + v_4*zeta*z^4     - v_5*(zeta+1)*z^5
         * v^(p^20) = v_0 + v_1*(zeta+1)*z + v_2*zeta*z^2     - v_3*z^3 - v_4*(zeta+1)*z^4 - v_5*zeta*z^5
         */
        assert!(m < 6);
        let zeta0 = BLS24Fp::from_words(PAR::ZETA.try_into().unwrap());
        let zeta1 = -(zeta0 + BLS24Fp::one());
        // [(z^0)^(p^(4*m)) : m in [0..5]] = [ 1,          1,         1,    1,         1,          1 ];
        // [ z   ^(p^(4*m)) : m in [0..5]] = [ z,   -zeta0*z,   zeta1*z,   -z,   zeta0*z,   -zeta1*z ];
        // [(z^2)^(p^(4*m)) : m in [0..5]] = [ z^2,  zeta1*z^2, zeta0*z^2,  z^2, zeta1*z^2,  zeta0*z^2 ];
        // [(z^3)^(p^(4*m)) : m in [0..5]] = [ z^3,       -z^3,       z^3, -z^3,       z^3,       -z^3 ];
        // [(z^4)^(p^(4*m)) : m in [0..5]] = [ z^4,  zeta0*z^4, zeta1*z^4,  z^4, zeta0*z^4,  zeta1*z^4 ];
        // [(z^5)^(p^(4*m)) : m in [0..5]] = [ z^5, -zeta1*z^5, zeta0*z^5, -z^5, zeta1*z^5, -zeta0*z^5 ];
        let a = match m {
            0 => [self.a0, self.a1, self.a2, self.a3, self.a4, self.a5],
            1 => [self.a0, -zeta0 * self.a1, zeta1 * self.a2, -self.a3, zeta0 * self.a4, -zeta1 * self.a5],
            2 => [self.a0, zeta1 * self.a1, zeta0 * self.a2, self.a3, zeta1 * self.a4, zeta0 * self.a5],
            3 => [self.a0, -self.a1, self.a2, -self.a3, self.a4, -self.a5],
            4 => [self.a0, zeta0 * self.a1, zeta1 * self.a2, self.a3, zeta0 * self.a4, zeta1 * self.a5],
            5 => [self.a0, -zeta1 * self.a1, zeta0 * self.a2, -self.a3, zeta1 * self.a4, -zeta0 * self.a5],
            _ => [self.a0, self.a1, self.a2, self.a3, self.a4, self.a5]  // just to make the compiler happy
        };
        Self {
            a0: a[0],
            a1: a[1],
            a2: a[2],
            a3: a[3],
            a4: a[4],
            a5: a[5],
        }
    }

    /// <b>F</b><sub><i>p&#x2074;</i></sub>-norm of `self` in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    #[inline]
    pub fn norm(&self) -> BLS24Fp4<PAR, LIMBS> {
        /*
        let n12 = *self*self.conj(1)*self.conj(2);
        let n = n12*n12.conj(3);
        // */
        let n = (*self)*self.conj(1)*self.conj(2)*self.conj(3)*self.conj(4)*self.conj(5);
        assert!(bool::from(n.a1.is_zero() & n.a2.is_zero() & n.a3.is_zero() & n.a4.is_zero() & n.a5.is_zero()));
        n.a0
    }

    /// Compute `self`<i>&#x1D4F;</i> in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    #[inline]
    pub fn pow(&self, k: &Uint<LIMBS>) -> Self {
        // prepare a table such that t[d] = v^d, where 0 <= d < 16:
        let mut t = [Self::one(); 16];
        t[1] = self.clone();
        for d in 1..8 {
            t[2 * d] = t[d].sq();  // v^(2*d) = (v^d)^2
            t[2 * d + 1] = t[2 * d].clone() * (*self);  // v^(2*d + 1) = (v^d)^2*v
        }

        // perform fixed-window raising to the exponent, one hex digit at a time:
        let mut v = Self::one();  // accumulator
        let x = k.as_words();  // exponent
        for j in (0..x.len() << 4).rev() {  // scan the exponent from most to least significant nybble
            v = v.sq().sq().sq().sq();  // raise the accumulator to the 16th
            let d = ((x[j >> 4] >> ((j & 0xF) << 2)) & 0xF) as usize;  // hex digit at index k
            // perform constant-time sequential search on t to extract t[d]:
            let mut w = Self::one();
            for e in 0..16 {  // t[] contains 16 serialized points...
                w = Self::conditional_select(&w, &t[e], e.ct_eq(&d)); // ... (of which only the d-th is to be kept)
            }
            v *= w;  // accumulate pt[d] into v
        }
        v
    }

    /// Compute `self`<i>&#x02B3;</i> in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>,
    /// where <i>r</i> = <i>u</i>&#x2078; - <i>u</i>&#x2074; + 1 is the BLS24 curve order over <b>F</b><sub><i>p</i></sub>.
    #[inline]
    pub(crate) fn pow_r(&self) -> Self {
        // this method is local to the crate, and the exponent (restricted to the curve order)
        // is fixed, public, and fairly sparse, hence the square-and-multiply method suffices
        // (isochronous for that exponent, and more efficient than a fixed-window approach):
        assert!(bool::from((*self * self.conj(3)).is_one()));  // hence self^-1 = self.conj(3)
        let spu4 = self.pow_u().pow_u().pow_u().pow_u();  // self^(u^4)
        let spu8 = spu4.pow_u().pow_u().pow_u().pow_u();  // self^(u^8)
        spu8 * spu4.conj(3) * (*self)  // self^(u^8)*self^(-u^4)*self = self^(u^8 - u^4 + 1) = self^r
        /*
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let mut w = Self::one();
        let rbits = r.bits();
        for j in (0..rbits).rev() {
            w = w.sq();
            if bool::from(r.bit(j)) {
                w *= *self;
            }
        }
        w
        // */
    }

    /// Compute <i>`self`&#x1D58;</i> in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>,
    /// where <i>u</i> is the BLS24 curve selector.
    #[inline]
    fn pow_u(&self) -> Self {
        // this method is private, and the exponent (restricted to the BLS24 selector)
        // is fixed, public, and rather sparse, hence the square-and-multiply method suffices:
        // (isochronous for that exponent, and more efficient than a fixed-window approach):
        assert!(bool::from((*self * self.conj(3)).is_one()));  // hence self^-1 = self.conj(3)
        let mut ud = PAR::UD;
        let mut m = 0;
        let mut f = self.clone();
        let mut v = BLS24Fp24::one();
        for _ in 0..8 {
            let k = ud & 0xFF;
            ud >>= 8; // extract term degree
            if k >= 128 {
                for _ in 0..256 - k - m {
                    f = f.sq();
                }
                m = 256 - k;
                v *= f.conj(3);
            } else if k > 0 {
                for _ in 0..k - m {
                    f = f.sq();
                }
                m = k;
                v *= f;
            } else {
                break;
            }
        }
        v
    }

    /// Compute `self`<sup>(<i>p&sup2;&#xFEFF;&#x2074;</i>-1)/<i>r</i></sup> in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    ///
    /// References:
    ///
    /// * Benger, N.: Cryptographic Pairings: Efficiency and DLP Security. PhD thesis,
    /// Dublin City University (May 2010).
    ///
    /// * Craig Costello, Kristin Lauter, Michael Naehrig:
    ///  "Attractive Subfamilies of BLS Curves for Implementing High-Security Pairings."
    ///  In: Bernstein, D.J., Chatterjee, S. (eds) <i>Progress in Cryptology -- INDOCRYPT 2011</i>.
    ///  Lecture Notes in Computer Science, vol 7107, pp. 320--342.
    ///  Springer, Berlin, Heidelberg, 2011. https://doi.org/10.1007/978-3-642-25578-6_23
    #[inline]
    pub(crate) fn final_exp(&self) -> Self {
        // Costello-Lauter-Naehrig, section 5.
        let mut m = self.clone();

        // easy part of final exponentiation: m := m^{(p^12 - 1)*(p^4 + 1)}
        m = m.conj(3)*m.inv();  // m := m^(p^12 - 1)
        m = m.conj(1)*m;  // m := m^(p^4 + 1)
        assert!(bool::from((m*m.conj(3)).is_one()));  // hence m^-1 = m.conj(3)

        // hard part of final exponentiation: m := m^{(p^8 - p^4 + 1)/r}
        // m^{(p^8 − p^4 + 1)/r} = μ0·μ1^p·μ2^(p^2)·μ3^(p^3)·μ4^(p^4)·μ5^(p^5)·μ6^(p^6)·μ7^(p^7)
        let mu8 = m.pow_u();  // μ8 = m^u
        assert!(bool::from((mu8*mu8.conj(3)).is_one()));  // hence m8^-1 = m8.conj(3)
        let mu7 = mu8.pow_u()*mu8.conj(3).sq()*m;  // μ7 = μ8^u · μ8^−2 · m
        let mu6 = mu7.pow_u();  // μ6 = μ7^u
        let mu5 = mu6.pow_u();  // μ5 = μ6^u
        let mu4 = mu5.pow_u();  // μ4 = μ5^u
        assert!(bool::from((mu7*mu7.conj(3)).is_one()));  // hence m7^-1 = m7.conj(3)
        let mu3 = mu4.pow_u()*mu7.conj(3);  // μ3 = μ4^u · μ7^−1
        let mu2 = mu3.pow_u();  // μ2 = μ3^u
        let mu1 = mu2.pow_u();  // μ1 = μ2^u
        let mu0 = mu1.pow_u()*m.sq()*m;  // μ0 = μ1^u · m^2 · m
        m = mu7;
        m = mu6*m.frob();
        m = mu5*m.frob();
        m = mu4*m.frob();
        m = mu3*m.frob();
        m = mu2*m.frob();
        m = mu1*m.frob();
        m = mu0*m.frob();

        m
    }

    /// Multiply `self` by a sparse <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> value
    /// of form <i>w&#8320;</i> + <i>w&#8322;z&sup2;</i> + <i>w&#8323;z&sup3;</i>.
    /// Cost: 13 <b>F</b><sub><i>p&#x2074;</i></sub> multiplications.
    #[inline]
    pub(crate) fn mul_023(&self, rhs0: BLS24Fp4<PAR, LIMBS>, rhs2: BLS24Fp4<PAR, LIMBS>, rhs3: BLS24Fp4<PAR, LIMBS>) -> Self {
        // Karatsuba multiplication:

        let d_00 = self.a0*rhs0;
        let d_22 = self.a2*rhs2;
        let d_33 = self.a3*rhs3;

        let d_01 = (self.a0 + self.a1)*rhs0 - d_00;
        let d_02 = (self.a0 + self.a2)*(rhs0 + rhs2) - d_00 - d_22;
        let d_04 = (self.a0 + self.a4)*rhs0 - d_00;
        let d_13 = (self.a1 + self.a3)*rhs3 - d_33;
        let d_23 = (self.a2 + self.a3)*(rhs2 + rhs3) - d_22 - d_33;
        let d_24 = (self.a2 + self.a4)*rhs2 - d_22;
        let d_35 = (self.a3 + self.a5)*rhs3 - d_33;

        let d_03 = (self.a0 + self.a1 + self.a2 + self.a3)*(rhs0 + rhs2 + rhs3)
            - (d_00 + d_22 + d_33 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.a0 + self.a1 + self.a4 + self.a5)*rhs0
            - (d_00 + d_01 + d_04);
        let d_25 = (self.a2 + self.a3 + self.a4 + self.a5)*(rhs2 + rhs3)
            - (d_22 + d_33 + d_23 + d_24 + d_35);

        Self {
            a0: d_00 - (d_24 + d_33).mul_v(),
            a1: d_01 - d_25.mul_v(),
            a2: d_02 - d_35.mul_v(),
            a3: d_03,
            a4: d_04 + d_13 + d_22,
            a5: d_05 + d_23,
        }
    }

    /// Multiply `self` by a sparse <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> value
    /// of form <i>w&#8320;</i> + <i>w&#8322;z&sup2;</i> + <i>w&#8323;z&sup3;</i>
    /// where <i>w&#8320;</i> &in; {0, 1}.
    /// Cost: 9 <b>F</b><sub><i>p&#x2074;</i></sub> multiplications.
    #[inline]
    pub(crate) fn mul_b23(&self, rhs0: Choice, rhs2: BLS24Fp4<PAR, LIMBS>, rhs3: BLS24Fp4<PAR, LIMBS>) -> Self {
        // Karatsuba multiplication:

        let zero = BLS24Fp4::<PAR, LIMBS>::zero();
        let one = BLS24Fp4::<PAR, LIMBS>::one();
        let d_00 = BLS24Fp4::conditional_select(&zero, &self.a0, rhs0);
        let d_22 = self.a2*rhs2;
        let d_33 = self.a3*rhs3;

        let d_01 = BLS24Fp4::conditional_select(&zero, &(self.a0 + self.a1), rhs0) - d_00;
        let d_02 = (self.a0 + self.a2)*(BLS24Fp4::conditional_select(&zero, &one, rhs0) + rhs2) - d_00 - d_22;
        let d_04 = BLS24Fp4::conditional_select(&zero, &(self.a0 + self.a4), rhs0) - d_00;
        let d_13 = (self.a1 + self.a3)*rhs3 - d_33;
        let d_23 = (self.a2 + self.a3)*(rhs2 + rhs3) - d_22 - d_33;
        let d_24 = (self.a2 + self.a4)*rhs2 - d_22;
        let d_35 = (self.a3 + self.a5)*rhs3 - d_33;

        let d_03 = (self.a0 + self.a1 + self.a2 + self.a3)*(BLS24Fp4::conditional_select(&zero, &one, rhs0) + rhs2 + rhs3)
            - (d_00 + d_22 + d_33 + d_01 + d_02 + d_13 + d_23);
        let d_05 = BLS24Fp4::conditional_select(&zero, &(self.a0 + self.a1 + self.a4 + self.a5), rhs0)
            - (d_00 + d_01 + d_04);
        let d_25 = (self.a2 + self.a3 + self.a4 + self.a5)*(rhs2 + rhs3)
            - (d_22 + d_33 + d_23 + d_24 + d_35);

        Self {
            a0: d_00 - (d_24 + d_33).mul_v(),
            a1: d_01 - d_25.mul_v(),
            a2: d_02 - d_35.mul_v(),
            a3: d_03,
            a4: d_04 + d_13 + d_22,
            a5: d_05 + d_23,
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Add for BLS24Fp24<PAR, LIMBS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val += rhs;
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> AddAssign for BLS24Fp24<PAR, LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.a0 += rhs.a0;
        self.a1 += rhs.a1;
        self.a2 += rhs.a2;
        self.a3 += rhs.a3;
        self.a4 += rhs.a4;
        self.a5 += rhs.a5;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Field for BLS24Fp24<PAR, LIMBS> {
    /// Convert `self` to byte array representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = self.a0.to_bytes();
        let mut next = self.a1.to_bytes(); bytes.append(&mut next);
        let mut next = self.a2.to_bytes(); bytes.append(&mut next);
        let mut next = self.a3.to_bytes(); bytes.append(&mut next);
        let mut next = self.a4.to_bytes(); bytes.append(&mut next);
        let mut next = self.a5.to_bytes(); bytes.append(&mut next);
        bytes
    }

    /// Compute the value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        Self {
            a0: self.a0.double(), a1: self.a1.double(), a2: self.a2.double(),
            a3: self.a3.double(), a4: self.a4.double(), a5: self.a5.double(),
        }
    }

    /// Compute the value of half this element.
    #[inline]
    fn half(&self) -> Self {
        Self {
            a0: self.a0.half(), a1: self.a1.half(), a2: self.a2.half(),
            a3: self.a3.half(), a4: self.a4.half(), a5: self.a5.half(),
        }
    }

    /// Compute the square of this <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> element.
    #[inline]
    fn sq(&self) -> Self {
        // Karatsuba multiplication:

        let d_00 = self.a0.sq();
        let d_11 = self.a1.sq();
        let d_22 = self.a2.sq();
        let d_33 = self.a3.sq();
        let d_44 = self.a4.sq();
        let d_55 = self.a5.sq();

        let d_01 = (self.a0 + self.a1).sq() - d_00 - d_11;
        let d_02 = (self.a0 + self.a2).sq() - d_00 - d_22;
        let d_04 = (self.a0 + self.a4).sq() - d_00 - d_44;
        let d_13 = (self.a1 + self.a3).sq() - d_11 - d_33;
        let d_15 = (self.a1 + self.a5).sq() - d_11 - d_55;
        let d_23 = (self.a2 + self.a3).sq() - d_22 - d_33;
        let d_24 = (self.a2 + self.a4).sq() - d_22 - d_44;
        let d_35 = (self.a3 + self.a5).sq() - d_33 - d_55;
        let d_45 = (self.a4 + self.a5).sq() - d_44 - d_55;

        let s_01 = d_00 + d_11;
        let s_23 = d_22 + d_33;
        let s_45 = d_44 + d_55;
        let d_03 = (self.a0 + self.a1 + self.a2 + self.a3).sq()
            - (s_01 + s_23 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.a0 + self.a1 + self.a4 + self.a5).sq()
            - (s_01 + s_45 + d_01 + d_04 + d_15 + d_45);
        let d_25 = (self.a2 + self.a3 + self.a4 + self.a5).sq()
            - (s_23 + s_45 + d_23 + d_24 + d_35 + d_45);

        Self {
            a0: d_00 - (d_15 + d_24 + d_33).mul_v(),
            a1: d_01 - d_25.mul_v(),
            a2: d_02 + d_11 - (d_35 + d_44).mul_v(),
            a3: d_03 - d_45.mul_v(),
            a4: d_04 + d_13 + d_22 - d_55.mul_v(),
            a5: d_05 + d_23,
        }
    }

    /// Compute the cube of this <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> element.
    #[inline]
    fn cb(&self) -> Self {
        self.sq()*(*self)
    }

    /// Compute the inverse of this <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> element
    /// (or 0, if this element is itself 0).
    #[inline]
    fn inv(&self) -> Self {
        // |a| = a*a.conj(1)*a.conj(2)*(a*a.conj(1)*a.conj(2)).conj(3) = c012*c345
        // :: a^-1 = |a|^-1*a.conj(1)*a.conj(2)*(a*a.conj(1)*a.conj(2)).conj(3) = |a|^-1*c12*c345
        let c12 = self.conj(1)*self.conj(2);  // a.conj(1)*a.conj(2)
        let c012 = *self*c12;  // a*a.conj(1)*a.conj(2)
        let c345 = c012.conj(3);
        let n = c012*c345;
        assert!(bool::from(n.a1.is_zero() & n.a2.is_zero() & n.a3.is_zero() & n.a4.is_zero() & n.a5.is_zero()));
        let norm_inv = n.a0.inv();
        norm_inv*c12*c345
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Clone for BLS24Fp24<PAR, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            a0: self.a0.clone(), a1: self.a1.clone(), a2: self.a2.clone(),
            a3: self.a3.clone(), a4: self.a4.clone(), a5: self.a5.clone(),
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConditionallySelectable for BLS24Fp24<PAR, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let a0 = BLS24Fp4::conditional_select(&a.a0, &b.a0, choice);
        let a1 = BLS24Fp4::conditional_select(&a.a1, &b.a1, choice);
        let a2 = BLS24Fp4::conditional_select(&a.a2, &b.a2, choice);
        let a3 = BLS24Fp4::conditional_select(&a.a3, &b.a3, choice);
        let a4 = BLS24Fp4::conditional_select(&a.a4, &b.a4, choice);
        let a5 = BLS24Fp4::conditional_select(&a.a5, &b.a5, choice);
        Self { a0, a1, a2, a3, a4, a5 }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> ConstantTimeEq for BLS24Fp24<PAR, LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.a0.ct_eq(&other.a0) & self.a1.ct_eq(&other.a1) & self.a2.ct_eq(&other.a2) &
        self.a3.ct_eq(&other.a3) & self.a4.ct_eq(&other.a4) & self.a5.ct_eq(&other.a5)
    }

    fn ct_ne(&self, other: &Self) -> Choice {
        self.a0.ct_ne(&other.a0) | self.a1.ct_ne(&other.a1) | self.a2.ct_ne(&other.a2) |
        self.a3.ct_ne(&other.a3) | self.a4.ct_ne(&other.a4) | self.a5.ct_ne(&other.a5)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Copy for BLS24Fp24<PAR, LIMBS> {}

impl<PAR: BLS24Param, const LIMBS: usize> Debug for BLS24Fp24<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Display for BLS24Fp24<PAR, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.a1.is_zero() &
                      self.a2.is_zero() &
                      self.a3.is_zero() &
                      self.a4.is_zero() &
                      self.a5.is_zero()) {
            // element in F_{p^2}:
            write!(f, "{}", self.a0)
        } else if bool::from(self.a1.is_zero() & self.a2.is_zero() &
                                    self.a4.is_zero() & self.a5.is_zero()) {
            // element in F_{p^4}:
            write!(f, "({}) + ({})*z^3", self.a0, self.a3)
        } else if bool::from(self.a1.is_zero() & self.a3.is_zero() & self.a5.is_zero()) {
            // element in F_{p^6}:
            write!(f, "({}) + ({})*z^2 + ({})*z^4",
                   self.a0, self.a2, self.a4)
        } else {
            write!(f, "({}) + ({})*z + ({})*z^2 + ({})*z^3 + ({})*z^4 + ({})*z^5",
                   self.a0, self.a1, self.a2, self.a3, self.a4, self.a5)
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul for BLS24Fp24<PAR, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp24<PAR, LIMBS>> for Word {
    type Output = BLS24Fp24<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp24<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            a0: self*rhs.a0, a1: self*rhs.a1, a2: self*rhs.a2,
            a3: self*rhs.a3, a4: self*rhs.a4, a5: self*rhs.a5
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp24<PAR, LIMBS>> for Uint<LIMBS> {
    type Output = BLS24Fp24<PAR, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp24<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            a0: self*rhs.a0, a1: self*rhs.a1, a2: self*rhs.a2,
            a3: self*rhs.a3, a4: self*rhs.a4, a5: self*rhs.a5
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp24<PAR, LIMBS>> for BLS24Fp<PAR, LIMBS> {
    type Output = BLS24Fp24<PAR, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp24<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            a0: self*rhs.a0, a1: self*rhs.a1, a2: self*rhs.a2,
            a3: self*rhs.a3, a4: self*rhs.a4, a5: self*rhs.a5
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp24<PAR, LIMBS>> for BLS24Fp2<PAR, LIMBS> {
    type Output = BLS24Fp24<PAR, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p&sup2;</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp24<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            a0: self*rhs.a0, a1: self*rhs.a1, a2: self*rhs.a2,
            a3: self*rhs.a3, a4: self*rhs.a4, a5: self*rhs.a5
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Mul<BLS24Fp24<PAR, LIMBS>> for BLS24Fp4<PAR, LIMBS> {
    type Output = BLS24Fp24<PAR, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p&#x2074;</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub>.
    fn mul(self, rhs: BLS24Fp24<PAR, LIMBS>) -> Self::Output {
        Self::Output {
            a0: self*rhs.a0, a1: self*rhs.a1, a2: self*rhs.a2,
            a3: self*rhs.a3, a4: self*rhs.a4, a5: self*rhs.a5
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> MulAssign for BLS24Fp24<PAR, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        // Karatsuba multiplication:

        let d_00 = self.a0*rhs.a0;
        let d_11 = self.a1*rhs.a1;
        let d_22 = self.a2*rhs.a2;
        let d_33 = self.a3*rhs.a3;
        let d_44 = self.a4*rhs.a4;
        let d_55 = self.a5*rhs.a5;

        let d_01 = (self.a0 + self.a1)*(rhs.a0 + rhs.a1) - d_00 - d_11;
        let d_02 = (self.a0 + self.a2)*(rhs.a0 + rhs.a2) - d_00 - d_22;
        let d_04 = (self.a0 + self.a4)*(rhs.a0 + rhs.a4) - d_00 - d_44;
        let d_13 = (self.a1 + self.a3)*(rhs.a1 + rhs.a3) - d_11 - d_33;
        let d_15 = (self.a1 + self.a5)*(rhs.a1 + rhs.a5) - d_11 - d_55;
        let d_23 = (self.a2 + self.a3)*(rhs.a2 + rhs.a3) - d_22 - d_33;
        let d_24 = (self.a2 + self.a4)*(rhs.a2 + rhs.a4) - d_22 - d_44;
        let d_35 = (self.a3 + self.a5)*(rhs.a3 + rhs.a5) - d_33 - d_55;
        let d_45 = (self.a4 + self.a5)*(rhs.a4 + rhs.a5) - d_44 - d_55;

        let d_03 = (self.a0 + self.a1 + self.a2 + self.a3)*(rhs.a0 + rhs.a1 + rhs.a2 + rhs.a3)
            - (d_00 + d_11 + d_22 + d_33 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.a0 + self.a1 + self.a4 + self.a5)*(rhs.a0 + rhs.a1 + rhs.a4 + rhs.a5)
            - (d_00 + d_11 + d_44 + d_55 + d_01 + d_04 + d_15 + d_45);
        let d_25 = (self.a2 + self.a3 + self.a4 + self.a5)*(rhs.a2 + rhs.a3 + rhs.a4 + rhs.a5)
            - (d_22 + d_33 + d_44 + d_55 + d_23 + d_24 + d_35 + d_45);

        self.a0 = d_00 - (d_15 + d_24 + d_33).mul_v();
        self.a1 = d_01 - d_25.mul_v();
        self.a2 = d_02 + d_11 - (d_35 + d_44).mul_v();
        self.a3 = d_03 - d_45.mul_v();
        self.a4 = d_04 + d_13 + d_22 - d_55.mul_v();
        self.a5 = d_05 + d_23;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Neg for BLS24Fp24<PAR, LIMBS> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Output {
            a0: -self.a0, a1: -self.a1, a2: -self.a2,
            a3: -self.a3, a4: -self.a4, a5: -self.a5
        }
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> One for BLS24Fp24<PAR, LIMBS> {
    #[inline]
    fn one() -> Self {
        Self {
            a0: BLS24Fp4::one(),  a1: BLS24Fp4::zero(), a2: BLS24Fp4::zero(),
            a3: BLS24Fp4::zero(), a4: BLS24Fp4::zero(), a5: BLS24Fp4::zero()
        }
    }

    fn is_one(&self) -> Choice {
        self.a0.is_one() &
        self.a1.is_zero() &
        self.a2.is_zero() &
        self.a3.is_zero() &
        self.a4.is_zero() &
        self.a5.is_zero()
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> PartialEq for BLS24Fp24<PAR, LIMBS> {
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<PAR: BLS24Param, const LIMBS: usize> Random for BLS24Fp24<PAR, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> by rejection sampling.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            a0: BLS24Fp4::random(rng),
            a1: BLS24Fp4::random(rng),
            a2: BLS24Fp4::random(rng),
            a3: BLS24Fp4::random(rng),
            a4: BLS24Fp4::random(rng),
            a5: BLS24Fp4::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&sup2;&#xFEFF;&#x2074;</i></sub> by rejection sampling.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> where R: TryRngCore {
        let try_a0 = match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_a1 = match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_a2 = match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_a3 = match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_a4 = match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_a5 = match BLS24Fp4::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        Ok(Self { a0: try_a0, a1: try_a1, a2: try_a2, a3: try_a3, a4: try_a4, a5: try_a5 })
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Sub for BLS24Fp24<PAR, LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val -= rhs;
        val
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> SubAssign for BLS24Fp24<PAR, LIMBS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.a0 -= rhs.a0;
        self.a1 -= rhs.a1;
        self.a2 -= rhs.a2;
        self.a3 -= rhs.a3;
        self.a4 -= rhs.a4;
        self.a5 -= rhs.a5;
    }
}

impl<PAR: BLS24Param, const LIMBS: usize> Zero for BLS24Fp24<PAR, LIMBS> {
    fn zero() -> Self {
        Self {
            a0: BLS24Fp4::zero(), a1: BLS24Fp4::zero(), a2: BLS24Fp4::zero(),
            a3: BLS24Fp4::zero(), a4: BLS24Fp4::zero(), a5: BLS24Fp4::zero()
        }
    }

    fn is_zero(&self) -> Choice {
        self.a0.is_zero() & self.a1.is_zero() & self.a2.is_zero() &
        self.a3.is_zero() & self.a4.is_zero() & self.a5.is_zero()
    }

    fn set_zero(&mut self) {
        self.a0.set_zero();
        self.a1.set_zero();
        self.a2.set_zero();
        self.a3.set_zero();
        self.a4.set_zero();
        self.a5.set_zero();
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
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BLS24Fp24 test template.
    #[allow(non_snake_case)]
    fn BLS24Fp24_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BLS24{:03}Fp24 test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BLS24Fp24::zero());
        assert!(bool::from(BLS24Fp24::<PAR, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BLS24Fp24::one());
        assert!(bool::from(BLS24Fp24::<PAR, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e24: BLS24Fp24<PAR, LIMBS> = BLS24Fp24::random(&mut rng);
            //println!("e24 = {}", e24);
            //println!("e24 + 0 = {}", e24 + BLS24Fp24::zero());
            assert_eq!(e24 + BLS24Fp24::zero(), e24);
            //println!("e24*1 = {}", e24*BLS24Fp24::one());
            assert_eq!(e24*BLS24Fp24::one(), e24);
            let e4: BLS24Fp4<PAR, LIMBS> = BLS24Fp4::random(&mut rng);
            assert_eq!(BLS24Fp24::from_Fp4(e4), BLS24Fp24::from([e4, BLS24Fp4::zero(), BLS24Fp4::zero(), BLS24Fp4::zero(), BLS24Fp4::zero(), BLS24Fp4::zero()]));

            // addition vs subtraction:
            //println!("-e24      = {}", -e24);
            //println!("e24 - e24  = {}", e24 - e24);
            //println!("e24+(-e24) = {}", e24 + (-e24));
            assert!(bool::from((e24 - e24).is_zero()));
            assert!(bool::from((e24 + (-e24)).is_zero()));

            // double and half:
            //println!("2*e24   = {}", e24.double());
            //println!("e24/2   = {}", e24.half());
            assert_eq!(e24.double().half(), e24);
            assert_eq!(e24.half().double(), e24);
            assert_eq!(e24.double()*e24.half(), e24.sq());

            // square and cube:
            //println!("e24^2       = {}", e24.sq());
            //println!("e24^2 = e24*e24 ? {}", e24.sq() == e24*e24);
            assert_eq!(e24.sq(), e24*e24);
            //println!("e24^3       = {}", e24.cb());
            //println!("e24^3 = e24*e24*e24 ? {}", e24.cb() == e24*e24*e24);
            assert_eq!(e24.cb(), e24*e24*e24);

            // field inversion:
            //println!("e24 = {}", e24);
            //println!("e24^-1 = {};", e24.inv());
            //println!("e24*e24^-1 = {}", e24*e24.inv());
            assert!(bool::from((e24*e24.inv()).is_one()));

            // subring multiplication (Word*BLS24Fp24, Uint*BLS24Fp24, BLS24Fp*BLS24Fp24, BLS24Fp2*BLS24Fp24, BLS24Fp4*BLS24Fp24):
            let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
            let k24: Word = rng.next_u64() & 0xF;
            //println!("k24*e24 = {}", k24*e24);
            //println!("k24*e24 ? {}", BLS24Fp::from_word(k24)*e24);
            assert_eq!(k24*e24, BLS24Fp::from_word(k24)*e24);
            let u24 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u24 = {}", u24.to_string_radix_vartime(20));
            //println!("u24*e24 = {}", u24*e24);
            assert_eq!(u24*e24, BLS24Fp::from_uint(u24)*e24);
            assert_eq!(u24*e24, BLS24Fp2::from_Fp(BLS24Fp::from_uint(u24))*e24);

            // norm homomorphism:
            //println!("|e24|_4 = {}", e24.norm4());
            let e25: BLS24Fp24<PAR, LIMBS> = BLS24Fp24::random(&mut rng);
            //println!("e25 = {}", e13);
            //println!("|e25|_4 = {}", e25.norm4());
            //println!("|e24*e25| = |e24|*|e25| ? {}", (e24*e25).norm() == e24.norm()*e25.norm());
            assert_eq!((e24*e25).norm(), e24.norm()*e25.norm());

            let f24 = BLS24Fp24::random(&mut rng);
            //println!("f24     = {}", f24);
            let g24 = BLS24Fp24::random(&mut rng);
            //println!("g24     = {}", g24);

            // commutativity of addition and multiplication:
            //println!("e24 + f24 = {}", e24 + f24);
            //println!("f24 + e24 = {}", f24 + e24);
            assert_eq!(e24 + f24, f24 + e24);
            assert_eq!(e24*f24, f24*e24);

            // associativity:
            //println!("(e24 + f24) + g24 = {}", (e24 + f24) + g24);
            //println!("e24 + (f24 + g24) = {}", e24 + (f24 + g24));
            assert_eq!((e24 + f24) + g24, e24 + (f24 + g24));
            //println!("(e24*f24)*g24 = {}", (e24*f24)*g24);
            //println!("e24*(f24*g24) = {}", e24*(f24*g24));
            assert_eq!((e24*f24)*g24, e24*(f24*g24));

            // final exponentiation:
            let h24 = e24.final_exp();
            //assert_eq!(h24.inv(), h24.conj(3));
            //println!("e24        = {}", e24);
            //println!("e24^fx     = {}", h24);
            let fx = h24.pow_r();
            //println!("finexp: {}", fx);
            assert!(bool::from(fx.is_one()));
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
    fn BLS24317Fp24_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Fp24_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Fp24_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Fp24_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Fp24_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Fp24_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Fp24_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Fp24_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Fp24_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Fp24_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Fp24_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Fp24_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Fp24_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Fp24_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Fp24_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Fp24_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Fp24_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Fp24_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Fp24_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Fp24_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Fp24_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Fp24_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Fp24_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Fp24_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Fp24_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Fp24_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Fp24_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Fp24_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Fp24_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Fp24_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Fp24_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Fp24_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Fp24_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Fp24_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Fp24_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Fp24_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Fp24_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Fp24_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Fp24_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Fp24_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Fp24_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Fp24_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Fp24_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Fp24_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Fp24_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Fp24_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Fp24_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Fp24_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Fp24_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Fp24_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Fp24_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Fp24_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Fp24_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Fp24_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Fp24_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Fp24_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Fp24_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Fp24_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Fp24_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Fp24_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Fp24_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Fp24_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Fp24_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Fp24_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Fp24_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Fp24_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Fp24_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Fp24_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Fp24_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Fp24_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Fp24_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Fp24_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Fp24_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Fp24_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Fp24_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Fp24_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Fp24_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Fp24_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Fp24_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Fp24_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Fp24_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Fp24_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Fp24_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Fp24_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Fp24_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Fp24_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Fp24_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Fp24_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Fp24_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Fp24_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Fp24_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Fp24_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Fp24_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Fp24_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Fp24_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Fp24_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Fp24_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Fp24_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Fp24_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Fp24_test::<BLS24639Param, LIMBS>();
    }

}
