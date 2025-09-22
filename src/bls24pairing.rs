#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bls24fp2::BLS24Fp2;
use crate::bls24fp4::BLS24Fp4;
use crate::bls24fp24::BLS24Fp24;
use crate::bls24param::BLS24Param;
use crate::bls24point::BLS24Point;
use crate::bls24point4::BLS24Point4;
use crate::traits::{BLS24Field, One};
use crypto_bigint::subtle::{ConditionallySelectable};
use crypto_bigint::Zero;
use std::marker::PhantomData;

#[allow(non_snake_case)]
pub struct BLS24Pairing<PAR: BLS24Param, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<PAR>,
);

impl<PAR: BLS24Param, const LIMBS: usize> BLS24Pairing<PAR, LIMBS> {

    /// The (optimal) Ate pairing for BLS24 curves: <i>a&#x1D64;</i>(<i>Q&#x1D57;</i>,&thinsp;<i>P</i>)&nbsp;&#x2254;
    /// <i>f</i><sub><i>u</i>,<i>Q&#x1D57;</i></sub></i>(<i>&phi;&#x207B;&sup1;</i>(<i>P</i>))<sup>(<i>p&#x1D4F;</i>&thinsp;-&thinsp;1)/<i>r</i></sup>,
    /// where <i>&phi;&#x207B;&sup1;</i> : <i>E</i> &rarr; <i>E'</i> is the untwisting isomorphism
    /// <i>&phi;&#x207B;&sup1;</i>(<i>x</i>, <i>y</i>)&nbsp;&#x21A6; (-<i>x&thinsp;z&sup2;</i>, <i>y&thinsp;i&thinsp;z&sup3;</i>).
    ///
    /// References:
    ///
    /// * Hess, F., Smart, N., Vercauteren, F.:
    /// "The Eta pairing revisited." IACR Cryptology ePrint Archive,
    /// Report 2006/110, (2006) http://eprint.iacr.org/2006/110
    ///
    /// * Craig Costello, Kristin Lauter, Michael Naehrig:
    /// "Attractive Subfamilies of BLS Curves for Implementing High-Security Pairings."
    /// In: Bernstein, D.J., Chatterjee, S. (eds) <i>Progress in Cryptology -- INDOCRYPT 2011</i>.
    /// Lecture Notes in Computer Science, vol 7107, pp. 320--342.
    /// Springer, Berlin, Heidelberg, 2011. https://doi.org/10.1007/978-3-642-25578-6_23
    #[allow(non_snake_case)]
    #[inline]
    pub fn ate(Qt: &BLS24Point4<PAR, LIMBS>, P: &BLS24Point<PAR, LIMBS>) -> BLS24Fp24<PAR, LIMBS> {
        //println!("Qt = {}", Qt);
        //println!("P  = {}", P);

        let mut X1 = Qt.x;
        let mut Y1 = Qt.y;
        let mut Z1 = Qt.z;
        let X2 = Qt.x;
        let Y2 = Qt.y;
        let Z2 = Qt.z;
        let PN = P.normalize();
        // xP := -P[1]*z^2; yP := P[2]*i*z^3;
        let xP = -PN.x;
        let yP = BLS24Fp2::from_Fp_i(PN.y);
        let c1 = -xP*Z2;
        let c2 = yP*Z2;

        let mut f = BLS24Fp24::<PAR, LIMBS>::one();
        let ud = PAR::UD;
        let mut s = 0;  // index of most significant degree
        while ((ud >> (s + 8)) & 0xFF) != 0 {
            s += 8;
        }
        let mut m = (ud >> s) & 0xFF;  // most significant degree
        while s >= 0 {
            s -= 8;
            let k = if s >= 0 { (ud >> s) & 0xFF } else { 0 };  // next degree
            let d = (if m >= 128 { 256 - m } else { m }) - (if k >= 128 { 256 - k } else { k });
            // double d times:
            for _ in 0..d {
                // Ut, g_dbl := dbl(Ut, P);  f := f^2*g_dbl;
                let A = X1.sq();
                let B = Y1.sq();
                let C = Z1.sq();
                let D = 3*PAR::CURVE_B*C.mul_v();  // 3*b*v*C
                let F = (X1 + Y1).sq() - A - B;
                let G = (Y1 + Z1).sq() - B - C;
                let H = 3*D;
                X1 = F*(B - H);
                Y1 = (B + H).sq() - 12*D.sq();
                Z1 = 4*B*G;
                // xP := -P[1]*z^2; yP := P[2]*i*z^3;
                let L_00 = D - B;
                let L_10 = 3*A;
                let L_01 = -G;
                // g_dbl := L_00 + L_10*xP + L_01*yP;
                // f := f^2*g_dbl;
                f = f.sq().mul_023(L_00, xP*L_10, yP*L_01);
            }
            if s >= 0 {
                // add/subtract:
                // Ut, g_addsub := addsub(Ut, Qt, P, k ge 128);  f := f*g_addsub;
                let pmY2 = if k >= 128 { -Y2 } else { Y2 };
                let mut T1 = Z1*X2;
                let mut X3 = X1*Z2;
                T1 = X3 - T1;
                let mut T2 = Z1*pmY2;
                let mut Y3 = Y1*Z2;
                T2 = Y3 - T2;
                let L_00 = X2*T2 - T1*pmY2;
                let L_10 = T2*c1;
                let L_01 = T1*c2;
                // g_add := L_00 + L_10*z^2 + L_01*z^3;
                // f := f*g_addsub;
                f = f.mul_023(L_00, L_10, L_01);
                let mut Z3 = Z1*Z2;
                let mut T3 = T1.sq();
                T3 = T3;
                X3 = T3*X3;
                T3 = T1*T3;
                let mut T4 = T2.sq();
                T4 = T4*Z3;
                T4 = T3 + T4;
                T4 = T4 - X3;
                T4 = T4 - X3;
                X3 = X3 - T4;
                T2 = T2*X3;
                Y3 = T3*Y3;
                Y3 = T2 - Y3;
                X3 = T1*T4;
                Z3 = Z3*T3;
                X1 = X3;
                Y1 = Y3;
                Z1 = Z3;

                m = k;
            }
        }
        f = BLS24Fp24::conditional_select(&f, &BLS24Fp24::one(), f.is_zero());
        f = f.final_exp();  // f = f^((p^24 - 1)/r)
        assert!(bool::from(f.pow_r().is_one()));
        f
    }

    /// Create a list `Qt_triples` of triples of <b>F</b><sub><i>p&#x2074;</i></sub> elements from
    /// a point `Qt` &in; <b>G</b><i>&#x2082;</i>, to be used later by BLS24Pairing::eval(.)
    /// when `Qt` is involved in several ate pairing computations with different
    /// arguments <i>P&#x2C7C;</i> from group <b>G</b><i>&#x2081;</i>.
    ///
    /// Example:
    ///
    /// &nbsp;&nbsp;&nbsp;&nbsp;let Qt_triples = BLS24Pairing::precomp(&Qt);<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_1 = BLS24Pairing::eval(&Qt_triples, &P_1);  // <i>g&#x2081;</i> = <i>a&#x1D64;</i>(<i>Q&#x1D57;</i>, <i>P&#x2081;</i>)<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;// ...<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_m = BLS24Pairing::eval(&Qt_triples, &P_m);  // <i>g&#x2098;</i> = <i>a&#x1D64;</i>(<i>Q&#x1D57;</i>, <i>P&#x2098;</i>)<br>
    #[allow(non_snake_case)]
    #[inline]
    pub fn precomp(Qt: &BLS24Point4<PAR, LIMBS>) -> Vec<BLS24Fp4<PAR, LIMBS>> {
        let mut Qt_triples = Vec::<BLS24Fp4<PAR, LIMBS>>::with_capacity(3*PAR::TRIPLES as usize);
        let mut X1 = Qt.x;
        let mut Y1 = Qt.y;
        let mut Z1 = Qt.z;
        let X2 = Qt.x;
        let Y2 = Qt.y;
        let Z2 = Qt.z;

        let ud = PAR::UD;
        let mut s = 0;  // index of most significant degree
        while ((ud >> (s + 8)) & 0xFF) != 0 {
            s += 8;
        }
        let mut m = (ud >> s) & 0xFF;  // most significant degree
        while s >= 0 {
            s -= 8;
            let k = if s >= 0 { (ud >> s) & 0xFF } else { 0 };  // next degree
            let d = (if m >= 128 { 256 - m } else { m }) - (if k >= 128 { 256 - k } else { k });
            // double d times:
            for _ in 0..d {
                // Ut, g_dbl := dbl(Ut, P);  f := f^2*g_dbl;
                let A = X1.sq();
                let B = Y1.sq();
                let C = Z1.sq();
                let D = 3*PAR::CURVE_B*C.mul_v();  // 3*b*v*C
                let F = (X1 + Y1).sq() - A - B;
                let G = (Y1 + Z1).sq() - B - C;
                let H = 3*D;
                X1 = F*(B - H);
                Y1 = (B + H).sq() - 12*D.sq();
                Z1 = 4*B*G;
                // xP := -P[1]*z^2; yP := P[2]*i*z^3;
                let L_00 = D - B;
                let L_10 = -(3*A);
                let L_01 = -G.mul_i();
                // g_dbl := L_00 + L_10*xP + L_01*yP;
                // f := f^2*g_dbl;
                //f = f.sq().mul_023(L_00, PN.x*L_10, PN.y*L_01);
                Qt_triples.push(L_00);
                Qt_triples.push(L_10);
                Qt_triples.push(L_01);
            }
            if s >= 0 {
                // add/subtract:
                // Ut, g_addsub := addsub(Ut, Qt, P, k ge 128);  f := f*g_addsub;
                let pmY2 = if k >= 128 { -Y2 } else { Y2 };
                let mut T1 = Z1*X2;
                let mut X3 = X1*Z2;
                T1 = X3 - T1;
                let mut T2 = Z1*pmY2;
                let mut Y3 = Y1*Z2;
                T2 = Y3 - T2;
                let L_00 = X2*T2 - T1*pmY2;
                let L_10 = T2*Z2;
                let L_01 = T1*Z2.mul_i();
                // g_add := L_00 + L_10*z^2 + L_01*z^3;
                // f := f*g_addsub;
                //f = f.mul_023(L_00, PN.x*L_10, PN.y*L_01);
                Qt_triples.push(L_00);
                Qt_triples.push(L_10);
                Qt_triples.push(L_01);

                let mut Z3 = Z1*Z2;
                let mut T3 = T1.sq();
                T3 = T3;
                X3 = T3*X3;
                T3 = T1*T3;
                let mut T4 = T2.sq();
                T4 = T4*Z3;
                T4 = T3 + T4;
                T4 = T4 - X3;
                T4 = T4 - X3;
                X3 = X3 - T4;
                T2 = T2*X3;
                Y3 = T3*Y3;
                Y3 = T2 - Y3;
                X3 = T1*T4;
                Z3 = Z3*T3;
                X1 = X3;
                Y1 = Y3;
                Z1 = Z3;

                m = k;
            }
        }
        assert_eq!(Qt_triples.len(), 3*PAR::TRIPLES as usize);
        Qt_triples
    }

    /// Evaluate an ate pairing in expedited fashion, from a point `P` &in; <b>G</b><i>&#x2081;</i>
    /// and a list of precomputed `Qt_triples` of <b>F</b><sub><i>p&sup2;</i></sub> elements previously
    /// computed with BLS24Pairing::precomp(.) from a common point <i>Q&#x1D57;</i> &in; <b>G</b><i>&#x2082;</i>.
    ///
    /// Example:
    ///
    /// &nbsp;&nbsp;&nbsp;&nbsp;let Qt_triples = BLS24Pairing::precomp(&Qt);<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_1 = BLS24Pairing::eval(&Qt_triples, &P_1);  // <i>g&#x2081;</i> = <i>a&#x1D64;</i>(<i>Q&#x1D57;</i>, <i>P&#x2081;</i>)<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;// ...<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_m = BLS24Pairing::eval(&Qt_triples, &P_m);  // <i>g&#x2098;</i> = <i>a&#x1D64;</i>(<i>Q&#x1D57;</i>, <i>P&#x2098;</i>)<br>
    #[allow(non_snake_case)]
    #[inline]
    pub fn eval(Q_triples: &Vec<BLS24Fp4<PAR, LIMBS>>, P: &BLS24Point<PAR, LIMBS>) -> BLS24Fp24<PAR, LIMBS> {
        assert_eq!(Q_triples.len(), 3*PAR::TRIPLES as usize);
        let PN = P.normalize();
        let mut pre = 0;  // individual precomputed value
        let mut f = BLS24Fp24::<PAR, LIMBS>::one();
        let ud = PAR::UD;
        let mut s = 0;  // index of most significant degree
        while ((ud >> (s + 8)) & 0xFF) != 0 {
            s += 8;
        }
        let mut m = (ud >> s) & 0xFF;  // most significant degree
        while s >= 0 {
            s -= 8;
            let k = if s >= 0 { (ud >> s) & 0xFF } else { 0 };  // next degree
            let d = (if m >= 128 { 256 - m } else { m }) - (if k >= 128 { 256 - k } else { k });
            // double d times:
            for _ in 0..d {
                let L_00 = Q_triples[pre]; pre += 1;
                let L_10 = Q_triples[pre]; pre += 1;
                let L_01 = Q_triples[pre]; pre += 1;
                // g_dbl := L_00 + L_10*xP + L_01*yP;
                // f := f^2*g_dbl;
                f = f.sq().mul_023(L_00, PN.x*L_10, PN.y*L_01);
            }
            if s >= 0 {
                // add/subtract:
                let L_00 = Q_triples[pre]; pre += 1;
                let L_10 = Q_triples[pre]; pre += 1;
                let L_01 = Q_triples[pre]; pre += 1;
                // g_add := L_00 + L_10*z^2 + L_01*z^3;
                // f := f*g_addsub;
                f = f.mul_023(L_00, PN.x*L_10, PN.y*L_01);
                m = k;
            }
        }
        assert_eq!(pre, 3*PAR::TRIPLES as usize);
        f = BLS24Fp24::conditional_select(&f, &BLS24Fp24::one(), f.is_zero());
        f = f.final_exp();  // f = f^((p^24 - 1)/r)
        assert!(bool::from(f.pow_r().is_one()));
        f
    }
}


#[cfg(test)]
mod tests {
    use crate::bls24fp::BLS24Fp;
    use crate::bls24param::{BLS24317Param, BLS24324Param, BLS24329Param, BLS24339Param, BLS24341Param, BLS24342Param, BLS24343Param, BLS24347Param, BLS24348Param, BLS24349Param, BLS24358Param, BLS24362Param, BLS24365Param, BLS24379Param, BLS24380Param, BLS24407Param, BLS24409Param, BLS24429Param, BLS24449Param, BLS24454Param, BLS24459Param, BLS24469Param, BLS24470Param, BLS24471Param, BLS24472Param, BLS24477Param, BLS24481Param, BLS24485Param, BLS24489Param, BLS24507Param, BLS24519Param, BLS24520Param, BLS24529Param, BLS24539Param, BLS24549Param, BLS24559Param, BLS24569Param, BLS24571Param, BLS24587Param, BLS24589Param, BLS24600Param, BLS24605Param, BLS24609Param, BLS24617Param, BLS24619Param, BLS24623Param, BLS24627Param, BLS24629Param, BLS24631Param, BLS24639Param};
    use crypto_bigint::{Random, Uint};
    use crypto_bigint::subtle::Choice;
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 10;

    /// General BLS24Pairing test template.
    #[allow(non_snake_case)]
    fn BLS24Pairing_test<PAR: BLS24Param, const LIMBS: usize>() {
        let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
        let r: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BLS24-{:03}Pairing test(s)...", TESTS, p.bits());
        let now = SystemTime::now();

        // default generator for group G_1: one of (±1, *), (±2, *), (±3, *), (±4, *), then elim_cof:
        let O1: BLS24Point<PAR, LIMBS> = BLS24Point::zero();
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
        assert!(bool::from(!G1.is_zero() & (r*G1).is_zero()));

        // default generator for group G_2: one of (1, *), (i, *), (2, *), (2*i, *), (1 + i, *), then elim_cof:
        let O2: BLS24Point4<PAR, LIMBS> = BLS24Point4::zero();
        let mut xt0: BLS24Fp4<PAR, LIMBS> = BLS24Fp4::zero();
        let mut found = false;
        for w in [BLS24Fp2::one(), BLS24Fp2::from_word_i(1), BLS24Fp2::from_word(2), BLS24Fp2::from_word_i(2), BLS24Fp2::from_word_pair(1, 1)] {
            xt0 = BLS24Fp4::from_Fp2(w);
            if bool::from(BLS24Point4::is_abscissa(xt0)) {
                //println!("found x_0' = {}", xt0);
                found = true;
                break;
            }
        }
        assert!(found);
        let Gt0: BLS24Point4<PAR, LIMBS> = BLS24Point4::new(xt0, Choice::from(0));
        //println!("G'_0 = {}", Gt0);
        let G2 = Gt0.elim_cof();
        //println!("G' = {}", G2);
        //println!("[r]G' = {}", r*G2);
        assert!(bool::from(!G2.is_zero() & (r*G2).is_zero()));

        // default generators and infinity:
        let g1 = BLS24Pairing::ate(&G2, &O1);
        //println!("**** a(G2, O1) = {}", g1);
        assert!(bool::from(g1.is_one()));
        let g2 = BLS24Pairing::ate(&O2, &G1);
        //println!("**** a(O2, G1) = {}", g2);
        assert!(bool::from(g2.is_one()));
        let g0 = BLS24Pairing::ate(&G2, &G1);
        //println!("**** a(G2, G1) = {}", g0);
        //println!("**** a(G2, G1)^r = {}", g0.pow_r());
        assert!(bool::from(!g0.is_one() & g0.pow_r().is_one()));
        for _t in 0..TESTS {
            let k = Uint::random(&mut rng);
            //println!("k = {}", k);
            let a = BLS24Pairing::ate(&(k*G2), &G1);
            //println!("a = {}", a);
            let b = BLS24Pairing::ate(&G2, &(k*G1));
            //println!("b = {}", b);
            let c = g0.pow(&k);
            //println!("c = {}", c);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(k.is_zero() | !a.is_one() & a.pow_r().is_one()));
            assert!(bool::from(k.is_zero() | !b.is_one() & b.pow_r().is_one()));
            assert!(bool::from(k.is_zero() | !c.is_one() & c.pow_r().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);

            let P1 = BLS24Point::point_factory(BLS24Fp::random(&mut rng)).elim_cof();
            //println!("P1 = {}", P1);
            assert!(bool::from(!P1.is_zero() & (r*P1).is_zero()));
            let P2 = BLS24Point::point_factory(BLS24Fp::random(&mut rng)).elim_cof();
            //println!("P2 = {}", P2);
            assert!(bool::from(!P2.is_zero() & (r*P2).is_zero()));
            let Q1 = BLS24Point4::point_factory(BLS24Fp4::random(&mut rng)).elim_cof();
            //println!("Q1' = {}", Q1);
            assert!(bool::from(!Q1.is_zero() & (r*Q1).is_zero()));
            let Q2 = BLS24Point4::point_factory(BLS24Fp4::random(&mut rng)).elim_cof();
            //println!("Q2' = {}", Q2);
            assert!(bool::from(!Q2.is_zero() & (r*Q2).is_zero()));

            let g: BLS24Fp24<PAR, LIMBS> = BLS24Pairing::ate(&Q1, &P1);
            //println!("**** g = a(Q1, P1)             = {}", g);
            assert!(bool::from(!g.is_one() & g.pow_r().is_one()));

            // linearity in the 1st argument:
            let gs: BLS24Fp24<PAR, LIMBS> = BLS24Pairing::ate(&(Q1 + Q2), &P1);
            //println!("**** g = a(Q1' + Q2', P1)      = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_r().is_one()));
            let gp = g*BLS24Pairing::ate(&Q2, &P1);
            //println!("**** g ? a(Q1', P1)*a(Q2', P1) = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_r().is_one()));
            assert_eq!(gp, gs);

            // linearity in the 2nd argument:
            let gs: BLS24Fp24<PAR, LIMBS> = BLS24Pairing::ate(&Q1, &(P1 + P2));
            //println!("**** g = a(Q1', P1 + P2)       = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_r().is_one()));
            let gp = g*BLS24Pairing::ate(&Q1, &P2);
            //println!("**** g ? a(Q1', P1)*a(Q1', P2) = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_r().is_one()));
            assert_eq!(gp, gs);

            let a = BLS24Pairing::ate(&(k*Q1), &P1);
            let b = BLS24Pairing::ate(&Q1, &(k*P1));
            let c = g.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_r().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_r().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_r().is_one()));
            assert!(bool::from(!g.is_one() & g.pow_r().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);
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
    fn BLS24317Pairing_test() {
        const LIMBS: usize = BLS24317Param::LIMBS;
        BLS24Pairing_test::<BLS24317Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24324Pairing_test() {
        const LIMBS: usize = BLS24324Param::LIMBS;
        BLS24Pairing_test::<BLS24324Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24329Pairing_test() {
        const LIMBS: usize = BLS24329Param::LIMBS;
        BLS24Pairing_test::<BLS24329Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24339Pairing_test() {
        const LIMBS: usize = BLS24339Param::LIMBS;
        BLS24Pairing_test::<BLS24339Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24341Pairing_test() {
        const LIMBS: usize = BLS24341Param::LIMBS;
        BLS24Pairing_test::<BLS24341Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24342Pairing_test() {
        const LIMBS: usize = BLS24342Param::LIMBS;
        BLS24Pairing_test::<BLS24342Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24343Pairing_test() {
        const LIMBS: usize = BLS24343Param::LIMBS;
        BLS24Pairing_test::<BLS24343Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24347Pairing_test() {
        const LIMBS: usize = BLS24347Param::LIMBS;
        BLS24Pairing_test::<BLS24347Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24348Pairing_test() {
        const LIMBS: usize = BLS24348Param::LIMBS;
        BLS24Pairing_test::<BLS24348Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24349Pairing_test() {
        const LIMBS: usize = BLS24349Param::LIMBS;
        BLS24Pairing_test::<BLS24349Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24358Pairing_test() {
        const LIMBS: usize = BLS24358Param::LIMBS;
        BLS24Pairing_test::<BLS24358Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24362Pairing_test() {
        const LIMBS: usize = BLS24362Param::LIMBS;
        BLS24Pairing_test::<BLS24362Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24365Pairing_test() {
        const LIMBS: usize = BLS24365Param::LIMBS;
        BLS24Pairing_test::<BLS24365Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24379Pairing_test() {
        const LIMBS: usize = BLS24379Param::LIMBS;
        BLS24Pairing_test::<BLS24379Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24380Pairing_test() {
        const LIMBS: usize = BLS24380Param::LIMBS;
        BLS24Pairing_test::<BLS24380Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24407Pairing_test() {
        const LIMBS: usize = BLS24407Param::LIMBS;
        BLS24Pairing_test::<BLS24407Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24409Pairing_test() {
        const LIMBS: usize = BLS24409Param::LIMBS;
        BLS24Pairing_test::<BLS24409Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24429Pairing_test() {
        const LIMBS: usize = BLS24429Param::LIMBS;
        BLS24Pairing_test::<BLS24429Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24449Pairing_test() {
        const LIMBS: usize = BLS24449Param::LIMBS;
        BLS24Pairing_test::<BLS24449Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24454Pairing_test() {
        const LIMBS: usize = BLS24454Param::LIMBS;
        BLS24Pairing_test::<BLS24454Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24459Pairing_test() {
        const LIMBS: usize = BLS24459Param::LIMBS;
        BLS24Pairing_test::<BLS24459Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24469Pairing_test() {
        const LIMBS: usize = BLS24469Param::LIMBS;
        BLS24Pairing_test::<BLS24469Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24470Pairing_test() {
        const LIMBS: usize = BLS24470Param::LIMBS;
        BLS24Pairing_test::<BLS24470Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24471Pairing_test() {
        const LIMBS: usize = BLS24471Param::LIMBS;
        BLS24Pairing_test::<BLS24471Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24472Pairing_test() {
        const LIMBS: usize = BLS24472Param::LIMBS;
        BLS24Pairing_test::<BLS24472Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24477Pairing_test() {
        const LIMBS: usize = BLS24477Param::LIMBS;
        BLS24Pairing_test::<BLS24477Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24481Pairing_test() {
        const LIMBS: usize = BLS24481Param::LIMBS;
        BLS24Pairing_test::<BLS24481Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24485Pairing_test() {
        const LIMBS: usize = BLS24485Param::LIMBS;
        BLS24Pairing_test::<BLS24485Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24489Pairing_test() {
        const LIMBS: usize = BLS24489Param::LIMBS;
        BLS24Pairing_test::<BLS24489Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24507Pairing_test() {
        const LIMBS: usize = BLS24507Param::LIMBS;
        BLS24Pairing_test::<BLS24507Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24519Pairing_test() {
        const LIMBS: usize = BLS24519Param::LIMBS;
        BLS24Pairing_test::<BLS24519Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24520Pairing_test() {
        const LIMBS: usize = BLS24520Param::LIMBS;
        BLS24Pairing_test::<BLS24520Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24529Pairing_test() {
        const LIMBS: usize = BLS24529Param::LIMBS;
        BLS24Pairing_test::<BLS24529Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24539Pairing_test() {
        const LIMBS: usize = BLS24539Param::LIMBS;
        BLS24Pairing_test::<BLS24539Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24549Pairing_test() {
        const LIMBS: usize = BLS24549Param::LIMBS;
        BLS24Pairing_test::<BLS24549Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24559Pairing_test() {
        const LIMBS: usize = BLS24559Param::LIMBS;
        BLS24Pairing_test::<BLS24559Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24569Pairing_test() {
        const LIMBS: usize = BLS24569Param::LIMBS;
        BLS24Pairing_test::<BLS24569Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24571Pairing_test() {
        const LIMBS: usize = BLS24571Param::LIMBS;
        BLS24Pairing_test::<BLS24571Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24587Pairing_test() {
        const LIMBS: usize = BLS24587Param::LIMBS;
        BLS24Pairing_test::<BLS24587Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24589Pairing_test() {
        const LIMBS: usize = BLS24589Param::LIMBS;
        BLS24Pairing_test::<BLS24589Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24600Pairing_test() {
        const LIMBS: usize = BLS24600Param::LIMBS;
        BLS24Pairing_test::<BLS24600Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24605Pairing_test() {
        const LIMBS: usize = BLS24605Param::LIMBS;
        BLS24Pairing_test::<BLS24605Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24609Pairing_test() {
        const LIMBS: usize = BLS24609Param::LIMBS;
        BLS24Pairing_test::<BLS24609Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24617Pairing_test() {
        const LIMBS: usize = BLS24617Param::LIMBS;
        BLS24Pairing_test::<BLS24617Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24619Pairing_test() {
        const LIMBS: usize = BLS24619Param::LIMBS;
        BLS24Pairing_test::<BLS24619Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24623Pairing_test() {
        const LIMBS: usize = BLS24623Param::LIMBS;
        BLS24Pairing_test::<BLS24623Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24627Pairing_test() {
        const LIMBS: usize = BLS24627Param::LIMBS;
        BLS24Pairing_test::<BLS24627Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24629Pairing_test() {
        const LIMBS: usize = BLS24629Param::LIMBS;
        BLS24Pairing_test::<BLS24629Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24631Pairing_test() {
        const LIMBS: usize = BLS24631Param::LIMBS;
        BLS24Pairing_test::<BLS24631Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BLS24639Pairing_test() {
        const LIMBS: usize = BLS24639Param::LIMBS;
        BLS24Pairing_test::<BLS24639Param, LIMBS>();
    }

}
