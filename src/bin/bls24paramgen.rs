//! An executable tool to prepare the bls24params.rs file needed by the bls24-curves crate.
//! 
//! Curve selection criteria
//! 
//! There are four Costello-Lauter-Naehrig families of BLS24 curves.
//! Two of them are richer in KZG-friendly curves, namely, those curves
//! with curve parameter <i>u</i> = 16 (mod 72) and those with <i>u</i> = 64 (mod 72).
//! It is not hard to see that parameters of these shapes are
//! more likely to yield curve orders <i>r</i> = <i>u</i>&#x2078;&nbsp;-&nbsp;<i>u</i>&#x2074;&nbsp;+&nbsp;1
//! of high 2-adicity by just restricting <i>u</i> itself to be a multiple of
//! a fairly high power of 2.  Further, this implementation is restricted
//! to <i>u</i> = 16 (mod 72), so that the curve twist equation has a uniform shape
//! with <i>b'</i> = <i>b</i><i>v</i>, and for simplicity only positive values of <i>u</i>
//! are currently supported.  Finally, following Costello-Lauter-Naehrig,
//! this implementation focuses on sparse parameters only (trinomials, tetranomials,
//! and pentanomials).
//! 
//! This still yields plenty of useful curves, sometimes more than one choice
//! for primes of the same size.  When this happens, the curve with the most sparse
//! parameter <i>u</i> takes precedence.
//! If more than one choice remains, the curve with the highest 2-adicity is chosen
//! (to maximize the circuit depth allowed for KZG polynomial commitments),
//! and if still more than one choice is viable, the one with the largest group order is selected.
//! The range of supported parameters covers target security between
//! ~2&sup1;&#xFEFF;&sup2;&#xFEFF;&#x2078; to ~2&sup2;&#xFEFF;&#x2075;&#xFEFF;&#x2076;.
//! 
//! Each byte of the parameter descriptor indicates one term of the curve parameter <i>u</i>:
//! if the <i>k</i>-th term is +2<i>&#x1D50;</i>, the <i>k</i>-th byte is set to <i>m</i>,
//! and if the <i>k</i>-th term is -2<i>&#x1D50;</i>, the <i>k</i>-th byte is set to 256&nbsp;-&nbsp;<i>m</i>
//! (this upper bounds the degree <i>m</i> at 127, but for the actual parameters the degree
//! does not exceed 64 anyway).

use crypto_bigint::{Integer, Limb, NonZero, One, Uint, Word, Zero};
use crypto_bigint::subtle::ConditionallySelectable;
use std::ops::{Div,Shl};

const LIMBS: usize = 16;  // maximum supported size (1024 bits)

/// Compute <i>r</i> := <i>u&#x02E3;</i> mod <i>p</i>.
fn pow_mod_p(u: Uint<LIMBS>, x: Uint<LIMBS>, p: Uint<LIMBS>) -> Uint<LIMBS> {
    let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
    // the exponent is presumed fixed and public, hence the square-and-multiply method suffices:
    let mut r = Uint::ONE;
    let w = x.as_words();
    for i in (0..LIMBS << 6).rev() {
        r = r.mul_mod_vartime(&r, &nzp);
        if ((w[i >> 6] >> (i & 63)) & 1) == 1 {
            r = r.mul_mod_vartime(&u, &nzp);
        }
    }
    r
}

/// Compute <i>r</i> = &radic;<i>u</i> = <i>u</i><sup>(<i>q</i> + 1)/4</sup> mod <i>q</i>,
/// which satisfies <i>r&sup2;</i> mod <i>q</i> = <i>u</i>
/// if <i>u</i> is a quadratic residue mod <i>q</i> and <i>q</i> &equiv; 3 (mod 4).
fn sqrt(u: Uint<LIMBS>, p: Uint<LIMBS>) -> Uint<LIMBS> {
    pow_mod_p(u, (p + Uint::ONE).shr(2), p) // sqrt exponent: (p + 1)/4
}

fn get_u<const LIMBS: usize>(up: Word) -> Uint<LIMBS> {
    let seq = up;
    assert!(seq & 0xFF > 0);
    let mut u: Uint<LIMBS> = Uint::zero();
    let o: Uint<LIMBS> = Uint::one();
    for b in (0..8).rev() {
        let deg = ((seq >> 8*b) & 0xFF) as usize;  // extract term degree
        if deg >= 0x80 {
            u = u.wrapping_sub(&o.shl(0x100 - deg));
        } else if deg > 0 {
            u = u.wrapping_add(&o.shl(deg));
        }
    }
    u
}

fn poly_u(up: Word) -> String {
    let seq = up;
    assert!(seq & 0xFF > 0);
    let mut u = "".to_string();
    for b in (0..8).rev() {
        let deg = ((seq >> 8*b) & 0xFF) as usize;  // extract term degree
        if deg >= 0x80 {
            u += if u.len() > 0 { " - 2^" } else { "-2^" };
            u += (0x100 - deg).to_string().as_str();
        } else if deg > 0 {
            u += if u.len() > 0 { " + 2^" } else { "2^" };
            u += deg.to_string().as_str();
        }
    }
    u
}

/// A selection of relevant Costello-Lauter-Naehrig <i>u</i> parameters, all positive and sparse
/// (trinomials, tetranomials, and pentanomials) with <i>u</i> &equiv; 16 (mod 72).
///
/// These constraints still yields plenty of useful curves, sometimes more than one choice for <i>p</i> primes of the same size.
/// When this happens, the curve with the sparsest parameter <i>u</i> takes precedence.
/// If more than one choice remains, the curve with the highest 2-adicity is chosen
/// (to maximize the circuit depth allowed for KZG polynomial commitments),
/// and if still more than one choice is viable, the one with the largest group order is selected.
///
/// The range of supported parameters covers target security between ~2&sup1;&sup2;&#x2078; to ~2&sup2;&#x2075;&#x2076; bits,
/// specifically with no curve being included with <i>r</i> &lt; 2&sup2;&#x2075;&#x2075; or <i>r</i> &gt; 2&#x2075;&sup1;&sup2;,
/// nor with p &gt; 2&#x2076;&#x2074;&#x2070; (ten 64-bit limbs) for practical considerations.
///
/// Each byte of a parameter descriptor on this list indicates one term of the curve parameter <i>u</i>:
/// if the <i>k</i>-th term is +2<i>&#x1D50;</i>, the <i>k</i>-th byte is set to <i>m</i>,
/// and if the <i>k</i>-th term is -2<i>&#x1D50;</i>, the <i>k</i>-th byte is set to 256-<i>m</i>
/// (this upper bounds the degree <i>k</i> at 127, but for the actual parameters this does not exceed 64 anyway).
const PARAMDESC: [Word; 50] = [
    // `u` descriptors
    //0x0B0A08,  // D00:  DEBUGGING ONLY!
    //FindPentanomialBLS24Params(31); // 312:  68: 2^31 + 2^29 + 2^24 + 2^20 - 2^17 = A10E0000 =
    //0x1F1D1814EF,  // omitted: r < 2^255
    //FindPentanomialBLS24Params(32); // 317:  64: 2^32 - 2^29 - 2^24 - 2^22 + 2^16 = DEC10000 =
    0x20E3E8EA10,
    //FindTetranomialBLS24Params(33); // 324:  72: 2^33 - 2^31 - 2^28 - 2^18 = 16FFC0000 =
    0x21E1E4EE,
    //FindTetranomialBLS24Params(33); // 329:  84: 2^33 + 2^25 + 2^23 - 2^21 = 202600000 =
    0x211917EB,
    //FindPentanomialBLS24Params(33); // 329:  64: 2^33 + 2^26 + 2^23 - 2^21 + 2^16 = 204610000 =
    //0x211A17EB10,  // omitted
    //FindPentanomialBLS24Params(34); // 339:  68: 2^34 - 2^28 + 2^24 - 2^21 + 2^17 = 3F0E20000 =
    0x22E418EB11,
    //FindPentanomialBLS24Params(34); // 339:  64: 2^34 + 2^28 + 2^26 - 2^20 - 2^16 = 413EF0000 =
    //0x221C1AECF0,  // omitted
    //FindPentanomialBLS24Params(34); // 341:  76: 2^34 + 2^31 - 2^27 - 2^23 + 2^19 = 477880000 =
    0x221FE5E913,
    //FindPentanomialBLS24Params(34); // 342:  80: 2^34 + 2^32 + 2^29 - 2^23 - 2^20 = 51F700000 =
    0x22201DE9EC,
    //FindPentanomialBLS24Params(34); // 343:  68: 2^34 + 2^33 - 2^31 - 2^25 + 2^17 = 57E020000 =
    0x2221E1E711,
    //FindPentanomialBLS24Params(35); // 347:  72: 2^35 - 2^32 - 2^28 - 2^26 - 2^18 = 6EBFC0000 =
    0x23E0E4E6EE,
    //FindPentanomialBLS24Params(35); // 348:  64: 2^35 - 2^31 - 2^29 + 2^25 + 2^16 = 762010000 =
    0x23E1E31910,
    //FindPentanomialBLS24Params(35); // 349:  68: 2^35 + 2^28 + 2^26 + 2^20 + 2^17 = 814120000 =
    0x231C1A1411,
    //FindPentanomialBLS24Params(36); // 358:  68: 2^36 - 2^31 - 2^23 + 2^21 + 2^17 = F7FA20000 =
    0x24E1E91511,
    //FindPentanomialBLS24Params(36); // 362:  80: 2^36 + 2^34 + 2^26 - 2^24 - 2^20 = 1402F00000 =
    0x24221AE8EC,
    //FindPentanomialBLS24Params(36); // 365:  72: 2^36 + 2^35 + 2^32 - 2^26 + 2^18 = 18FC040000 =
    0x242320E612,
    //FindTetranomialBLS24Params(38); // 379:  84: 2^38 - 2^30 - 2^26 + 2^21 = 3FBC200000 =
    //0x26E2E615,  // omitted
    //FindTrinomialBLS24Params(38);   // 379:  72: 2^38 - 2^22 + 2^18 = 3FFFC40000 =
    0x26EA12,
    //FindTetranomialBLS24Params(38); // 380: 104: 2^38 + 2^34 + 2^30 + 2^26 = 4444000000 =
    0x26221E1A,
    //FindTetranomialBLS24Params(41); // 407:  64: 2^41 - 2^38 + 2^20 - 2^16 = 1C0000F0000 =
    0x29DA14F0,
    //FindTrinomialBLS24Params(41);   // 409: 104: 2^41 + 2^28 + 2^26 = 20014000000 =
    0x291C1A,
    //FindTetranomialBLS24Params(43); // 429:  64: 2^43 - 2^33 + 2^31 - 2^16 = 7FE7FFF0000 =
    //0x2BDF1FF0,  // omitted
    //FindTetranomialBLS24Params(43); // 429:  76: 2^43 - 2^30 + 2^21 - 2^19 = 7FFC0180000 =
    0x2BE215ED,
    //FindTetranomialBLS24Params(45); // 449:  88: 2^45 - 2^36 + 2^31 + 2^22 = 1FF080400000 =
    //0x2DDC1F16,  // omitted
    //FindTrinomialBLS24Params(45);   // 449:  80: 2^45 - 2^29 + 2^20 = 1FFFE0100000 =
    0x2DE314,
    //FindPentanomialBLS24Params(45); // 454:  96: 2^45 + 2^44 - 2^42 + 2^32 + 2^24 = 2C0101000000 =
    0x2D2CD62018,
    //FindTetranomialBLS24Params(46); // 459: 104: 2^46 - 2^37 + 2^34 + 2^26 = 3FE404000000 =
    0x2EDB221A,
    //FindTetranomialBLS24Params(47); // 469:  84: 2^47 - 2^37 + 2^35 + 2^21 = 7FE800200000 =
    0x2FDB2315,
    //FindTetranomialBLS24Params(47); // 470:  72: 2^47 + 2^43 - 2^36 + 2^18 = 87F000040000 =
    0x2F2BDC12,
    //FindTetranomialBLS24Params(47); // 471: 100: 2^47 + 2^44 - 2^38 + 2^25 = 8FC002000000 =
    0x2F2CDA19,
    //FindPentanomialBLS24Params(47); // 472: 120: 2^47 + 2^45 + 2^42 + 2^36 + 2^30 = A41040000000 =
    0x2F2D2A241E,
    //FindPentanomialBLS24Params(48); // 477:  72: 2^48 - 2^45 + 2^32 - 2^28 - 2^18 = E000EFFC0000 =
    0x30D320E4EE,
    //FindPentanomialBLS24Params(48); // 481:  80: 2^48 + 2^45 - 2^36 - 2^23 + 2^20 = 11FEFFF900000 =
    0x302DDCE914,
    //FindPentanomialBLS24Params(48); // 485:  92: 2^48 + 2^47 + 2^36 + 2^32 + 2^23 = 1801100800000 =
    //0x302F242017,  // omitted
    //FindPentanomialBLS24Params(48); // 485:  88: 2^48 + 2^47 + 2^38 - 2^30 + 2^22 = 1803FC0400000 =
    //0x302F26E216,  // omitted
    //FindPentanomialBLS24Params(48); // 485:  84: 2^48 + 2^47 - 2^35 - 2^25 + 2^21 = 17FF7FE200000 =
    //0x302FDDE715,  // omitted
    //FindPentanomialBLS24Params(48); // 485: 100: 2^48 + 2^47 - 2^35 + 2^33 - 2^25 = 17FF9FE000000 =
    0x302FDD21E7,
    //FindTetranomialBLS24Params(49); // 489:  76: 2^49 + 2^36 - 2^34 + 2^19 = 2000C00080000 =
    0x3124DE13,
    //FindTetranomialBLS24Params(51); // 507:  64: 2^51 - 2^48 + 2^46 - 2^16 = 73FFFFFFF0000 =
    0x33D02EF0,
    //FindTetranomialBLS24Params(52); // 519: 104: 2^52 - 2^32 - 2^30 - 2^26 = FFFFEBC000000 =
    //0x34E0E2E6,  // omitted
    //FindTetranomialBLS24Params(52); // 519:  84: 2^52 + 2^34 + 2^24 - 2^21 = 10000400E00000 =
    //0x342218EB,  // omitted
    //FindTetranomialBLS24Params(52); // 519: 156: 2^52 + 2^45 + 2^43 + 2^39 = 10288000000000 =
    0x342D2B27,
    //FindTetranomialBLS24Params(52); // 520: 136: 2^52 + 2^48 - 2^45 + 2^34 = 10E00400000000 =
    0x3430D322,
    //FindTetranomialBLS24Params(53); // 529: 108: 2^53 + 2^43 + 2^39 - 2^27 = 20087FF8000000 =
    0x352B27E5,
    //FindTetranomialBLS24Params(53); // 529:  68: 2^53 - 2^40 - 2^38 - 2^17 = 1FFEBFFFFE0000 =
    //0x35D8DAEF,  // omitted
    //FindTetranomialBLS24Params(54); // 539:  84: 2^54 - 2^37 - 2^25 - 2^21 = 3FFFDFFDE00000 =
    0x36DBE7EB,
    //FindTetranomialBLS24Params(55); // 549:  88: 2^55 + 2^43 + 2^30 - 2^22 = 8008003FC00000 =
    //0x372B1EEA,  // omitted
    //FindTetranomialBLS24Params(55); // 549: 116: 2^55 + 2^45 + 2^43 - 2^29 = 8027FFE0000000 =
    0x372D2BE3,
    //FindTetranomialBLS24Params(56); // 559:  96: 2^56 - 2^43 + 2^26 + 2^24 = FFF80005000000 =
    //0x38D51A18,  // omitted
    //FindTrinomialBLS24Params(56);   // 559:  80: 2^56 + 2^40 - 2^20 = 10000FFFFF00000 =
    0x3828EC,
    //FindTetranomialBLS24Params(56); // 559:  68: 2^56 + 2^42 - 2^31 - 2^17 = 10003FF7FFE0000 =
    //0x382AE1EF,  // omitted
    //FindTetranomialBLS24Params(57); // 569: 120: 2^57 - 2^46 - 2^43 - 2^30 = 1FFB7FFC0000000 =
    0x39D2D5E2,
    //FindTetranomialBLS24Params(57); // 571: 156: 2^57 + 2^54 + 2^51 + 2^39 = 248008000000000 =
    0x39363327,
    //FindTetranomialBLS24Params(59); // 587: 120: 2^59 - 2^56 - 2^37 - 2^30 = 6FFFFDFC0000000 =
    0x3BC8DBE2,
    //FindTetranomialBLS24Params(59); // 587: 104: 2^59 - 2^56 + 2^48 - 2^26 = 700FFFFFC000000 =
    //0x3BC830E6,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 108: 2^59 - 2^48 + 2^37 - 2^27 = 7FF001FF8000000 =
    //0x3BD025E5,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 72: 2^59 - 2^46 - 2^30 + 2^18 = 7FFBFFFC0040000 =
    //0x3BD2E212,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 64: 2^59 - 2^44 + 2^39 + 2^16 = 7FFF08000010000 =
    //0x3BD42710,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 72: 2^59 - 2^40 + 2^30 - 2^18 = 7FFFF003FFC0000 =
    //0x3BD81EEE,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 64: 2^59 - 2^28 - 2^22 + 2^16 = 7FFFFFFEFC10000 =
    //0x3BE4EA10,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 88: 2^59 + 2^51 + 2^24 - 2^22 = 808000000C00000 =
    //0x3B3318EA,  // omitted
    //FindTetranomialBLS24Params(59); // 589: 112: 2^59 + 2^53 + 2^45 + 2^28 = 820200010000000 =
    0x3B352D1C,
    //FindTetranomialBLS24Params(60); // 600: 104: 2^60 + 2^56 + 2^52 + 2^26 = 1110000004000000 =
    0x3C38341A,
    //FindTetranomialBLS24Params(60); // 605:  76: 2^60 + 2^59 - 2^24 + 2^19 = 17FFFFFFFF080000 =
    0x3C3BE813,
    //FindTetranomialBLS24Params(61); // 609: 108: 2^61 - 2^49 + 2^39 + 2^27 = 1FFE008008000000 =
    //0x3DCF271B,  // omitted
    //FindTetranomialBLS24Params(61); // 609: 132: 2^61 - 2^39 + 2^35 + 2^33 = 1FFFFF8A00000000 =
    0x3DD92321,
    //FindTetranomialBLS24Params(61); // 609:  80: 2^61 + 2^29 + 2^23 + 2^20 = 2000000020900000 =
    //0x3D1D1714,  // omitted
    //FindTetranomialBLS24Params(61); // 609:  92: 2^61 + 2^53 + 2^50 + 2^23 = 2024000000800000 =
    //0x3D353217,  // omitted
    //FindTetranomialBLS24Params(62); // 617: 64: 2^62 - 2^59 - 2^33 + 2^16 = 37FFFFFE00010000 =
    //0x3EC5DF10,  // omitted
    //FindTetranomialBLS24Params(62); // 617: 68: 2^62 - 2^59 + 2^50 - 2^17 = 3803FFFFFFFE0000 =
    0x3EC532EF,
    //FindTetranomialBLS24Params(62); // 619: 68: 2^62 - 2^45 - 2^37 - 2^17 = 3FFFDFDFFFFE0000 =
    0x3ED3DBEF,
    //FindTetranomialBLS24Params(62); // 623: 104: 2^62 + 2^60 + 2^58 + 2^26 = 5400000004000000 =
    0x3E3C3A1A,
    //FindTetranomialBLS24Params(63); // 627: 164: 2^63 - 2^60 - 2^53 + 2^41 = 6FE0020000000000 =
    0x3FC4CB29,
    //FindTrinomialBLS24Params(63);   // 629: 152: 2^63 - 2^47 + 2^38 = 7FFF804000000000 =
    0x3FD126,
    //FindPentanomialBLS24Params(63); // 631: 128: 2^63 + 2^60 + 2^46 + 2^44 - 2^32 = 90004FFF00000000 =
    0x3F3C2E2CE0,
    //FindTetranomialBLS24Params(64); // 639: 120: 2^64 + 2^50 - 2^35 + 2^30 = 10003FFF840000000 =
    0x4032DD1E,
    //FindPentanomialBLS24Params(64); // 639: 148: 2^64 - 2^51 - 2^46 - 2^42 - 2^37 = FFF7BBE000000000 =
    //0x40CDD2D6DB,  // omitted
    //FindTrinomialBLS24Params(65);   // 649:  76: 2^65 + 2^38 - 2^19 = 20000003FFFF80000 =
    //0x4126ED,  // omitted: p > 2^640
];

fn bls24params() {
    let n1: Uint<LIMBS> = Uint::ONE;
    let n2: Uint<LIMBS> = Uint::from_u64(2);
    let n4: Uint<LIMBS> = Uint::from_u64(4);
    let n5: Uint<LIMBS> = Uint::from_u64(5);
    let n6: Uint<LIMBS> = Uint::from_u64(6);

    println!("//! NB: This file was, and future versions should always be, created automatically by the `bls24paramgen` tool.");
    println!();
    println!("#![allow(unused)]");
    println!();
    println!("use crypto_bigint::{{Uint,Word}};");
    println!("use std::ops::Shl;");
    println!();
    println!("pub trait BLS24Param {{");
    println!("    const UD: Word;                           // BLS24 curve parameter descriptor (u is also the optimal pairing order)");
    println!("    const LIMBS: usize;                       // number of limbs required to represent a base field element");
    println!("    const MODULUS: &'static [Word];           // base finite field modulus p");
    println!("    const NEG_INV_MOD: &'static [Word];       // -1/p mod 2^(64*LIMBS)");
    println!("    const MONTY_P: &'static [Word];           // (2^(64*LIMBS))^2 mod p");
    println!("    const CURVE_B: Word;                      // curve equation coefficient");
    println!("    const ORDER: &'static [Word];             // cryptographic group order r");
    println!("    const NEG_INV_ORD: &'static [Word];       // -1/r mod 2^(64*LIMBS)");
    println!("    const MONTY_R: &'static [Word];           // (2^(64*LIMBS))^2 mod r");
    println!("    const NEG_SQRT_NEG_2: &'static [Word];    // -sqrt(-2) mod p");
    println!("    const QNR_SCALE: &'static [Word];         // 1/ξ^((p^2 + 7)/16)");
    println!("    const SQRT_NEG_3: &'static [Word];        // sqrt(-3) mod p");
    println!("    const SVDW: &'static [Word];              // (-1 + sqrt(-3))/2 mod p, the Shallue & van de Woestijne constant");
    println!("    const ZETA: &'static [Word];              // primitive cube root of unity mod p: ζ = u^9 - 3*u^8 + 4*u^7 - 4*u^6 + 3*u^5 - 2*u^3 + 2*u^2 - u + 1");
    println!("    const THETA1: &'static [Word];            // coefficient of the Frobenius endomorphism on the twist");
    println!("    const THETA2: &'static [Word];            // coefficient of the Frobenius endomorphism on the twist");
    println!("    const THETA3: &'static [Word];            // coefficient of the Frobenius endomorphism on the twist");
    println!("    const TRIPLES: Word;                      // number of precomputed optimal pairing triples");
    println!("}}");
    println!();
    println!("pub(crate) fn get_u<PAR: BLS24Param, const LIMBS: usize>() -> Uint<LIMBS> {{");
    println!("    let seq = PAR::UD;");
    println!("    assert!(seq & 0xFF > 0);");
    println!("    let mut u: Uint<LIMBS> = Uint::from_word(0);");
    println!("    let o: Uint<LIMBS> = Uint::from_word(1);");
    println!("    for b in (0..8).rev() {{");
    println!("        let deg = ((seq >> 8*b) & 0xFF) as usize;  // extract term degree");
    println!("        if deg >= 0x80 {{");
    println!("            u = u.wrapping_sub(&o.shl(0x100 - deg));");
    println!("        }} else if deg > 0 {{");
    println!("            u = u.wrapping_add(&o.shl(deg));");
    println!("        }}");
    println!("    }}");
    println!("    u");
    println!("}}");
    println!();

    let v1 = Uint::<LIMBS>::ONE;
    let v2 = Uint::<LIMBS>::from_word(2);
    let v3 = Uint::<LIMBS>::from_word(3);
    let v4 = Uint::<LIMBS>::from_word(4);
    for param in 0..PARAMDESC.len() {
        let u: Uint<LIMBS> = get_u::<LIMBS>(PARAMDESC[param]);
        let u1: Uint<LIMBS> = u.wrapping_sub(&v1);
        let u2: Uint<LIMBS> = u*u;
        let u4: Uint<LIMBS> = u2*u2;

        // c = (u - 1)^2/3
        let c: Uint<LIMBS> = (u1*u1)/v3;  // G_1 cofactor: (u - 1)^2/3
        // r = u^8 - u^4 + 1 = u^4*(u^4 - 1) + 1
        let r: Uint<LIMBS> = (u4*u4.wrapping_sub(&v1)).wrapping_add(&v1);
        let p: Uint<LIMBS> = (c*r).wrapping_add(&u);
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        let p_w = p.to_words();
        let pbits: usize = p.bits() as usize;
        let limbs: usize = (pbits + 63) >> 6;

        let pinvmod2k = p.invert_mod2k((64*limbs) as u32).unwrap();
        let neg_inv_p: Uint<LIMBS> = n1.shl((64*limbs) as u32).wrapping_sub(&pinvmod2k);
        let neg_inv_p_w = neg_inv_p.to_words();

        let mut monty_p = n1.shl((64*limbs) as u32).rem(&nzp);
        monty_p = monty_p.mul_mod_vartime(&monty_p, &nzp);
        let monty_w = monty_p.to_words();

        let r_w = r.to_words();

        let nzr: NonZero<Uint<LIMBS>> = NonZero::new(r).unwrap();

        let rinvmod2k = r.invert_mod2k((64*limbs) as u32).unwrap();
        let neg_inv_r: Uint<LIMBS> = n1.shl((64*limbs) as u32).wrapping_sub(&rinvmod2k);
        let neg_inv_r_w = neg_inv_r.to_words();

        let mut monty_r = Uint::<LIMBS>::ONE.shl((64*limbs) as u32).rem(&nzr);
        monty_r = monty_r.mul_mod_vartime(&monty_r, &nzr);
        let monty_r_w = monty_r.to_words();

        /*
         * The two primitive cube roots of unity are
         * zeta = u^9 - 3*u^8 + 4*u^7 - 4*u^6 + 3*u^5 - 2*u^3 + 2*u^2 - u + 1 and p - zeta - 1.
         * The default one will be that which facilitates a uniform implementation
         * of conjugate computation across all supported curves, namely,
         * the one such that
         * v^(p^4) = v_0 + (zeta + 1)*v_1*z + zeta*v_2*z^2 - v_3*z^3 - (zeta + 1)*v_4*z^4 - zeta*v_5*z^5
         * for any v in the extension field F_{p^24} = F_{p^4}[z]/<z^6 + (1 + i)>.
         */
        // zeta = u^9 - 3*u^8 + 4*u^7 - 4*u^6 + 3*u^5 - 2*u^3 + 2*u^2 - u + 1
        let mut zeta: Uint<LIMBS> = u.clone();
        zeta = zeta.wrapping_sub(&v3); zeta = zeta*u;
        zeta = zeta.wrapping_add(&v4); zeta = zeta*u;
        zeta = zeta.wrapping_sub(&v4); zeta = zeta*u;
        zeta = zeta.wrapping_add(&v3); zeta = zeta*u;
        zeta = zeta*u;
        zeta = zeta.wrapping_sub(&v2); zeta = zeta*u;
        zeta = zeta.wrapping_add(&v2); zeta = zeta*u;
        zeta = zeta.wrapping_sub(&v1); zeta = zeta*u;
        zeta = zeta.wrapping_add(&v1);
        assert_eq!(zeta.mul_mod_vartime(&zeta, &nzp).mul_mod_vartime(&zeta, &nzp), v1);
        let zeta_w = zeta.to_words();

        let sqrt_m3: Uint<LIMBS> = sqrt(Uint::from_word(3).neg_mod(&nzp), p);  // sqrt(-3) mod p
        let sqrt_m3_w = sqrt_m3.to_words();
        let svdw: Uint<LIMBS> = Uint::conditional_select(&(sqrt_m3 - n1), &(sqrt_m3 - n1 + p),
                                                         (sqrt_m3 - n1).is_odd()) >> 1;  // (-1 + sqrt(-3))/2
        let svdw_w = svdw.to_words();

        println!();
        println!("pub struct BLS24{:03}Param;", pbits);
        println!();
        println!("impl BLS24Param for BLS24{:03}Param {{", pbits);

        println!("    const UD: Word = 0x{:X};  // u = {}",
            PARAMDESC[param], poly_u(PARAMDESC[param]));

        println!("    const LIMBS: usize = {};", limbs);

        println!("    const MODULUS: &'static [Word] = &[  // base finite field modulus");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", p_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(p_w[i], 0);
        }
        println!();
        println!("        // p = {}: {} bits", p.to_string_radix_vartime(10), p.bits());
        println!("    ];");

        println!("    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", neg_inv_p_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(neg_inv_p_w[i], 0);
        }
        println!();
        println!("        // -1/p mod 2^{} = {}: {} bits", 64*limbs, neg_inv_p.to_string_radix_vartime(10), neg_inv_p.bits());
        println!("    ];");

        println!("    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", monty_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(monty_w[i], 0);
        }
        println!();
        println!("        // (2^{})^2 mod p = {}: {} bits", 64*limbs, monty_p.to_string_radix_vartime(10), monty_p.bits());
        println!("    ];");

        println!("    const CURVE_B: Word = {};", if (u.as_words()[0] & 1) == 1 { 1 } else { 4 });

        println!("    const ORDER: &'static [Word] = &[  // cryptographic group order");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", r_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(r_w[i], 0);
        }
        println!();
        println!("        // r = {}: {} bits", r.to_string_radix_vartime(10), r.bits());
        println!("    ];");

        println!("    const NEG_INV_ORD: &'static [Word] = &[  // -1/r mod 2^(64*LIMBS)");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", neg_inv_r_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(neg_inv_r_w[i], 0);
        }
        println!();
        println!("        // -1/r mod 2^{} = {}: {} bits", 64*limbs, neg_inv_r.to_string_radix_vartime(10), neg_inv_r.bits());
        println!("    ];");

        println!("    const MONTY_R: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod r");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", monty_r_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(monty_r_w[i], 0);
        }
        println!();
        println!("        // (2^{})^2 mod r = {}: {} bits", 64*limbs, monty_r.to_string_radix_vartime(10), monty_r.bits());
        println!("    ];");

        let msqrt_m2: Uint<LIMBS> = p - sqrt(Uint::from_word(2).neg_mod(&nzp), p);  // -sqrt(-2) mod p
        let msqrt_m2_w = msqrt_m2.to_words();
        println!("    const NEG_SQRT_NEG_2: &'static [Word] = &[  // -sqrt(-2) mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", msqrt_m2_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(msqrt_m2_w[i], 0);
        }
        println!();
        println!("        // -sqrt(-2) mod p = {}: {} bits", msqrt_m2.to_string_radix_vartime(10), msqrt_m2.bits());
        println!("    ];");

        // 1/ξ^((p^2 + 7)/16) = (-4)^((5 + (((u*(u + 1)) & 63) >> 2))*p >> 4)
        let x: Uint<LIMBS> = Uint::from(Limb::from(5u8) + (((u*(u.wrapping_add(&n1))).as_limbs()[0] & Limb::from(63u8)) >> 2))*p >> 4;
        let qnr_scale: Uint<LIMBS> = pow_mod_p(p.wrapping_sub(&n4), x, p);
        let qnr_scale_w = qnr_scale.to_words();
        println!("    const QNR_SCALE: &'static [Word] = &[  // 1/ξ^((p^2 + 7)/16)");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", qnr_scale_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(qnr_scale_w[i], 0);
        }
        println!();
        println!("        // 1/ξ^((p^2 + 7)/16) = {}: {} bits", qnr_scale.to_string_radix_vartime(10), qnr_scale.bits());
        println!("    ];");

        println!("    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", sqrt_m3_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(sqrt_m3_w[i], 0);
        }
        println!();
        println!("    ];");

        println!("    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:016X},", svdw_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(svdw_w[i], 0);
        }
        println!();
        println!("    ];");

        println!("    const ZETA: &'static [Word] = &[  // primitive cube root of unity mod p, in absolute value");
        print!("       ");
        /* big integer words for zeta */
        for i in 0..limbs {
            print!(" 0x{:016X},", zeta_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(zeta_w[i], 0);
        }
        println!();
        println!("        // ζ = {}", zeta.to_string_radix_vartime(10));
        //println!("        //  {}", zeta.to_string_radix_vartime(10));
        println!("    ];");

        // p - 2^(p - 1 - ((p-1) div 6 + 1) div 2) mod p
        let theta: Uint<LIMBS> = p - pow_mod_p(n2, (p - n1) - ((p - n1).div(n6) + n1).shr(1), p);
        let theta_w = theta.to_words();
        println!("    const THETA1: &'static [Word] = &[");
        print!("       ");
        /* big integer words for theta */
        for i in 0..limbs {
            print!(" 0x{:016X},", theta_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(theta_w[i], 0);
        }
        println!();
        println!("        // θ_1 = {}", theta.to_string_radix_vartime(10));
        println!("    ];");

        // p - 2^(p + 1 - 5*((p-1) div 6 + 1) div 2) mod p
        let theta: Uint<LIMBS> = p - pow_mod_p(n2, (p + n1) - n5*((p - n1).div(n6) + n1).shr(1), p);
        let theta_w = theta.to_words();
        println!("    const THETA2: &'static [Word] = &[");
        print!("       ");
        /* big integer words for theta */
        for i in 0..limbs {
            print!(" 0x{:016X},", theta_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(theta_w[i], 0);
        }
        println!();
        println!("        // θ_2 = {}", theta.to_string_radix_vartime(10));
        println!("    ];");

        // 2^(p - 1 - ((p+1) div 4 + 1) div 2) mod p
        let theta: Uint<LIMBS> = pow_mod_p(n2, (p - n1) - ((p + n1).shr(2) + n1).shr(1), p);
        let theta_w = theta.to_words();
        println!("    const THETA3: &'static [Word] = &[");
        print!("       ");
        /* big integer words for theta */
        for i in 0..limbs {
            print!(" 0x{:016X},", theta_w[i]);
        }
        for i in limbs..LIMBS {
            assert_eq!(theta_w[i], 0);
        }
        println!();
        println!("        // θ_3 = {}", theta.to_string_radix_vartime(10));
        println!("    ];");

        let ntriples = u.bits() + (((64 - PARAMDESC[param].leading_zeros()) + 7) >> 3) - 1;  // one extra triple for each term in the descriptor, minus one
        println!("    const TRIPLES: Word = {};  // number of precomputed optimal pairing triples", ntriples);

        println!("}}");
    }
}

fn bls24uses() {
    println!();
    print!("    use crate::bls24param::{{");
    for param in 0..PARAMDESC.len() {
        let u: Uint<LIMBS> = get_u(PARAMDESC[param]);
        let v1: Uint<LIMBS> = Uint::<LIMBS>::ONE;
        let u1: Uint<LIMBS> = u.wrapping_sub(&v1);
        let u2: Uint<LIMBS> = u*u;
        let u4: Uint<LIMBS> = u2*u2;

        // c = (u - 1)^2/3
        let c: Uint<LIMBS> = (u1*u1)/Uint::<LIMBS>::from_u8(3);  // G_1 cofactor
        // r = u^8 - u^4 + 1 = u^4*(u^4 - 1) + 1
        let r = u4* u4.wrapping_sub(&v1).wrapping_add(&v1);
        let p = (c*r).wrapping_add(&u);
        let pbits: usize = p.bits() as usize;
        print!("{}BLS24{:03}Param,", if param % 5 == 0 { "\n        " } else { " " }, pbits);
    }
    println!("\n    }};");
}

fn bls24tests(module: &str) {
    for param in 0..PARAMDESC.len() {
        let u = get_u::<LIMBS>(PARAMDESC[param]);
        let v1 = Uint::<LIMBS>::ONE;
        let u1 = u.wrapping_sub(&v1);
        let u2 = u*u;
        let u4 = u2*u2;

        // c = (u - 1)^2/3
        let c: Uint<LIMBS> = (u1*u1)/Uint::<LIMBS>::from_u8(3);  // G_1 cofactor
        // r = u^8 - u^4 + 1 = u^4*(u^4 - 1) + 1
        let r = u4* u4.wrapping_sub(&v1).wrapping_add(&v1);
        let p = (c*r).wrapping_add(&u);
        let pbits: usize = p.bits() as usize;
        println!();
        println!("     #[test]");
        println!("     #[allow(non_snake_case)]");
        println!("     fn BLS24{:03}{}_test() {{", pbits, module);
        println!("         const LIMBS: usize = BLS24{:03}Param::LIMBS;", pbits);
        println!("         BLS24{}_test::<BLS24{:03}Param, LIMBS>();", module, pbits);
        println!("     }}");
    }
}

fn main() {
    bls24params();
    //bls24uses();
    //bls24tests("Fp");
    //bls24tests("Fp2");
    //bls24tests("Fp4");
    //bls24tests("Point");
    //bls24tests("Point2");
    //bls24tests("Zr");
}
