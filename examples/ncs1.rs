use bls24_curves::bls24fp::BLS24Fp;
use bls24_curves::bls24fp4::BLS24Fp4;
use bls24_curves::bls24pairing::BLS24Pairing;
use bls24_curves::bls24param::{BLS24Param, BLS24317Param, BLS24324Param, BLS24329Param, BLS24339Param, BLS24341Param, BLS24342Param, BLS24343Param, BLS24347Param, BLS24348Param, BLS24349Param, BLS24358Param, BLS24362Param, BLS24365Param, BLS24379Param, BLS24380Param, BLS24407Param, BLS24409Param, BLS24429Param, BLS24449Param, BLS24454Param, BLS24459Param, BLS24469Param, BLS24470Param, BLS24471Param, BLS24472Param, BLS24477Param, BLS24481Param, BLS24485Param, BLS24489Param, BLS24507Param, BLS24519Param, BLS24520Param, BLS24529Param, BLS24539Param, BLS24549Param, BLS24559Param, BLS24569Param, BLS24571Param, BLS24587Param, BLS24589Param, BLS24600Param, BLS24605Param, BLS24609Param, BLS24617Param, BLS24619Param, BLS24623Param, BLS24627Param, BLS24629Param, BLS24631Param, BLS24639Param};
use bls24_curves::bls24point::BLS24Point;
use bls24_curves::bls24point4::BLS24Point4;
use crypto_bigint::{NonZero, Random, RandomMod, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConstantTimeEq};
use std::marker::PhantomData;
use std::time::SystemTime;
use crypto_bigint::rand_core::RngCore;

/// The Boneh-Freeman-Katz-Waters NCS&#x2081; scheme for signing a linear subspace.
///
/// Reference:
///
/// * D. Boneh, D. Freeman, J. Katz, B. Waters,
/// "Signing a Linear Subspace: Signature Schemes for Network Coding."
/// LNCS 5443, pp. 68--87, 2009.
/// International Conference on Practice and Theory in Public Key Cryptography -- PKC 2009
/// https://doi.org/10.1007/978-3-642-00468-1_5
#[allow(non_camel_case_types)]
pub struct NCS1<PAR: BLS24Param, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<PAR>,
);

impl<PAR: BLS24Param, const LIMBS: usize> NCS1<PAR, LIMBS> {
    /// Given a pairing friendly elliptic curve with groups
    /// <b>G</b><i>&#x2081;</i>, <b>G</b><i>&#x2082;</i> and <b>G</b><i><sub>T</sub></i>,
    /// choose generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and <i>Q</i> &in; <b>G</b><i>&#x2082;</i>.
    ///
    /// Choose a random value <i>sk</i> &#8668; &Zopf;<i>&#x2099;</i> where &Zopf;<i>&#x2099;</i>
    /// is the scalar field of the elliptic curve, and set <i>R</i> &larr; &lbrack;<i>sk</i>&rbrack;<i>Q</i>.
    ///
    /// Output the public key <i>pk</i> &#x2254; (<i>P, Q, R</i>) &in;
    /// <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2082;</i> &times; <b>G</b><i>&#x2082;</i>
    /// and the secret key <i>sk</i>.
    #[allow(non_snake_case)]
    pub fn setup<R: RngCore + ?Sized>(rng: &mut R)
                 -> ((BLS24Point<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>), Uint<LIMBS>) {
        /*
        // default generators:
        let P = BLS24Point::gen();
        let Q = BLS24Point4::gen();
        // */
        //*
        // individualized generators:
        let P = BLS24Point::point_factory(BLS24Fp::random(rng));
        let Q = BLS24Point4::point_factory(BLS24Fp4::random(rng)).elim_cof();
        // */
        let n: Uint<LIMBS> = Uint::from_words(PAR::ORDER.try_into().unwrap());
        let sk = Uint::random_mod(rng, &NonZero::new(n).unwrap());
        let R = sk*Q;
        let pk = (P, Q, R);
        (pk, sk)
    }

    /// Given a secret key <i>sk</i>, the point <i>P &in; <b>G</b>&#x2081;</i> from the public key <i>pk</i>,
    /// an identifier <i>id</i>, an <i>index</i> corresponding to the row being signed, and a message <i>m</i>,
    /// output the signature as <i>&sigma; := &lbrack;sk&rbrack;(H(id, index) + &lbrack;m&rbrack;P)</i>,
    /// where <i>H(id, index)</i> hashes to the group <i><b>G</b>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn sign(sk: Uint<LIMBS>, pk: (BLS24Point<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>),
                id: String, index: usize, m: Uint<LIMBS>) -> BLS24Point<PAR, LIMBS> {
        let P = pk.0;
        let data = [id.as_bytes(), index.to_string().as_bytes()].concat();
        let sigma = sk*(BLS24Point::shake256(&*data) + m*P);
        sigma
    }

    /// Given a public key <i>pk = (P, Q, R)</i>,
    /// an identifier <i>id</i>, an <i>index</i> corresponding to the row being signed, a message <i>m</i>,
    /// and a signature <i>&sigma;</i>, calculate <i>left := e(&sigma;, Q)</i>
    /// and <i>right := e(H(id, index) + &lbrack;m&rbrack;P, R)</i>, and output
    /// <i>true</i> if <i>left = right</i>, or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn verify(pk: (BLS24Point<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>),
                  id: String, index: usize, m: Uint<LIMBS>, sigma: BLS24Point<PAR, LIMBS>) -> Choice {
        let P = pk.0;
        let Q = pk.1;
        let R = pk.2;
        let data = [id.as_bytes(), index.to_string().as_bytes()].concat();
        let left = BLS24Pairing::ate(&Q, &sigma);
        let right = BLS24Pairing::ate(&R, &(BLS24Point::shake256(&*data) + m*P));
        left.ct_eq(&right)
    }

    /// Given a vector of weights <i>(weight&#x1D62;)</i>
    /// and a vector of signatures <i>(&sigma;&#x1D62;)</i>, each of length <i>k</i>,
    /// calculate the aggregate signature
    /// <i>S := &Sigma;&#x1D62;&#x208C;&#x2080;&#x1D4F; &lbrack;w&#x1D62;&rbrack;&sigma;&#x1D62;</i>.
    #[allow(non_snake_case)]
    pub fn combine(weight: &[Uint<LIMBS>], sigma: &[BLS24Point<PAR, LIMBS>]) -> BLS24Point<PAR, LIMBS> {
        let mut S: BLS24Point<PAR, LIMBS> = BLS24Point::zero();
        for i in 0..weight.len() {
            S += weight[i]*sigma[i];
        }
        S
    }

    /// Given a public key <i>pk = (P, Q, R)</i>, an identifier <i>id</i>,
    /// a vector of weights <i>(weight&#x1D62;)</i> of length <i>k</i>, a message <i>m</i>,
    /// and an aggregate_signature <i>S</i>, verify that the message corresponds
    /// to the weighted average of signed original messages by calculating
    /// <i>left := e(S, Q)</i> and
    /// <i>right := e(&Sigma;&#x1D62;&#x208C;&#x2080;&#x1D4F; &lbrack;w&#x1D62;&rbrack;&#x1D62;H(id, i) + &lbrack;m&rbrack;P, R)</i>,
    /// and output <i>true</i> if <i>left = right</i>, or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn verify_aggregate(pk: (BLS24Point<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>),
                            id: String, weight: &[Uint<LIMBS>], m: Uint<LIMBS>, S: BLS24Point<PAR, LIMBS>) -> Choice {
        let P = pk.0;
        let Q = pk.1;
        let R = pk.2;
        let mut T: BLS24Point<PAR, LIMBS> = m*P;
        for i in 0..weight.len() {
            let data = [id.as_bytes(), i.to_string().as_bytes()].concat();
            T += weight[i]*BLS24Point::shake256(&*data);
        }
        let left = BLS24Pairing::ate(&Q, &S);
        let right = BLS24Pairing::ate(&R, &T);
        left.ct_eq(&right)
    }
}

/// A simple driver for a few benchmarks on the PAR bls24_curves
#[allow(non_snake_case)]
fn main() {
    // choose a target parameter set:
    type PAR = BLS24317Param;
    //type PAR = BLS24324Param;
    //type PAR = BLS24329Param;
    //type PAR = BLS24339Param;
    //type PAR = BLS24341Param;
    //type PAR = BLS24342Param;
    //type PAR = BLS24343Param;
    //type PAR = BLS24347Param;
    //type PAR = BLS24348Param;
    //type PAR = BLS24349Param;
    //type PAR = BLS24358Param;
    //type PAR = BLS24362Param;
    //type PAR = BLS24365Param;
    //type PAR = BLS24379Param;
    //type PAR = BLS24380Param;
    //type PAR = BLS24407Param;
    //type PAR = BLS24409Param;
    //type PAR = BLS24429Param;
    //type PAR = BLS24449Param;
    //type PAR = BLS24454Param;
    //type PAR = BLS24459Param;
    //type PAR = BLS24469Param;
    //type PAR = BLS24470Param;
    //type PAR = BLS24471Param;
    //type PAR = BLS24472Param;
    //type PAR = BLS24477Param;
    //type PAR = BLS24481Param;
    //type PAR = BLS24485Param;
    //type PAR = BLS24489Param;
    //type PAR = BLS24507Param;
    //type PAR = BLS24519Param;
    //type PAR = BLS24520Param;
    //type PAR = BLS24529Param;
    //type PAR = BLS24539Param;
    //type PAR = BLS24549Param;
    //type PAR = BLS24559Param;
    //type PAR = BLS24569Param;
    //type PAR = BLS24571Param;
    //type PAR = BLS24587Param;
    //type PAR = BLS24589Param;
    //type PAR = BLS24600Param;
    //type PAR = BLS24605Param;
    //type PAR = BLS24609Param;
    //type PAR = BLS24617Param;
    //type PAR = BLS24619Param;
    //type PAR = BLS24623Param;
    //type PAR = BLS24627Param;
    //type PAR = BLS24629Param;
    //type PAR = BLS24631Param;
    //type PAR = BLS24639Param;

    const LIMBS: usize = PAR::LIMBS;
    println!("Showcasing NCS1 over PAR{:03}...", 64*LIMBS - 2);
    let mut rng = rand::rng();
    let now = SystemTime::now();

    // setup:
    let (pk, sk) = NCS1::<PAR, LIMBS>::setup(&mut rng);
    println!("    pk: {:?}", pk);
    println!("    sk: {}", sk.to_string_radix_vartime(10));

    // sign:
    let sigma = NCS1::<PAR, LIMBS>::sign(sk, pk, "id".to_string(), 0, Uint::from_word(31415926536));
    println!("    sign: {}", sigma);

    // verify:
    let ok = NCS1::<PAR, LIMBS>::verify(pk, "id".to_string(), 0, Uint::from_word(31415926536), sigma);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = NCS1::<PAR, LIMBS>::verify(pk, "id".to_string(), 0, Uint::from_word(27182818285), sigma);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    let w = [Uint::from_word(34), Uint::from_word(55)];
    let m = [Uint::from_word(27182818285), Uint::from_word(31415926536)];
    let tau0 = NCS1::<PAR, LIMBS>::sign(sk, pk, "id".to_string(), 0, m[0]);
    let tau1 = NCS1::<PAR, LIMBS>::sign(sk, pk, "id".to_string(), 1, m[1]);
    let S = NCS1::<PAR, LIMBS>::combine(&w, &[tau0, tau1]);
    let M = w[0]*m[0] + w[1]*m[1];
    println!("    aggregate signature: {}", S);

    let ok = NCS1::<PAR, LIMBS>::verify_aggregate(pk, "id".to_string(), &w, M, S);
    println!("    verify_aggregate 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = NCS1::<PAR, LIMBS>::verify_aggregate(pk, "id".to_string(), &w, Uint::ZERO, S);
    println!("    verify_aggregate 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    match now.elapsed() {
        Ok(elapsed) => {
            println!("Total elapsed time: {} ms.", (elapsed.as_micros() as f64)/1000.0);
        }
        Err(e) => {
            println!("Error: {e:?}");
        }
    }
}
