#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use bls24_curves::bls24fp::BLS24Fp;
use bls24_curves::bls24fp4::BLS24Fp4;
use bls24_curves::bls24fp24::BLS24Fp24;
use bls24_curves::bls24pairing::BLS24Pairing;
use bls24_curves::bls24param::{BLS24Param, BLS24317Param, BLS24324Param, BLS24329Param, BLS24339Param, BLS24341Param, BLS24342Param, BLS24343Param, BLS24347Param, BLS24348Param, BLS24349Param, BLS24358Param, BLS24362Param, BLS24365Param, BLS24379Param, BLS24380Param, BLS24407Param, BLS24409Param, BLS24429Param, BLS24449Param, BLS24454Param, BLS24459Param, BLS24469Param, BLS24470Param, BLS24471Param, BLS24472Param, BLS24477Param, BLS24481Param, BLS24485Param, BLS24489Param, BLS24507Param, BLS24519Param, BLS24520Param, BLS24529Param, BLS24539Param, BLS24549Param, BLS24559Param, BLS24569Param, BLS24571Param, BLS24587Param, BLS24589Param, BLS24600Param, BLS24605Param, BLS24609Param, BLS24617Param, BLS24619Param, BLS24623Param, BLS24627Param, BLS24629Param, BLS24631Param, BLS24639Param};
use bls24_curves::bls24point::BLS24Point;
use bls24_curves::bls24point4::BLS24Point4;
use bls24_curves::bls24zr::BLS24Zr;
use bls24_curves::traits::{BLS24Field, One};
use crypto_bigint::{Random, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::RngCore;
use std::marker::PhantomData;
use std::time::SystemTime;

/// The Boneh-Gentry-Lynn-Shacham (BGLS) aggregate signature scheme over BLS24 curves.
///
/// NB: The original description assumed Type 2 pairings, which Chatterjee and Menezes argue
/// to be just an inefficient form of Type 3 pairings.  Indeed, it is possible to adapt both
/// BGLS protocols (i.e. the aggregate signature scheme and the verifiably encrypted
/// signature scheme alike) and their security proofs under the q-SDH assumption to Type 3 pairings,
/// and this implementation follows this more natural and more efficient approach.
///
/// References:
///
/// * D. Boneh, C. Gentry, B. Lynn, H. Shacham,
/// "Aggregate and Verifiably Encrypted Signatures from Bilinear Maps."
/// Advances in Cryptology -- EUROCRYPT 2003, LNCS 2656, pp. 416--432, Springer, 2003.
/// https://doi.org/10.1007/11593447_28
///
/// * S. Chatterjee, A. Menezes,
/// "On cryptographic protocols employing asymmetric pairings -- The role of &Psi; revisited."
/// Discrete Applied Mathematics, vol. 159, no. 13, pp. 1311--1322, ScienceDirect, 2011.
/// https://doi.org/10.1016/j.dam.2011.04.021
#[allow(non_camel_case_types)]
pub struct BGLS<PAR: BLS24Param, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<PAR>,
);

impl<PAR: BLS24Param, const LIMBS: usize> BGLS<PAR, LIMBS> {

    /// Given a pairing-friendly elliptic curve with groups
    /// <b>G</b><i>&#x2081;</i>, <b>G</b><i>&#x2082;</i> and <b>G</b><i><sub>T</sub></i>,
    /// choose and output public generators <i>P</i> &in; <b>G</b><i>&#x2081;</i>
    /// and <i>Q</i> &in; <b>G</b><i>&#x2082;</i>.
    #[allow(non_snake_case)]
    pub fn setup() -> (BLS24Point<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>) {
        /*
        // default generators:
        let P = BLS24Point::default_generator();
        let Q = BLS24Point4::default_generator();
        // */
        //*
        // pick individualized generators:
        let BGLS_ID = "BGLS ID".to_string().into_bytes().to_vec();  // or pick them randomly
        let P = BLS24Point::point_factory(BLS24Fp::shake256(&BGLS_ID)).elim_cof();
        let Q = BLS24Point4::point_factory(BLS24Fp4::shake256(&BGLS_ID)).elim_cof();
        // */
        (P, Q)
    }

    /// A sample hash function <i>H</i> ∶ <b>G</b><i>&#x2082;</i> &times; {0,1}&ast; → <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn H(V: &BLS24Point4<PAR, LIMBS>, m: &[u8]) -> BLS24Point<PAR, LIMBS> {
        let mut bytes: Vec<u8> = m.to_vec();
        let mut nonce: Vec<u8> = V.to_bytes();
        bytes.append(&mut nonce);
        let mut sep: Vec<u8> = "BGLS H".to_string().into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        BLS24Point::point_factory(BLS24Fp::shake256(bytes.as_slice())).elim_cof()
    }

    /// For each user, pick a random <i>s</i> &#8668; &Zopf;<i>&#x2099;&ast;</i>
    /// and compute <i>V</i> &#x2254; &lbrack;<i>s</i>&rbrack;<i>Q</i>.
    /// The user's public key is <i>V</i> &in; <b>G</b><i>&#x2082;</i>
    /// and their private key is <i>s</i> &in; &Zopf;<i>&#x2099;&ast;</i>.
    #[allow(non_snake_case)]
    pub fn keygen<R: RngCore + ?Sized>(rng: &mut R, Q: &BLS24Point4<PAR, LIMBS>)
            -> (BLS24Point4<PAR, LIMBS>, BLS24Zr<PAR, LIMBS>) {
        let s = BLS24Zr::random(rng);
        let V = s*(*Q);
        (V, s)
    }

    /// Given a user's key pair (<i>V</i>, <i>s</i>) and a message <i>m</i>,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) and
    /// generate a BGLS signature <i>&sigma;</i> &larr; &lbrack;<i>s</i>&rbrack;<i>M</i>
    /// for <i>m</i> verifiable under <i>V</i>.
    #[allow(non_snake_case)]
    pub fn sign(V: &BLS24Point4<PAR, LIMBS>, s: &BLS24Zr<PAR, LIMBS>, m: &[u8]) -> BLS24Point<PAR, LIMBS> {
        // hash M ← H(V, m) ∈ G_1:
        let M = BGLS::H(&V, m);
        // compute the signature σ ← [s]M:
        let sigma = (*s)*M;
        sigma
    }

    /// Given a public key <i>V</i>, a message <i>m</i>, and a signature <i>&sigma;</i>,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) and accept iff
    /// e(<i>&sigma;</i>, <i>Q</i>) = e(<i>M</i>, <i>V</i>).
    #[allow(non_snake_case)]
    pub fn verify(Q: &BLS24Point4<PAR, LIMBS>, V: &BLS24Point4<PAR, LIMBS>,
            m: &[u8], sigma: &BLS24Point<PAR, LIMBS>) -> Choice {
        // hash M ← H(V, m) ∈ G_1:
        let M = BGLS::H(&V, m);
        // accept iff e(σ, Q) = e(M, V)
        BLS24Pairing::ate(Q, sigma).ct_eq(&BLS24Pairing::ate(V, &M))
    }

    /// Let &lbrack;<i>&sigma;&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; be a set of signatures created for
    /// corresponding messages &lbrack;<i>m&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; and verifiable under
    /// matching public keys &lbrack;<i>V&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack;.
    /// Their aggregate signature is <i>&sigma;</i> &larr; &Sigma;<sub><i>0&leq;i&lt;k</i></sub>
    /// <i>&sigma;&#x1D62;</i> &in; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn aggregate(sigma: &[BLS24Point<PAR, LIMBS>]) -> BLS24Point<PAR, LIMBS> {
        let mut Sigma = BLS24Point::zero();
        for sig in sigma {
            Sigma += *sig;
        }
        Sigma
    }

    /// Let &lbrack;<i>m&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; be a set of messages
    /// signed into an aggregated signature <i>&Sigma;</i>, and let
    /// &lbrack;<i>V&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; be a set of corresponding public keys.
    /// Compute <i>M&#x1D62;</i> &larr; <i>H</i>(<i>V&#x1D62;</i>, <i>m&#x1D62;</i>) for all <i>0&leq;i&lt;k</i>
    /// and accept iff e(<i>&Sigma;</i>, <i>Q</i>) =
    /// &Pi;<sub><i>0&leq;i&lt;k</i></sub> e(<i>M&#x1D62;</i>, <i>V&#x1D62;</i>).
    #[allow(non_snake_case)]
    pub fn verify_aggregate(Q: &BLS24Point4<PAR, LIMBS>, V: &[BLS24Point4<PAR, LIMBS>],
            Sigma: &BLS24Point<PAR, LIMBS>, m: &Vec<Vec<u8>>) -> Choice {
        if m.len() != V.len() {
            return Choice::from(0);  // impossible to verify lists of unequal lengths
        }
        let mut rhs = BLS24Fp24::<PAR, LIMBS>::one();
        for i in 0..m.len() {
            let Mi = BGLS::H(&V[i], &m[i]);
            let ei = BLS24Pairing::ate(&V[i], &Mi);
            rhs *= ei;
        }
        BLS24Pairing::ate(Q, Sigma).ct_eq(&rhs)
    }

    /// Given the public generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// pick a random <i>s<sub>adj</sub></i> &#8668; &Zopf;<i>&#x2099;&ast;</i>
    /// and compute <i>P<sub>adj</sub></i> &larr; &lbrack;<i>s<sub>adj</sub></i>&thinsp;&rbrack;<i>P</i>
    /// and <i>Q<sub>adj</sub></i> &larr; &lbrack;<i>s<sub>adj</sub></i>&thinsp;&rbrack;<i>Q</i>.
    /// The adjudicator's public keys are <i>P<sub>adj</sub></i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i>,
    /// and their private key is <i>s<sub>adj</sub></i> &in; &Zopf;<i>&#x2099;&ast;</i>.
    #[allow(non_snake_case)]
    pub fn ve_keygen<R: RngCore + ?Sized>(rng: &mut R,
            P: &BLS24Point<PAR, LIMBS>, Q: &BLS24Point4<PAR, LIMBS>)
            -> (BLS24Point<PAR, LIMBS>, BLS24Point4<PAR, LIMBS>, BLS24Zr<PAR, LIMBS>) {
        let s_adj = BLS24Zr::random(rng);
        let P_adj = s_adj*(*P);
        let Q_adj = s_adj*(*Q);
        (P_adj, Q_adj, s_adj)
    }

    /// Given the public generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// validate the adjudicator's public keys <i>P<sub>adj</sub></i> &in; <b>G</b><i>&#x2081;</i>
    /// and <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i> for consistency by checking that
    /// e(<i>P<sub>adj</sub></i>&thinsp;, <i>Q</i>) = e(<i>P</i>, <i>Q<sub>adj</sub></i>&thinsp;).
    #[allow(non_snake_case)]
    pub fn ve_validate(P: &BLS24Point<PAR, LIMBS>, Q: &BLS24Point4<PAR, LIMBS>,
            P_adj: &BLS24Point<PAR, LIMBS>, Q_adj: &BLS24Point4<PAR, LIMBS>) -> Choice {
        BLS24Pairing::ate(&Q_adj, &P).ct_eq(&BLS24Pairing::ate(&Q, &P_adj))
    }

    /// Given the public generator <i>P</i> &in; <b>G</b><i>&#x2081;</i>,
    /// a user's key pair (<i>V</i>, <i>s</i>) &in; <b>G</b><i>&#x2082;</i> &times; &Zopf;<i>&#x2099;&ast;</i>,
    /// an adjudicator's public key <i>P<sub>adj</sub></i> &in; <b>G</b><i>&#x2081;</i>,
    /// and a message <i>m</i> &in; {0, 1}&ast;,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) &in; <b>G</b><i>&#x2081;</i> and
    /// <i>&sigma;</i> &larr; &lbrack;<i>s</i>&rbrack;<i>M</i> &in; <b>G</b><i>&#x2081;</i>.
    /// Select <i>r</i> &#8668; &Zopf;<i>&#x2099;&ast;</i> at random, set
    /// <i>&mu;</i> &larr; &lbrack;<i>r</i>&rbrack;<i>P</i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>&sigma;<sub>adj</sub></i> &larr; &lbrack;<i>r</i>&rbrack;<i>P_adj</i> &in; <b>G</b><i>&#x2081;</i>,
    /// and aggregate <i>&omega;</i> &larr; <i>&sigma;</i> + <i>&sigma;<sub>adj</sub></i>
    /// &in; <b>G</b><i>&#x2081;</i>.  The verifiably encrypted signature is the pair
    /// (<i>&omega;</i>, <i>&mu;</i>) &in; <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn ve_sign<R: RngCore + ?Sized>(rng: &mut R,
            P: &BLS24Point<PAR, LIMBS>,
            V: &BLS24Point4<PAR, LIMBS>, s: &BLS24Zr<PAR, LIMBS>,
            P_adj: &BLS24Point<PAR, LIMBS>,
            m: &[u8])
            -> (BLS24Point<PAR, LIMBS>, BLS24Point<PAR, LIMBS>) {
        let M = BGLS::H(&V, m);
        let sigma = (*s)*M;
        let r = BLS24Zr::random(rng);
        let mu = r*(*P);
        let sigma_adj = r*(*P_adj);
        let omega = sigma + sigma_adj;
        (omega, mu)
    }

    /// Given the public generator <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// a user's public key <i>V</i> &in; <b>G</b><i>&#x2082;</i>,
    /// the adjudicator's public key <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i>,
    /// and a verifiably encrypted signature <i>&Sigma;</i> &#x2254;
    /// (<i>&omega;</i>, <i>&mu;</i>) &in; <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2081;</i>
    /// on a message <i>m</i> &in; {0, 1}&ast;,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) &in; <b>G</b><i>&#x2081;</i> and accept iff
    /// e(<i>&omega;</i>, <i>Q</i>) = e(<i>M</i>, <i>V</i>) &middot; e(<i>&mu;</i>, <i>Q<sub>adj</sub></i>&thinsp;).
    #[allow(non_snake_case)]
    pub fn ve_verify(Q: &BLS24Point4<PAR, LIMBS>, V: &BLS24Point4<PAR, LIMBS>, Q_adj: &BLS24Point4<PAR, LIMBS>,
            Sigma: &(BLS24Point<PAR, LIMBS>, BLS24Point<PAR, LIMBS>), m: &[u8]) -> Choice {
        let omega = &Sigma.0;
        let mu = &Sigma.1;
        let M = BGLS::H(&V, m);
        let rhs = BLS24Pairing::ate(V, &M)*BLS24Pairing::ate(Q_adj, &mu);
        BLS24Pairing::ate(Q, &omega).ct_eq(&rhs)
    }

    /// Given the public generator <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// a user's certified public key <i>V</i> &in; <b>G</b><i>&#x2082;</i>,
    /// the adjudicator’s public key <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i>
    /// and corresponding private key <i>s<sub>adj</sub></i> &in; &Zopf;<i>&#x2099;&ast;</i>,
    /// and a verifiably encrypted signature <i>&Sigma;</i> &#x2254;
    /// (<i>&omega;</i>, <i>&mu;</i>) &in; <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2081;</i>
    /// on some message <i>m</i> &in; {0, 1}&ast;,
    /// ensure that the verifiably encrypted signature is valid, and if so,
    /// output the user's signature <i>&sigma;</i> &#x2254;
    /// <i>&omega;</i> - &lbrack;<i>s<sub>adj</sub></i>&thinsp;&rbrack;<i>&mu;</i>
    /// &in; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn ve_adjudicate(Q: &BLS24Point4<PAR, LIMBS>, V: &BLS24Point4<PAR, LIMBS>,
            Q_adj: &BLS24Point4<PAR, LIMBS>, s_adj: &BLS24Zr<PAR, LIMBS>,
            Sigma: &(BLS24Point<PAR, LIMBS>, BLS24Point<PAR, LIMBS>), m: &[u8],
            sigma: &mut BLS24Point<PAR, LIMBS>) -> Choice {
        let ok = BGLS::ve_verify(Q, V, Q_adj, Sigma, m);
        let omega = &Sigma.0;
        let mu = &Sigma.1;
        let adj = (*omega) - (*s_adj)*(*mu);
        sigma.conditional_assign(&adj, ok);
        ok
    }
}

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
    let p: Uint<LIMBS> = Uint::from_words(PAR::MODULUS.try_into().unwrap());
    println!("Showcasing BGLS identity-based signatures over BLS24-{:03}...", p.bits());

    //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
    let mut rng = rand::rng();
    let now = SystemTime::now();

    // ---- BGLS aggregate signatures ----

    // setup:
    println!("setting up...");
    let (P, Q) = BGLS::<PAR, LIMBS>::setup();
    //println!("    P: {:?}", P);
    //println!("    Q: {:?}", Q);

    // keygen:
    const KEYPAIRS: usize = 20;
    println!("generating {} key pair(s)...", KEYPAIRS);
    let mut V: Vec<BLS24Point4<PAR, LIMBS>> = Vec::with_capacity(KEYPAIRS);
    let mut s: Vec<BLS24Zr<PAR, LIMBS>> = Vec::with_capacity(KEYPAIRS);
    for _i in 0..KEYPAIRS {
        let pair = BGLS::<PAR, LIMBS>::keygen(&mut rng, &Q);
        V.push(pair.0);
        //println!("    V_{}: {:?}", _i, V[_i]);
        s.push(pair.1);
        //println!("    s_{}: {:?}", _i, s[_i]);
    }

    // sign:
    println!("signing {} sample message(s)...", KEYPAIRS);
    let mut m: Vec<Vec<u8>> = Vec::with_capacity(KEYPAIRS);
    let mut sigma: Vec<BLS24Point<PAR, LIMBS>> = Vec::with_capacity(KEYPAIRS);
    for i in 0..KEYPAIRS {
        m.push(("sample message #".to_owned() + &i.to_string()).as_bytes().to_vec());
        //println!("    m_{}: {:?}", i, m[i]);
        sigma.push(BGLS::<PAR, LIMBS>::sign(&V[i], &s[i], &m[i]));
        //println!("    sigma_{}: {:?}", i, sigma[i]);
    }

    // verify individually:
    println!("verifying {} signatures individually...", KEYPAIRS);
    let mut x: Vec<Vec<u8>> = Vec::with_capacity(KEYPAIRS);
    for i in 0..KEYPAIRS {
        x.push(("wrong message #".to_owned() + &i.to_string()).as_bytes().to_vec());
        let ok = BGLS::<PAR, LIMBS>::verify(&Q, &V[i], &m[i], &sigma[i]);
        println!("    verify 1: {}  (should be true)", bool::from(ok));
        assert!(bool::from(ok));
        let ok = BGLS::<PAR, LIMBS>::verify(&Q, &V[i], &x[i], &sigma[i]);
        println!("    verify 0: {} (should be false)", bool::from(ok));
        assert!(!bool::from(ok));
    }

    // aggregate:
    println!("aggregating {} signatures...", KEYPAIRS);
    let Sigma = BGLS::<PAR, LIMBS>::aggregate(&sigma);
    //println!("    Sigma: {:?}", Sigma);

    // verify aggregate:
    println!("verifying aggregate...");
    let ok = BGLS::<PAR, LIMBS>::verify_aggregate(&Q, &V, &Sigma, &m);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = BGLS::<PAR, LIMBS>::verify_aggregate(&Q, &V, &Sigma, &x);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    // ---- BGLS verifiably encrypted signatures ----

    // generate the adjudicator's keys:
    println!("generating adjudicator's keys...");
    let (P_adj, Q_adj, s_adj) = BGLS::<PAR, LIMBS>::ve_keygen(&mut rng, &P, &Q);
    //println!("    P_adj: {:?}", P_adj);
    //println!("    Q_adj: {:?}", Q_adj);
    println!("    s_adj: {:?}", s_adj);

    // validate the adjudicator's keys:
    println!("validating adjudicator's keys...");
    let ok = BGLS::ve_validate(&P, &Q, &P_adj, &Q_adj);
    println!("    validate: {}", bool::from(ok));
    assert!(bool::from(ok));

    // sign in verifiably encrypted fashion:
    println!("signing in verifiably encrypted fashion...");
    let Sigma = BGLS::ve_sign(&mut rng, &P,&V[0], &s[0], &P_adj, &m[0]);
    println!("    omega: {:?}", Sigma.0);
    println!("    mu: {:?}", Sigma.1);

    // verify encrypted signature:
    println!("verifying encrypted signature...");
    let ok = BGLS::ve_verify(&Q, &V[0], &Q_adj, &Sigma, &m[0]);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = BGLS::ve_verify(&Q, &V[0], &Q_adj, &Sigma, &x[0]);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    // adjudicate:
    println!("adjudicating...");
    let mut sigma = BLS24Point::<PAR, LIMBS>::zero();
    let ok = BGLS::ve_adjudicate(&Q, &V[0], &Q_adj, &s_adj, &Sigma, &m[0], &mut sigma);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    //println!("    sigma  1: {}", sigma);
    assert!(bool::from(ok));
    let ok = BGLS::verify(&Q, &V[0], &m[0], &sigma);
    println!("    verification of extracted signature: {} (should be true)", bool::from(ok));
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    assert!(bool::from(!sigma.is_zero()));
    let mut sigma = BLS24Point::<PAR, LIMBS>::zero();
    let ok = BGLS::ve_adjudicate(&Q, &V[0], &Q_adj, &s_adj, &Sigma, &x[0], &mut sigma);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    //println!("    sigma  0: {}", sigma);
    assert!(!bool::from(ok));
    assert!(bool::from(sigma.is_zero()));

    match now.elapsed() {
        Ok(elapsed) => {
            println!("Total elapsed time: {} ms.", (elapsed.as_micros() as f64)/1000.0);
        }
        Err(e) => {
            println!("Error: {e:?}");
        }
    }
}
