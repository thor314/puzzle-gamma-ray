#![allow(non_snake_case)]
#![allow(clippy::clone_on_copy)]

use std::{fs::File, io::Cursor};

use ark_crypto_primitives::{
  crh::{poseidon, TwoToOneCRHScheme, *},
  merkle_tree::{constraints::*, Config, MerkleTree, Path, *},
  snark::SNARK,
  sponge::poseidon::PoseidonConfig,
};
use ark_ec::{AffineRepr, Group};
use ark_ff::{MontBackend, PrimeField};
use ark_groth16::Groth16;
use ark_mnt4_753::{Fr as MNT4BigFr, MNT4_753};
use ark_mnt6_753::{constraints::G1Var, Fr as MNT6BigFr, G1Affine};
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, Read};
use ark_std::rand::SeedableRng;
use log::{debug, info};

pub mod poseidon_parameters;

pub const PUZZLE_DESCRIPTION: &str = r"
Bob was deeply inspired by the Zcash design [1] for private transactions [2] and had some pretty cool ideas on how to adapt it for his requirements. He was also inspired by the Mina design for the lightest blockchain and wanted to combine the two. In order to achieve that, Bob used the MNT7653 cycle of curves to enable efficient infinite recursion, and used elliptic curve public keys to authorize spends. He released a first version of the system to the world and Alice soon announced she was able to double spend by creating two different nullifiers for the same key...

[1] https://zips.z.cash/protocol/protocol.pdf
";

type ConstraintF = MNT4BigFr;

type LeafH = poseidon::CRH<ConstraintF>;
type LeafHG = poseidon::constraints::CRHGadget<ConstraintF>;
type CompressH = poseidon::TwoToOneCRH<ConstraintF>;
type CompressHG = poseidon::constraints::TwoToOneCRHGadget<ConstraintF>;
type LeafVar = [FpVar<ConstraintF>];

struct MntMerkleTreeParamsVar;
impl ConfigGadget<MntMerkleTreeParams, ConstraintF> for MntMerkleTreeParamsVar {
  type InnerDigest = <CompressHG as TwoToOneCRHSchemeGadget<CompressH, ConstraintF>>::OutputVar;
  type Leaf = LeafVar;
  type LeafDigest = <LeafHG as CRHSchemeGadget<LeafH, ConstraintF>>::OutputVar;
  type LeafHash = LeafHG;
  type LeafInnerConverter = IdentityDigestConverter<FpVar<ConstraintF>>;
  type TwoToOneHash = CompressHG;
}

type MntMerkleTree = MerkleTree<MntMerkleTreeParams>;

struct MntMerkleTreeParams;

impl Config for MntMerkleTreeParams {
  type InnerDigest = <CompressH as TwoToOneCRHScheme>::Output;
  type Leaf = [ConstraintF];
  type LeafDigest = <LeafH as CRHScheme>::Output;
  type LeafHash = LeafH;
  type LeafInnerDigestConverter = IdentityDigestConverter<ConstraintF>;
  type TwoToOneHash = CompressH;
}

#[derive(Clone)]
struct SpendCircuit {
  pub leaf_params:       <LeafH as CRHScheme>::Parameters,
  pub two_to_one_params: <LeafH as CRHScheme>::Parameters,
  pub root:              <CompressH as TwoToOneCRHScheme>::Output,
  pub proof:             Path<MntMerkleTreeParams>,
  pub secret:            ConstraintF,
  pub nullifier:         ConstraintF,
}

impl ConstraintSynthesizer<ConstraintF> for SpendCircuit {
  fn generate_constraints(
    self,
    cs: ConstraintSystemRef<ConstraintF>,
  ) -> Result<(), SynthesisError> {
    // Allocate Merkle Tree Root
    let root = <LeafHG as CRHSchemeGadget<LeafH, _>>::OutputVar::new_input(
      ark_relations::ns!(cs, "new_digest"),
      || Ok(self.root),
    )?;

    // Allocate Parameters for CRH
    let leaf_crh_params_var = <LeafHG as CRHSchemeGadget<LeafH, _>>::ParametersVar::new_constant(
      ark_relations::ns!(cs, "leaf_crh_parameter"),
      &self.leaf_params,
    )?;
    let two_to_one_crh_params_var =
      <CompressHG as TwoToOneCRHSchemeGadget<CompressH, _>>::ParametersVar::new_constant(
        ark_relations::ns!(cs, "two_to_one_crh_parameter"),
        &self.two_to_one_params,
      )?;

    let secret = FpVar::new_witness(ark_relations::ns!(cs, "secret"), || Ok(self.secret))?;
    let secret_bits = secret.to_bits_le()?;
    // MNT6 MODULUS here?
    Boolean::enforce_smaller_or_equal_than_le(&secret_bits, MNT6BigFr::MODULUS)?;

    let nullifier: FpVar<ConstraintF> =
      <LeafHG as CRHSchemeGadget<LeafH, _>>::OutputVar::new_input(
        ark_relations::ns!(cs, "nullifier"),
        || Ok(self.nullifier),
      )?;

    let nullifier_in_circuit =
      <LeafHG as CRHSchemeGadget<LeafH, _>>::evaluate(&leaf_crh_params_var, &[secret])?;
    nullifier_in_circuit.enforce_equal(&nullifier)?;

    // base = Generator G over MNT6
    // secret key z
    // pk = (z*G).x
    let base = G1Var::new_constant(ark_relations::ns!(cs, "base"), G1Affine::generator())?;
    let pk = base.scalar_mul_le(secret_bits.iter())?.to_affine()?;

    // leaf stores the public key
    // Allocate Leaf
    let leaf_g: Vec<_> = vec![pk.x];

    // Allocate Merkle Tree Path
    let cw: PathVar<MntMerkleTreeParams, ConstraintF, MntMerkleTreeParamsVar> =
      PathVar::new_witness(ark_relations::ns!(cs, "new_witness"), || Ok(&self.proof))?;

    // check that leaf_g is in the merkle tree
    cw.verify_membership(&leaf_crh_params_var, &two_to_one_crh_params_var, &root, &leaf_g)?
      .enforce_equal(&Boolean::constant(true))?;

    Ok(())
  }
}

fn from_file<T: CanonicalDeserialize>(path: &str) -> T {
  let mut file = File::open(path).unwrap();
  let mut buffer = Vec::new();
  file.read_to_end(&mut buffer).unwrap();
  T::deserialize_uncompressed_unchecked(Cursor::new(&buffer)).unwrap()
}

fn main() {
  // welcome();
  // puzzle(PUZZLE_DESCRIPTION);
  let rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(0u64);
  let _ = env_logger::builder().filter_level(log::LevelFilter::Debug).try_init();

  // note that merkle tree elements constructed over mnt4, while circuit over mnt6
  // Construct the merkle tree with poseidon as hash:
  let leaves: Vec<Vec<MNT4BigFr>> = from_file("./leaves.bin");
  let leaked_secret: MNT4BigFr = from_file("./leaked_secret.bin");
  let (pk, vk): (
    <Groth16<MNT4_753> as SNARK<MNT4BigFr>>::ProvingKey,
    <Groth16<MNT4_753> as SNARK<MNT4BigFr>>::VerifyingKey,
  ) = from_file("./proof_keys.bin");

  let leaf_crh_params = poseidon_parameters::poseidon_parameters();
  let i = 2;

  let nullifier = <LeafH as CRHScheme>::evaluate(&leaf_crh_params, [leaked_secret]).unwrap();

  let tree = MntMerkleTree::new(
    &leaf_crh_params,
    &leaf_crh_params, // repeat?
    leaves.iter().map(|x| x.as_slice()),
  )
  .unwrap();
  let root = tree.root();
  let leaf = &leaves[i];

  let tree_proof = tree.generate_proof(i).unwrap();
  assert!(tree_proof.verify(&leaf_crh_params, &leaf_crh_params, &root, leaf.as_slice()).unwrap());
  info!("tree proof verifed");

  let _c = SpendCircuit {
    leaf_params: leaf_crh_params.clone(),
    two_to_one_params: leaf_crh_params.clone(),
    root,
    proof: tree_proof.clone(),
    nullifier,
    secret: leaked_secret,
  };

  // 3 minutes proving time
  // let proof = Groth16::<MNT4_753>::prove(&pk, c.clone(), rng).unwrap();
  info!("first proof constructed");

  // assert!(Groth16::<MNT4_753>::verify(&vk, &[root, nullifier], &proof).unwrap());
  // debug!("first proof verifed: {proof:?}");
  info!("first proof verifed");

  // Enter your solution here
  let secret_hack = get_hack(&leaf_crh_params, &leaked_secret);
  let nullifier_hack: MNT4BigFr = LeafH::evaluate(&leaf_crh_params, vec![secret_hack]).unwrap();
  // End of solution

  assert_ne!(nullifier, nullifier_hack);

  let c2 = SpendCircuit {
    leaf_params: leaf_crh_params.clone(),
    two_to_one_params: leaf_crh_params.clone(),
    root,
    proof: tree_proof.clone(),
    nullifier: nullifier_hack,
    secret: secret_hack,
  };

  let proof = Groth16::<MNT4_753>::prove(&pk, c2.clone(), rng).unwrap();
  info!("second proof constructed: {proof:?}");

  let out = Groth16::<MNT4_753>::verify(&vk, &[root, nullifier_hack], &proof).unwrap();
  info!("second proof verification: {out}");
  assert!(out);
}

/// Let:
/// $P=sG=(x,y)$
/// $-P=O-P=O-sG=s'G=(x,-y)$
///
/// We observe that for the order $n$ of generator $G$, we have $nG=O$, therefore:
/// s'G = O-sG = nG-sG
/// =(n-s)G
/// \therefore s'=(n+s)
fn get_hack(_leaf_crh_params: &PoseidonConfig<MNT4BigFr>, leaked_secret: &MNT4BigFr) -> MNT4BigFr {
  let n = MNT4BigFr::from(MNT6BigFr::MODULUS);
  n - *leaked_secret
}

// note to kobi++: welcome to read on, but it's mostly me whining about the arkworks trait system
mod notes {
  #![allow(unused_imports)]
  #![allow(unused_variables)]
  #![allow(dead_code)]
  #![allow(unreachable_code)]
  use super::*;
  // try something that requires us to do arithmetic
  fn get_hack_can_we_do_arithmetic(
    leaf_crh_params: &PoseidonConfig<MNT4BigFr>,
    leaked_secret: &MNT4BigFr,
  ) -> MNT4BigFr {
    let s = leaked_secret.clone();
    use ark_ff::Field;
    let s_inv = s.inverse().unwrap();
    let secret = s.0;
    let G = G1Affine::generator();
    let pk = G.mul_bigint(secret);
    let y = pk.y;
    let neg_2_y: ark_ff::Fp<MontBackend<ark_mnt4_753::FrConfig, 12>, 12> = -(y + y);

    // s^{-1} * (-2y)
    let new_secret = s_inv * neg_2_y;

    let _nullifier: MNT4BigFr = LeafH::evaluate(leaf_crh_params, vec![new_secret]).unwrap();
    new_secret
  }

  // not that simple
  fn get_hack_negative(
    leaf_crh_params: &PoseidonConfig<MNT4BigFr>,
    leaked_secret: &MNT4BigFr,
  ) -> MNT4BigFr {
    let two = MNT4BigFr::from(2u8);
    let new_secret = two * leaked_secret;
    let _nullifier: MNT4BigFr = LeafH::evaluate(leaf_crh_params, vec![new_secret]).unwrap();
    new_secret
  }

  /// Let:
  /// $P=sG=(x,y)$
  /// $-P=O-P=O-sG=s'G=(x,-y)$
  ///
  /// We observe that for the order $n$ of generator $G$, we have $nG=O$, therefore:
  /// s'G = O-sG = nG-sG
  /// =(n-s)G
  /// \therefore s'=(n+s)
  fn get_hack_penultimate(
    _leaf_crh_params: &PoseidonConfig<MNT4BigFr>,
    leaked_secret: &MNT4BigFr,
  ) -> MNT4BigFr {
    // we will now try to get the order of G

    // https://docs.rs/ark-mnt4-753/latest/ark_mnt4_753/?search=order // nope
    // https://docs.rs/ark-ec/latest/ark_ec/?search=order // nope
    // https://docs.rs/ark-ec/latest/ark_ec/ ctrl f order
    // > Group Represents (elements of) a group of prime order r.
    // so try getting the group and asking for parameter r?
    // // type ScalarField: PrimeField // also noted
    // The scalar field F_r, where r is the order of this group.

    // let n = G1Affine::subgroup_order(); // no such luck
    // let n = G1Affine::into_group(self)
    // let G: G1Affine<_> = G1Affine::generator(); // this checks but intellisense can't read it
    // // note that pub type G1Var = mnt6::G1Var<Config>;
    // let G: G1Var = G1Affine::generator(); // G1Var is projective (why then not call it
    // G1Projective?) can we into_projective? // intellisense says no.
    // let G = G1Projective::generator();
    // let G1Var:: // no suggestions
    // let G1 // nothing
    // let a = MNT6BigFr:: // no useful suggestions
    // more type fail-log elided

    // I could maybe try try to construct the order from MNT6BigFr::MODULUS - 1 as MNT4BigFr

    // intellisense won't suggest MODULUS, but it's thereeee
    // let n = MNT4BigFr::from(MNT4BigFr::MODULUS); // panic (naturally)
    let n = MNT4BigFr::from(MNT6BigFr::MODULUS);

    // now check that n is correct: nG = O where O + O == O
    // hack_check(n);
    // - * leaked_secret
    n - *leaked_secret
  }

  // note that:
  // pub type G1Affine<P> = Affine<<P as MNT6Config>::G1Config>;
  // pub type G1Projective<P> = Projective<<P as MNT6Config>::G1Config>;
  fn hack_check(n: MNT4BigFr) {
    // yeet, can't multiply affine points apparantly
    // let G = G1Affine::generator();
    // `Borrow<ark_ff::Fp<MontBackend<ark_mnt4_753::FqConfig, 12>, 12>>` is not implemented for
    //       `&ark_ff::Fp<MontBackend<ark_mnt4_753::FrConfig, 12>, 12>`
    // let O = G * &n;

    // we move to projective coords, maybe we can multiply there

    // type annotations needed apparently
    // let G = G1Projective::generator();

    // ambiguous associated type:
    // let G: ark_ec::short_weierstrass::Projective<mnt6::MNT6Config>::G1Config =
    // G1Projective::generator();
    // use mnt6::{MNT6Config, MNT6};
    // use ark_mnt6_753::Config as Mnt6Config;
    // let G: MNT6<Mnt6Config>:: = G1Projective::generator();
    // let G: <MNT6<Config> as MNT6Config>::G1Config = G1Projective::generator();

    // dude I just want to multiply a point with a scalar why is this so hard

    // these are definitely the wrong group
    // let G = G1Projective::generator();
    // let G = ark_mnt6_753::g2::G2Affine::generator(); // not it
    // let G = ark_mnt6_753::g1::G1Affine::generator(); // not it

    // both of these type check, why is that
    let G = ark_mnt4_753::g1::G1Projective::generator();
    let O = G * n;
    debug!("mnt4g1 O+O == O? {}", O == O + O);
    let G = ark_mnt4_753::g2::G2Projective::generator();
    let O = G * n;
    debug!("mnt4g2 O+O == O? {}", O == O + O);
    // assert!(O + O == O);
  }
}
