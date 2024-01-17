#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unreachable_code)]
use std::{fs::File, io::Cursor};

use ark_crypto_primitives::{
  crh::{poseidon, TwoToOneCRHScheme, *},
  merkle_tree::{constraints::*, Config, MerkleTree, Path, *},
  snark::SNARK,
  sponge::poseidon::PoseidonConfig,
};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use ark_groth16::Groth16;
use ark_mnt4_753::{Fr as MNT4BigFr, MNT4_753};
use ark_mnt6_753::{constraints::G1Var, Fr as MNT6BigFr, G1Affine};
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, Read};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use log::{debug, info};
use prompt::{puzzle, welcome};

pub mod poseidon_parameters;

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
    //
    // inverse attempt, try:
    // pk = ((-z) * G).x
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

  // note that merkle tree elements constructed over mnt4, while circuit over mnt6?
  //
  // Construct the merkle tree with poseidon as hash:
  let leaves: Vec<Vec<MNT4BigFr>> = from_file("./leaves.bin");
  let leaked_secret: MNT4BigFr = from_file("./leaked_secret.bin");
  let (pk, vk): (
    <Groth16<MNT4_753> as SNARK<MNT4BigFr>>::ProvingKey,
    <Groth16<MNT4_753> as SNARK<MNT4BigFr>>::VerifyingKey,
  ) = from_file("./proof_keys.bin");

  let leaf_crh_params = poseidon_parameters::poseidon_parameters();
  let i = 2;
  // let leaf_crh_params = leaf_crh_params.clone();

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

  let c = SpendCircuit {
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
  // we will generate a faulty secret, that satisfy the same tree proof for leaf at
  // index 2
  let (nullifier_hack, secret_hack) = get_hack(&leaf_crh_params, &leaked_secret);
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

fn get_hack(
  leaf_crh_params: &PoseidonConfig<MNT4BigFr>,
  leaked_secret: &MNT4BigFr,
) -> (MNT4BigFr, MNT4BigFr) {
  let new_secret: MNT4BigFr = -*leaked_secret;
  let nullifier: MNT4BigFr = LeafH::evaluate(leaf_crh_params, vec![new_secret]).unwrap();
  (nullifier, new_secret)
}

// not that simple
fn get_hack_negative(
  leaf_crh_params: &PoseidonConfig<MNT4BigFr>,
  leaked_secret: &MNT4BigFr,
) -> (MNT4BigFr, MNT4BigFr) {
  let new_secret: MNT4BigFr = -*leaked_secret;
  let nullifier: MNT4BigFr = LeafH::evaluate(leaf_crh_params, vec![new_secret]).unwrap();
  (nullifier, new_secret)
}

// base = Generator G over MNT6
// secret key z
// pk = (z*G).x
//
// inverse attempt, try:
// pk = ((-z) * G).x

// use ark_ec::pairing::Pairing;
// use ark_std::UniformRand;
// let new_secret: MNT4BigFr = MNT4BigFr::rand(rng);

// let g1: G1Affine = ark_mnt6_753::G1Affine::generator();
// //   let pairing = ark_mnt6_753::MNT6_753::pairing(&g1, &new_secret);

const PUZZLE_DESCRIPTION: &str = r"
Bob was deeply inspired by the Zcash design [1] for private transactions [2] and had some pretty cool ideas on how to adapt it for his requirements. He was also inspired by the Mina design for the lightest blockchain and wanted to combine the two. In order to achieve that, Bob used the MNT7653 cycle of curves to enable efficient infinite recursion, and used elliptic curve public keys to authorize spends. He released a first version of the system to the world and Alice soon announced she was able to double spend by creating two different nullifiers for the same key...

[1] https://zips.z.cash/protocol/protocol.pdf
";
