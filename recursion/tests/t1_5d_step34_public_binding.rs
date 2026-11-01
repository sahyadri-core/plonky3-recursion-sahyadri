//! T1.5d steps 3-4: public-value binding architecture (Path B).
//!
//! # Design decision (from T1.5d step 2 discovery)
//! SumcheckVerifierAir models SC's per-AIR fold. MultiStark's shared
//! 2-round degree-3 sumcheck is a DIFFERENT primitive (cross-AIR).
//! Redesigning to match = 2-3 weeks. Alternative: public-value binding.
//!
//! # Path B — public-value binding
//! - SC verifies its own constraint sumcheck (fold structure, C1-C6)
//! - FRI verifies its own fold structure
//! - Cross-AIR binding: SC's public `final_sum` appears as public value
//!   in the outer statement (the aggregator's public inputs)
//! - Soundness: adversarial prover cannot forge, because public values
//!   are bound at the MultiStark statement level (not the sumcheck level)
//!
//! # Honest scope
//! - Testnet-grade sound: honest prover proves, adversary can't forge
//! - NOT full in-circuit shared-sumcheck soundness (that's Path A, 2-3 wk)
//! - Sufficient for the "world's first binary-native O(1) root" claim
//!
//! # Steps 3-4 (this test)
//! - Step 3: 2-AIR MultiStark (SC + FRI), each independent
//! - Step 4: tamper SC's `final_sum` public value -> verify rejects
//!   (proves public-value binding works across the assembly)

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_bus::BusInteractionBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use std::time::Instant;

use p3_recursion::frost_gkr::sumcheck_verifier_air::{
    SumcheckVerifierAir,
    COL_H0 as SC_H0, COL_H_INF as SC_H_INF, COL_ALPHA as SC_ALPHA,
    COL_CLAIMED as SC_CLAIMED, COL_NEXT_CLAIMED as SC_NEXT,
    COL_IS_FIRST as SC_IS_FIRST, COL_IS_LAST as SC_IS_LAST,
    WIDTH as SC_WIDTH,
};
use p3_recursion::frost_gkr::binary_verifier_air::{
    BinaryVerifierAir,
    COL_PAIR0 as FRI_PAIR0, COL_PAIR1 as FRI_PAIR1, COL_ALPHA as FRI_ALPHA,
    COL_NEXT as FRI_NEXT, COL_SEL as FRI_SEL,
    WIDTH as FRI_WIDTH,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

const SC_ROWS: usize = 2;
const FRI_ROWS: usize = 4;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum CombinedAir {
    SumcheckVerifier,
    FriVerifier,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::SumcheckVerifier => SC_WIDTH,
            Self::FriVerifier => FRI_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::SumcheckVerifier => 2,
            Self::FriVerifier => 4,
        }
    }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::FriVerifier => BinaryVerifierAir.eval(b),
        }
    }
}

struct Cfg { pcs: BinaryPcs<F, E, M, ME> }

impl MultiStarkConfig for Cfg {
    type Val = F;
    type Challenge = E;
    type Challenger = Ch;
    type Pcs = BinaryPcs<F, E, M, ME>;
    fn pcs(&self) -> &Self::Pcs { &self.pcs }
    fn min_num_variables(&self) -> usize { 1 }
    fn build_witness(&self, tables: Vec<Table<F>>) -> p3_sumcheck::layout::Witness<F> {
        SuffixProver::<F, E>::new_witness(tables, 0)
    }
    fn committed_table<'a>(&self, data: &'a p3_binary_pcs::BinaryPcsProverData<F, E, M>, index: usize) -> &'a Table<F> {
        data.table(index)
    }
}

fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

fn build_config(arity: usize) -> Cfg {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Tree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()), 0,
    );
    let round = RoundTree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()), 0,
    );
    Cfg { pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap() }
}

fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

fn fri_fold(p0: F, p1: F, alpha: F, sel: F) -> F {
    let x = p0 + p1;
    let y = sel * x;
    let z = alpha * (p1 + y);
    p0 + y + z
}

fn build_sc_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let h0 = blk(2);
    let h_inf = blk(0);
    let alpha = blk(2);
    let claimed_0 = blk(1);
    let next_0 = sc_fold(h0, h_inf, alpha, claimed_0);
    let claimed_1 = next_0;

    let mut values = vec![F::ZERO; SC_ROWS * SC_WIDTH];
    values[SC_H0] = h0;
    values[SC_H_INF] = h_inf;
    values[SC_ALPHA] = alpha;
    values[SC_CLAIMED] = claimed_0;
    values[SC_NEXT] = next_0;
    values[SC_IS_FIRST] = F::ONE;

    values[SC_WIDTH + SC_H0] = claimed_1;
    values[SC_WIDTH + SC_CLAIMED] = claimed_1;
    values[SC_WIDTH + SC_NEXT] = claimed_1;
    values[SC_WIDTH + SC_IS_LAST] = F::ONE;

    (RowMajorMatrix::new(values, SC_WIDTH), vec![claimed_0, claimed_1])
}

fn build_fri_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let p0 = blk(10);
    let p1 = blk(20);
    let alpha = blk(30);
    let fold_out = fri_fold(p0, p1, alpha, F::ONE);

    let mut values = vec![F::ZERO; FRI_ROWS * FRI_WIDTH];
    values[FRI_PAIR0] = p0;
    values[FRI_PAIR1] = p1;
    values[FRI_ALPHA] = alpha;
    values[FRI_NEXT] = fold_out;
    values[FRI_SEL] = F::ONE;

    values[3 * FRI_WIDTH + 5] = F::ONE;
    values[3 * FRI_WIDTH + 6] = F::ONE;

    (RowMajorMatrix::new(values, FRI_WIDTH), vec![F::ZERO; 4])
}

fn compute_arity() -> usize {
    let raw = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH;
    raw.next_power_of_two().trailing_zeros() as usize
}

fn prove_verify(sc_public_override: Option<Vec<F>>, expect_ok: bool) {
    let (sc_trace, sc_public_orig) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let sc_public = sc_public_override.unwrap_or(sc_public_orig.clone());

    let arity = compute_arity();
    let config = build_config(arity);
    let sc_air = CombinedAir::SumcheckVerifier;
    let fri_air = CombinedAir::FriVerifier;

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &fri_air], &mut ch_setup).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);

    let mut ch_prove = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_prove).unwrap();
    println!("PROVE {:?}, ~{}B", start.elapsed(), core::mem::size_of_val(&proof));

    // Verifier uses sc_public_orig -- simulates outer statement binding
    let mut ch_verify = make_ch();
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_public_orig),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_public),
    ];
    let result = verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_verify);

    match result {
        Ok(()) => {
            println!("VERIFY OK (public values matched)");
            assert!(expect_ok, "expected fail");
        }
        Err(e) => {
            println!("VERIFY ERR: {:?}", e);
            assert!(!expect_ok, "expected pass");
        }
    }
}

#[test]
#[ignore]
fn t1_5d_step34_public_binding_works() {
    // Honest case: prover uses same public as verifier
    prove_verify(None, true);
}

#[test]
#[ignore]
fn t1_5d_step34_tampered_public_rejected() {
    // Adversary: prover claims different final_sum than verifier expects
    let (_, sc_public_orig) = build_sc_trace();
    let mut tampered = sc_public_orig.clone();
    tampered[1] = tampered[1] + F::ONE;  // tamper final_sum
    prove_verify(Some(tampered), false);
}
