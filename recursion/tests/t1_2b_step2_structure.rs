//! T1.2b step 2: inspect opened_values structure (arity, pairs, indices).
//!
//! # Goal
//! After T1.2b step 1 showed:
//!   - 6 rounds, 122 queries, per-round: 122 rows x 1 col
//!
//! Now inspect deeper:
//!   - What do the F values look like per round?
//!   - Is arity 1 (2 symbols/coset) or 2 (4 symbols/coset)?
//!   - What's the index pattern (i_0 shift per round)?
//!   - Can we directly feed our BinaryVerifierAir (arity 1)?
//!
//! # Decision criteria (post-inspection)
//! - If arity 1: reuse BinaryVerifierAir, build trace directly
//! - If arity 2+: need BinaryVerifierAirV2 (new AIR, +2-3 days)
//!
//! # NOT in scope (yet)
//! - Alpha derivation from transcript (mainnet task)
//! - Actual trace build (this informs next session)

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_bus::BusInteractionBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, ProverInstance, ProverInstances};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;

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

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum SrcAir {
    SumcheckVerifier,
    FriVerifier,
}

impl<F> BaseAir<F> for SrcAir {
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

impl<AB> Air<AB> for SrcAir
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
    let mmcs = Tree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    let round = RoundTree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    Cfg { pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap() }
}

fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

fn fri_fold(p0: F, p1: F, alpha: F, sel: F) -> F {
    let x = p0 + p1; let y = sel * x; let z = alpha * (p1 + y); p0 + y + z
}

fn build_sc_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let h0 = blk(2); let h_inf = blk(0); let alpha = blk(2);
    let claimed_0 = blk(1);
    let next_0 = sc_fold(h0, h_inf, alpha, claimed_0);
    let claimed_1 = next_0;
    let mut v = vec![F::ZERO; 2 * SC_WIDTH];
    v[SC_H0] = h0; v[SC_H_INF] = h_inf; v[SC_ALPHA] = alpha;
    v[SC_CLAIMED] = claimed_0; v[SC_NEXT] = next_0; v[SC_IS_FIRST] = F::ONE;
    v[SC_WIDTH + SC_H0] = claimed_1; v[SC_WIDTH + SC_CLAIMED] = claimed_1;
    v[SC_WIDTH + SC_NEXT] = claimed_1; v[SC_WIDTH + SC_IS_LAST] = F::ONE;
    (RowMajorMatrix::new(v, SC_WIDTH), vec![claimed_0, claimed_1])
}

fn build_fri_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let p0 = blk(10); let p1 = blk(20); let alpha = blk(30);
    let fo = fri_fold(p0, p1, alpha, F::ONE);
    let mut v = vec![F::ZERO; 4 * FRI_WIDTH];
    v[FRI_PAIR0] = p0; v[FRI_PAIR1] = p1; v[FRI_ALPHA] = alpha;
    v[FRI_NEXT] = fo; v[FRI_SEL] = F::ONE;
    v[3 * FRI_WIDTH + 5] = F::ONE; v[3 * FRI_WIDTH + 6] = F::ONE;
    (RowMajorMatrix::new(v, FRI_WIDTH), vec![F::ZERO; 4])
}

#[test]
#[ignore]
fn inspect_opened_values_structure() {
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let raw = 2 * SC_WIDTH + 4 * FRI_WIDTH;
    let arity = raw.next_power_of_two().trailing_zeros() as usize;

    let config = build_config(arity);
    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;
    let mut ch_s = make_ch();
    let (pk, _vk) = setup(&config, &[&sc_air, &fri_air], &mut ch_s).unwrap();
    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);
    let mut ch_p = make_ch();
    let proof = prove(&config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_p).unwrap();

    let opening = &proof.opening;

    println!("=== Detailed opened_values structure ===");
    println!("Total rounds: {}", opening.rounds.len());
    println!("Total queries: {}", opening.rounds[0].opened_values.len());

    // Structure of opened_values per round
    for r in 0..opening.rounds.len() {
        let rp = &opening.rounds[r];
        println!("\n--- Round {} ---", r);
        println!("  rows (queries): {}", rp.opened_values.len());
        println!("  cols (arities): {}", rp.opened_values[0].len());
    }

    // Deep inspect first query, first round
    println!("\n=== Deep inspect: query[0] across all rounds ===");
    for r in 0..opening.rounds.len() {
        let vals = &opening.rounds[r].opened_values[0];
        println!("  round[{}] query[0] = {:?}", r, vals);
    }

    // Second query, compare
    if opening.rounds[0].opened_values.len() > 1 {
        println!("\n=== Deep inspect: query[1] across all rounds ===");
        for r in 0..opening.rounds.len() {
            let vals = &opening.rounds[r].opened_values[1];
            println!("  round[{}] query[1] = {:?}", r, vals);
        }
    }

    // Base opened values
    println!("\n=== base_opened_values ===");
    println!("Total base queries: {}", opening.base_opened_values.len());
    if !opening.base_opened_values.is_empty() {
        println!("base_opened_values[0] = {:?}", opening.base_opened_values[0]);
    }

    // Final codeword
    println!("\n=== final_codeword ===");
    println!("(Poly<EF> — shape via internal access if available)");

    // Key insight: what does the fold look like?
    println!("\n=== INFERENCE ===");
    let one_row = &opening.rounds[0].opened_values[0];
    if one_row.len() == 1 {
        println!("opened_values[0] has 1 column -> arity 1 fold (2 symbols per pair)");
        println!("Our BinaryVerifierAir (arity 1) is the RIGHT match");
    } else if one_row.len() == 4 {
        println!("opened_values[0] has 4 columns -> arity 2 fold (4 symbols per coset)");
        println!("Need BinaryVerifierAirV2 (arity 2)");
    } else {
        println!("opened_values[0] has {} columns - UNKNOWN arity", one_row.len());
    }

    println!("\n=== T1.2b step 2 INSPECTION PASS ===");
}
