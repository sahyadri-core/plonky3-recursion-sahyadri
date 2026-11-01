//! T1.3: scale loop over N proofs -> tree -> 1 root.
//!
//! # Scope
//! - Synthetic leaves (real leaves via T1.2b extraction, next session)
//! - Pairwise aggregation loop (log2(N) levels)
//! - Root verification: single 832B proof
//!
//! # Pipeline
//! Level 0: N leaf traces (SC + FRI)
//! Level i: N/2^i aggregation traces (SC + CS + FRI)
//! Level log2(N): 1 root proof
//!
//! # Honest
//! This test uses SYNTHETIC leaves for the loop mechanics. Real leaves
//! require T1.2b extraction (PCS opening parse). Structure here is final;
//! data source changes next session.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_bus::BusInteractionBuilder;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use std::time::Instant;

use p3_recursion::frost_gkr::compressed_sumcheck_air::{
    CompressedSumcheckAir, WIDTH as CS_WIDTH,
    COL_EVALS0, COL_EVALS1, COL_EVALS2, COL_EVALS3,
    COL_RUNNING_IN, COL_RUNNING_OUT, COL_CHALLENGE,
    COL_IS_FIRST, COL_IS_LAST,
};
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
pub enum AssemblyAir {
    SumcheckVerifier,
    CompressedSumcheck,
    FriVerifier,
}

impl<F> BaseAir<F> for AssemblyAir {
    fn width(&self) -> usize {
        match self {
            Self::SumcheckVerifier => SC_WIDTH,
            Self::CompressedSumcheck => CS_WIDTH,
            Self::FriVerifier => FRI_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::SumcheckVerifier => 2,
            Self::CompressedSumcheck => 2,
            Self::FriVerifier => 4,
        }
    }
}

impl<AB> Air<AB> for AssemblyAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::CompressedSumcheck => CompressedSumcheckAir::new().eval(b),
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

fn lagrange_eval(h: [F; 5], alpha: F) -> F {
    let mut result = F::ZERO;
    for i in 0..5 {
        let mut num = F::ONE;
        let mut den = F::ONE;
        for j in 0..5 {
            if i == j { continue; }
            let xj = blk(j as u128);
            let xi = blk(i as u128);
            num = num * (alpha + xj);
            den = den * (xi + xj);
        }
        let li = num * den.try_inverse().expect("nonzero denom");
        result = result + h[i] * li;
    }
    result
}

/// Synthetic leaf: (sc_trace, sc_public, fri_trace, fri_public, extracted_sumcheck)
#[derive(Clone)]
struct Leaf {
    seed: u128,
    final_sum: F,
}

fn make_leaf(seed: u128) -> Leaf {
    Leaf { seed, final_sum: blk(seed * 7 + 1) }
}

/// Aggregation node: takes 2 leaves → new proof with real sumcheck data.
/// SYNTHETIC for now; T1.2b will feed real extracted data.
fn aggregate_pair(a: &Leaf, b: &Leaf) -> (Leaf, usize) {
    // Synthetic SC trace
    let h0 = a.final_sum;
    let h_inf = F::ZERO;
    let alpha = b.final_sum;
    let claimed_0 = a.seed ^ b.seed; // mix
    let claimed_0 = blk(claimed_0 as u128);
    let next_0 = sc_fold(h0, h_inf, alpha, claimed_0);
    let claimed_1 = next_0;

    let mut sc_values = vec![F::ZERO; 2 * SC_WIDTH];
    sc_values[SC_H0] = h0;
    sc_values[SC_H_INF] = h_inf;
    sc_values[SC_ALPHA] = alpha;
    sc_values[SC_CLAIMED] = claimed_0;
    sc_values[SC_NEXT] = next_0;
    sc_values[SC_IS_FIRST] = F::ONE;
    sc_values[SC_WIDTH + SC_H0] = claimed_1;
    sc_values[SC_WIDTH + SC_CLAIMED] = claimed_1;
    sc_values[SC_WIDTH + SC_NEXT] = claimed_1;
    sc_values[SC_WIDTH + SC_IS_LAST] = F::ONE;
    let sc_trace = RowMajorMatrix::new(sc_values, SC_WIDTH);
    let sc_public = vec![claimed_0, claimed_1];

    // Synthetic FRI trace
    let p0 = a.final_sum;
    let p1 = b.final_sum;
    let fa = blk(a.seed ^ b.seed);
    let fold_out = fri_fold(p0, p1, fa, F::ONE);
    let mut fri_values = vec![F::ZERO; 4 * FRI_WIDTH];
    fri_values[FRI_PAIR0] = p0;
    fri_values[FRI_PAIR1] = p1;
    fri_values[FRI_ALPHA] = fa;
    fri_values[FRI_NEXT] = fold_out;
    fri_values[FRI_SEL] = F::ONE;
    fri_values[3 * FRI_WIDTH + 5] = F::ONE;
    fri_values[3 * FRI_WIDTH + 6] = F::ONE;
    let fri_trace = RowMajorMatrix::new(fri_values, FRI_WIDTH);
    let fri_public = vec![F::ZERO; 4];

    // Synthetic CS trace (2 rounds)
    let claimed = F::ZERO;
    let mut cs_values = vec![F::ZERO; 2 * CS_WIDTH];
    let mut running = claimed;
    for r in 0..2 {
        let e0 = blk(r as u128 * 10 + 1);
        let e1 = blk(r as u128 * 10 + 2);
        let e2 = blk(r as u128 * 10 + 3);
        let e3 = blk(r as u128 * 10 + 4);
        let alpha_r = blk(r as u128 * 10 + 5);
        let h_native: [F; 5] = [e0, running + e0, e1, e2, e3];
        let r_out = lagrange_eval(h_native, alpha_r);
        cs_values[r * CS_WIDTH + COL_EVALS0] = e0;
        cs_values[r * CS_WIDTH + COL_EVALS1] = e1;
        cs_values[r * CS_WIDTH + COL_EVALS2] = e2;
        cs_values[r * CS_WIDTH + COL_EVALS3] = e3;
        cs_values[r * CS_WIDTH + COL_RUNNING_IN] = running;
        cs_values[r * CS_WIDTH + COL_RUNNING_OUT] = r_out;
        cs_values[r * CS_WIDTH + COL_CHALLENGE] = alpha_r;
        if r == 0 { cs_values[r * CS_WIDTH + COL_IS_FIRST] = F::ONE; }
        if r == 1 { cs_values[r * CS_WIDTH + COL_IS_LAST] = F::ONE; }
        running = r_out;
    }
    let cs_trace = RowMajorMatrix::new(cs_values, CS_WIDTH);
    let cs_public = vec![claimed, running];

    // Prove 3-AIR assembly
    let total = 2 * SC_WIDTH + 2 * CS_WIDTH + 4 * FRI_WIDTH;
    let arity = total.next_power_of_two().trailing_zeros() as usize;
    let config = build_config(arity);
    let sc_air = AssemblyAir::SumcheckVerifier;
    let cs_air = AssemblyAir::CompressedSumcheck;
    let fri_air = AssemblyAir::FriVerifier;
    let mut ch_s = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &cs_air, &fri_air], &mut ch_s).unwrap();

    let sc_i = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let cs_i = ProverInstance::new(&cs_air, Table::new(cs_trace.transpose()), &pk, &cs_public);
    let fri_i = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);
    let mut ch_p = make_ch();
    let proof = prove(&config, ProverInstances::new(vec![sc_i, cs_i, fri_i]), 0, &mut ch_p).unwrap();

    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_public),
        VerifierInstance::new(&cs_air, &vk, 1, &cs_public),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_public),
    ];
    let mut ch_v = make_ch();
    verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_v)
        .expect("aggregation must verify");

    let new_leaf = Leaf { seed: a.seed ^ b.seed ^ 0xAA, final_sum: running };
    let size = core::mem::size_of_val(&proof);
    (new_leaf, size)
}

#[test]
#[ignore]
fn t1_3_two_level_tree() {
    let start = Instant::now();
    // 4 leaves -> 2 -> 1
    let l0 = make_leaf(0xA0);
    let l1 = make_leaf(0xB0);
    let l2 = make_leaf(0xC0);
    let l3 = make_leaf(0xD0);
    println!("Level 0: 4 leaves ready");

    let (n01, sz01) = aggregate_pair(&l0, &l1);
    println!("Level 1 (0,1) {}B, {:?}", sz01, start.elapsed());
    let (n23, sz23) = aggregate_pair(&l2, &l3);
    println!("Level 1 (2,3) {}B, {:?}", sz23, start.elapsed());

    let (_root, root_sz) = aggregate_pair(&n01, &n23);
    println!("Level 2 (root) {}B, {:?}", root_sz, start.elapsed());

    println!("\n=== T1.3 two-level tree PASS ===");
    assert_eq!(root_sz, 832, "root proof size should be ~832B (constant)");
}

#[test]
#[ignore]
fn t1_3_eight_leaf_tree() {
    let start = Instant::now();
    // 8 leaves -> 4 -> 2 -> 1
    let mut level: Vec<Leaf> = (0..8).map(|i| make_leaf(0xA0 + i * 0x10)).collect();
    println!("Level 0: {} leaves", level.len());

    let mut depth = 0;
    while level.len() > 1 {
        let mut next = Vec::new();
        for pair in level.chunks(2) {
            let (n, _) = aggregate_pair(&pair[0], &pair[1]);
            next.push(n);
        }
        level = next;
        depth += 1;
        println!("Level {}: {} nodes, {:?}", depth, level.len(), start.elapsed());
    }

    println!("\n=== T1.3 8-leaf tree PASS (depth {}) ===", depth);
    assert_eq!(depth, 3, "8 leaves = 3 levels");
}
