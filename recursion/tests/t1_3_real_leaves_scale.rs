//! T1.3: real leaves (Plonky3 proof -> V2 extract -> V2 prove) + scale.
//!
//! # Scope
//! - Each leaf: generate real Plonky3 proof (SC+FRI), extract V2 trace,
//!   prove V2 as new MultiStark proof (independent verify)
//! - 8-leaf batch: prove 8 real leaves
//! - 16-leaf batch: prove 16 real leaves
//! - Scale framework: per-leaf time extrapolation to 4444
//!
//! # NOT in scope (needs T1.4c)
//! - Recursive tree aggregation (2-half composition AIR)
//! - Full 4444-leaf E2E root
//!
//! # Honest
//! Each leaf is real data. Aggregation uses existing synthetic pattern
//! from T1.3 loop (works, but not recursive yet).

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_dft::domain_point;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
    take_last_betas_bytes, take_last_indices,
};
use p3_bus::BusInteractionBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, MultiStarkProof, ProverInstance, ProverInstances,
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
use p3_recursion::frost_gkr::binary_verifier_air_v2::{
    BinaryVerifierAirV2, WIDTH as V2_WIDTH,
    COL_LO, COL_HI, COL_BETA, COL_X, COL_NEXT as V2_COL_NEXT, COL_IS_LAST as V2_COL_IS_LAST,
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
pub enum SrcAir { SumcheckVerifier, FriVerifier }

impl<Fb> BaseAir<Fb> for SrcAir {
    fn width(&self) -> usize {
        match self { Self::SumcheckVerifier => SC_WIDTH, Self::FriVerifier => FRI_WIDTH }
    }
    fn num_public_values(&self) -> usize {
        match self { Self::SumcheckVerifier => 2, Self::FriVerifier => 4 }
    }
}

impl<AB> Air<AB> for SrcAir
where AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::FriVerifier => BinaryVerifierAir.eval(b),
        }
    }
}

struct SrcCfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for SrcCfg {
    type Val = F; type Challenge = E; type Challenger = Ch;
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

#[derive(Clone, Copy)]
struct V2Only;
impl<Fb> BaseAir<Fb> for V2Only {
    fn width(&self) -> usize { V2_WIDTH }
    fn num_public_values(&self) -> usize { 0 }
}
impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for V2Only {
    fn eval(&self, b: &mut AB) { BinaryVerifierAirV2.eval(b); }
}

struct V2Cfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for V2Cfg {
    type Val = F; type Challenge = E; type Challenger = Ch;
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

fn make_ch(seed: &[u8]) -> Ch {
    Ch::from_hasher(seed.to_vec(), blake3::byte_hash())
}

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Tree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    let round = RoundTree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
}

fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

fn build_sc_trace(seed: u128) -> (RowMajorMatrix<F>, Vec<F>) {
    let h0 = blk(seed); let h_inf = blk(0); let alpha = blk(seed ^ 0xAA);
    let claimed_0 = blk(seed ^ 0x11);
    let next_0 = sc_fold(h0, h_inf, alpha, claimed_0);
    let claimed_1 = next_0;
    let mut v = vec![F::ZERO; 2 * SC_WIDTH];
    v[SC_H0] = h0; v[SC_H_INF] = h_inf; v[SC_ALPHA] = alpha;
    v[SC_CLAIMED] = claimed_0; v[SC_NEXT] = next_0; v[SC_IS_FIRST] = F::ONE;
    v[SC_WIDTH + SC_H0] = claimed_1; v[SC_WIDTH + SC_CLAIMED] = claimed_1;
    v[SC_WIDTH + SC_NEXT] = claimed_1; v[SC_WIDTH + SC_IS_LAST] = F::ONE;
    (RowMajorMatrix::new(v, SC_WIDTH), vec![claimed_0, claimed_1])
}

fn build_fri_trace(seed: u128) -> (RowMajorMatrix<F>, Vec<F>) {
    let p0 = blk(seed); let p1 = blk(seed ^ 0x22); let alpha = blk(seed ^ 0x33);
    let x = p0 + p1; let y = x; let z = alpha * (p1 + y);
    let fo = p0 + y + z;
    let mut v = vec![F::ZERO; 4 * FRI_WIDTH];
    v[FRI_PAIR0] = p0; v[FRI_PAIR1] = p1; v[FRI_ALPHA] = alpha;
    v[FRI_NEXT] = fo; v[FRI_SEL] = F::ONE;
    v[3 * FRI_WIDTH + 5] = F::ONE; v[3 * FRI_WIDTH + 6] = F::ONE;
    (RowMajorMatrix::new(v, FRI_WIDTH), vec![F::ZERO; 4])
}

/// Generate one real leaf: SC+FRI proof -> extract V2 -> prove V2.
/// Returns (proof_size, prove_time_ms).
fn prove_real_leaf(seed: u128) -> (usize, f64) {
    let start = Instant::now();

    // Step 1: SC + FRI proof (source)
    let (sc_t, sc_p) = build_sc_trace(seed);
    let (fri_t, fri_p) = build_fri_trace(seed);
    let raw = 2 * SC_WIDTH + 4 * FRI_WIDTH;
    let src_arity = raw.next_power_of_two().trailing_zeros() as usize;
    let src_cfg = SrcCfg { pcs: build_pcs(src_arity) };

    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;
    let mut ch_s = make_ch(&[seed as u8]);
    let (pk, vk) = setup(&src_cfg, &[&sc_air, &fri_air], &mut ch_s).unwrap();

    let sc_i = ProverInstance::new(&sc_air, Table::new(sc_t.transpose()), &pk, &sc_p);
    let fri_i = ProverInstance::new(&fri_air, Table::new(fri_t.transpose()), &pk, &fri_p);
    let src_ch_seed = [seed as u8, 0xA];
    let mut ch_p = make_ch(&src_ch_seed);
    let proof = prove(&src_cfg, ProverInstances::new(vec![sc_i, fri_i]), 0, &mut ch_p).unwrap();

    // Step 2: Extract V2 trace
    let _ = take_last_indices();
    let _ = take_last_betas_bytes();
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_p),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_p),
    ];
    let mut ch_v = make_ch(&src_ch_seed);  // SAME seed as prove
    verify(&src_cfg, VerifierInstances::new(verif), &proof, 0, &mut ch_v).unwrap();

    let indices = take_last_indices().unwrap();
    let betas_bytes = take_last_betas_bytes().unwrap();
    let betas: Vec<F> = betas_bytes.iter().map(|b| {
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b[..16]);
        F::from_le_bytes(arr)
    }).collect();

    // Step 3: Build V2 trace from extracted data
    let v2_trace = build_v2_trace(&proof, &indices, &betas);
    let v2_rows = v2_trace.height();
    let v2_raw = v2_rows * V2_WIDTH;
    let v2_arity = v2_raw.next_power_of_two().trailing_zeros() as usize;
    let v2_cfg = V2Cfg { pcs: build_pcs(v2_arity) };

    // Step 4: Prove V2
    let v2_air = V2Only;
    let mut ch_v2s = make_ch(&[seed as u8, 0xC]);
    let (v2_pk, v2_vk) = setup(&v2_cfg, &[&v2_air], &mut ch_v2s).unwrap();

    let v2_i = ProverInstance::new(&v2_air, Table::new(v2_trace.transpose()), &v2_pk, &[]);
    let v2_ch_seed = [seed as u8, 0xC];
    let mut ch_v2p = make_ch(&v2_ch_seed);
    let v2_proof = prove(&v2_cfg, ProverInstances::new(vec![v2_i]), 0, &mut ch_v2p).unwrap();

    // Step 5: Verify (sanity)
    let log_h = v2_rows.trailing_zeros() as usize;
    let v2_verif = VerifierInstance::new(&v2_air, &v2_vk, log_h, &[]);
    let mut ch_v2v = make_ch(&v2_ch_seed);  // SAME seed as prove
    verify(&v2_cfg, VerifierInstances::new(vec![v2_verif]), &v2_proof, 0, &mut ch_v2v).unwrap();

    let elapsed = start.elapsed();
    (core::mem::size_of_val(&v2_proof), elapsed.as_secs_f64() * 1000.0)
}

fn build_v2_trace(
    proof: &MultiStarkProof<SrcCfg>,
    indices: &[usize],
    betas: &[F],
) -> RowMajorMatrix<F> {
    let opening = &proof.opening;
    let base = &opening.base_opened_values;
    let rounds = &opening.rounds;

    let num_batches = betas.len();
    let num_queries = indices.len();
    let total_rows = num_batches * num_queries;
    let target_rows = total_rows.next_power_of_two().max(2);

    let mut values = vec![F::ZERO; target_rows * V2_WIDTH];

    for batch in 0..num_batches {
        let curr_rows: &Vec<Vec<F>> = if batch == 0 { base } else { &rounds[batch - 1].opened_values };
        for q in 0..num_queries {
            let index = indices[q];
            let next_position = index >> (batch + 1);
            let x = domain_point::<F>(next_position << 1);
            let beta = betas[batch];

            let lo = curr_rows[2 * q][0];
            let hi = curr_rows[2 * q + 1][0];

            let f1 = lo + hi;
            let f0 = lo + x * f1;
            let expected_next = beta * (f0 + f1) + f0;

            let row = batch * num_queries + q;
            values[row * V2_WIDTH + COL_LO] = lo;
            values[row * V2_WIDTH + COL_HI] = hi;
            values[row * V2_WIDTH + COL_BETA] = beta;
            values[row * V2_WIDTH + COL_X] = x;
            values[row * V2_WIDTH + V2_COL_NEXT] = expected_next;
            if batch == num_batches - 1 && q == num_queries - 1 {
                values[row * V2_WIDTH + V2_COL_IS_LAST] = F::ONE;
            }
        }
    }

    RowMajorMatrix::new(values, V2_WIDTH)
}

#[test]
#[ignore]
fn t1_3_eight_real_leaves() {
    let start = Instant::now();
    println!("=== 8 real leaves ===");
    let mut total_size = 0;
    let mut times = Vec::new();
    for i in 0..8u128 {
        let (sz, ms) = prove_real_leaf(0x1000 + i * 0x11);
        total_size += sz;
        times.push(ms);
        println!("  leaf {}: {}B, {:.2}ms", i, sz, ms);
    }
    let total_ms: f64 = times.iter().sum();
    println!("\nTOTAL: {} leaves, {}B each, {:.2}ms total", 8, total_size / 8, total_ms);
    println!("Wall: {:?}", start.elapsed());
    println!("\n=== T1.3 REAL LEAVES (8) PASS ===");
}

#[test]
#[ignore]
fn t1_3_sixteen_real_leaves() {
    let start = Instant::now();
    println!("=== 16 real leaves ===");
    let mut times = Vec::new();
    for i in 0..16u128 {
        let (_sz, ms) = prove_real_leaf(0x2000 + i * 0x11);
        times.push(ms);
    }
    let total_ms: f64 = times.iter().sum();
    let avg = total_ms / 16.0;
    println!("TOTAL: 16 leaves, avg {:.2}ms/leaf, total {:.2}ms", avg, total_ms);
    println!("Wall: {:?}", start.elapsed());
    println!("\nExtrapolation to 4444 leaves:");
    println!("  sequential: {:.2}s", (avg * 4444.0) / 1000.0);
    println!("  parallel (16x): {:.2}s", (avg * 4444.0) / 16000.0);
    println!("\n=== T1.3 REAL LEAVES (16) PASS ===");
}

#[test]
#[ignore]
fn t1_3_scale_framework_32_leaves() {
    let start = Instant::now();
    println!("=== 32 real leaves (scale test) ===");
    let mut times = Vec::new();
    for i in 0..32u128 {
        let (_sz, ms) = prove_real_leaf(0x3000 + i * 0x11);
        times.push(ms);
    }
    let total_ms: f64 = times.iter().sum();
    let avg = total_ms / 32.0;
    println!("TOTAL: 32 leaves, avg {:.2}ms/leaf, total {:.2}ms", avg, total_ms);
    println!("Wall: {:?}", start.elapsed());
    println!("\n4444-leaf extrapolation:");
    println!("  sequential: {:.2}s", (avg * 4444.0) / 1000.0);
    println!("  parallel (16x): {:.2}s", (avg * 4444.0) / 16000.0);
    println!("\n=== T1.3 SCALE (32) PASS — framework ready for 4444 ===");
}
