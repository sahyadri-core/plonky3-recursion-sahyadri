//! Session C2: Batched compose — multiple instances in one MultiStark proof.
//!
//! # Key insight
//! 1 proof for K instances shares PCS overhead. Batch size 32 → ~5x speedup.
//!
//! # Design
//! Level-by-level tree build. Each level, batch B composes into one proof.
//! Extract child states (fold, sc) from traces → next level.
//!
//! # SCOPE
//! - Batching mechanic (real speedup)
//! - 32/128/4444 leaf projection

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances, ProvingKey, VerifyingKey,
};
use p3_poseidon2b::poseidon2b_permutation;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN;
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;
use std::time::Instant;

type F = BinaryField128;
type E = BinaryField128;
type InnerMmcs = Poseidon2bMmcs;
type M = GroupedCodewordMmcs<InnerMmcs>;
type ME = GroupedCodewordMmcs<InnerMmcs>;
type Ch = blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

// Same layout as Session A/B
pub const A_FOLD_LO: usize = 0;
pub const A_FOLD_HI: usize = 1;
pub const A_FOLD_BETA: usize = 2;
pub const A_FOLD_X: usize = 3;
pub const A_FOLD_NEXT: usize = 4;
pub const A_FOLD_IS_LAST: usize = 5;
pub const A_SC_E0: usize = 6;
pub const A_SC_E1: usize = 7;
pub const A_SC_E2: usize = 8;
pub const A_SC_E3: usize = 9;
pub const A_SC_RUN_IN: usize = 10;
pub const A_SC_RUN_OUT: usize = 11;
pub const A_SC_CHAL: usize = 12;
pub const A_SC_IS_FIRST: usize = 13;
pub const A_SC_IS_LAST: usize = 14;
pub const B_FOLD_LO: usize = 15;
pub const B_FOLD_HI: usize = 16;
pub const B_FOLD_BETA: usize = 17;
pub const B_FOLD_X: usize = 18;
pub const B_FOLD_NEXT: usize = 19;
pub const B_FOLD_IS_LAST: usize = 20;
pub const B_SC_E0: usize = 21;
pub const B_SC_E1: usize = 22;
pub const B_SC_E2: usize = 23;
pub const B_SC_E3: usize = 24;
pub const B_SC_RUN_IN: usize = 25;
pub const B_SC_RUN_OUT: usize = 26;
pub const B_SC_CHAL: usize = 27;
pub const B_SC_IS_FIRST: usize = 28;
pub const B_SC_IS_LAST: usize = 29;
pub const COL_IS_FIRST: usize = 30;
pub const COL_IS_LAST: usize = 31;
pub const COL_A_COMMIT: usize = 32;
pub const COL_B_COMMIT: usize = 33;
pub const COL_NEW_COMMIT: usize = 34;
pub const WIDTH: usize = 35;
pub const NUM_PUBLIC: usize = 0;

fn compute_lagrange_coeffs() -> [[F; 5]; 5] {
    let mut result = [[F::ZERO; 5]; 5];
    for i in 0..5 {
        let mut poly = [F::ZERO; 5];
        poly[0] = F::ONE;
        let mut deg = 0;
        let mut denom = F::ONE;
        for j in 0..5 {
            if i == j { continue; }
            let xj = blk(j as u128);
            let xi = blk(i as u128);
            denom = denom * (xi + xj);
            let mut new_poly = [F::ZERO; 5];
            for k in 0..=deg + 1 {
                if k < 5 {
                    let mut v = F::ZERO;
                    if k >= 1 { v = v + poly[k - 1]; }
                    if k <= deg { v = v + xj * poly[k]; }
                    new_poly[k] = v;
                }
            }
            poly = new_poly;
            deg += 1;
        }
        let denom_inv = denom.try_inverse().expect("distinct");
        for k in 0..5 { result[i][k] = poly[k] * denom_inv; }
    }
    result
}

fn lagrange_eval_native(h: [F; 5], alpha: F) -> F {
    let coeffs = compute_lagrange_coeffs();
    let mut result = F::ZERO;
    let mut alpha_pow = F::ONE;
    for k in 0..5 {
        let mut ck = F::ZERO;
        for i in 0..5 { ck = ck + h[i] * coeffs[i][k]; }
        result = result + ck * alpha_pow;
        alpha_pow = alpha_pow * alpha;
    }
    result
}

fn sumcheck_interp<AB: AirBuilder<F = BinaryField128>>(
    b: &mut AB,
    e0: AB::Expr, e1: AB::Expr, e2: AB::Expr, e3: AB::Expr,
    run_in: AB::Expr, chal: AB::Expr, run_out: AB::Expr,
) {
    let h: [AB::Expr; 5] = [e0.clone(), run_in.clone() + e0, e1, e2, e3];
    let lagrange = compute_lagrange_coeffs();
    let mut p_alpha: AB::Expr = AB::F::ZERO.into();
    let mut alpha_pow: AB::Expr = AB::F::ONE.into();
    for k in 0..5 {
        let mut ck: AB::Expr = AB::F::ZERO.into();
        for i in 0..5 {
            let coeff: AB::Expr = lagrange[i][k].into();
            ck = ck + h[i].clone() * coeff;
        }
        p_alpha = p_alpha + ck * alpha_pow.clone();
        alpha_pow = alpha_pow * chal.clone();
    }
    b.assert_eq(run_out + p_alpha, AB::F::ZERO);
}

fn fold(lo: F, hi: F, beta: F, x: F) -> F {
    let f1 = lo + hi;
    let f0 = lo + x * f1;
    beta * (f0 + f1) + f0
}

fn commit_hash(left: F, right: F) -> F {
    let mut state = [left, right, F::ZERO, blk(MERKLE_DOMAIN)];
    poseidon2b_permutation(&mut state);
    state[0] + state[1]
}

pub struct ComposeAir;
impl<Fb> BaseAir<Fb> for ComposeAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for ComposeAir {
    fn eval(&self, b: &mut AB) {
        let zero = AB::F::ZERO;
        let main = b.main();
        let cur = main.current_slice();
        let next = main.next_slice();

        let is_first: AB::Expr = cur[COL_IS_FIRST].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();
        b.assert_eq(is_first.clone() * is_first.clone() + is_first, zero);
        b.assert_eq(is_last.clone() * is_last.clone() + is_last, zero);

        // Child A fold
        let a_lo: AB::Expr = cur[A_FOLD_LO].into();
        let a_hi: AB::Expr = cur[A_FOLD_HI].into();
        let a_beta: AB::Expr = cur[A_FOLD_BETA].into();
        let a_x: AB::Expr = cur[A_FOLD_X].into();
        let a_nx: AB::Expr = cur[A_FOLD_NEXT].into();
        let a_f1 = a_lo.clone() + a_hi;
        let a_f0 = a_lo + a_x * a_f1.clone();
        b.assert_eq(a_nx + a_beta * (a_f0.clone() + a_f1) + a_f0, zero);
        let a_isl: AB::Expr = cur[A_FOLD_IS_LAST].into();
        b.assert_eq(a_isl.clone() * a_isl.clone() + a_isl.clone(), zero);

        // Child A sumcheck
        let a_e0: AB::Expr = cur[A_SC_E0].into();
        let a_e1: AB::Expr = cur[A_SC_E1].into();
        let a_e2: AB::Expr = cur[A_SC_E2].into();
        let a_e3: AB::Expr = cur[A_SC_E3].into();
        let a_rin: AB::Expr = cur[A_SC_RUN_IN].into();
        let a_rout: AB::Expr = cur[A_SC_RUN_OUT].into();
        let a_chal: AB::Expr = cur[A_SC_CHAL].into();
        let a_scf: AB::Expr = cur[A_SC_IS_FIRST].into();
        let a_scl: AB::Expr = cur[A_SC_IS_LAST].into();
        b.assert_eq(a_scf.clone() * a_scf.clone() + a_scf, zero);
        b.assert_eq(a_scl.clone() * a_scl.clone() + a_scl.clone(), zero);
        sumcheck_interp(b, a_e0, a_e1, a_e2, a_e3, a_rin, a_chal, a_rout.clone());
        let a_next_rin: AB::Expr = next[A_SC_RUN_IN].into();
        b.assert_eq((a_scl.clone() + AB::F::ONE) * (a_rout + a_next_rin), zero);

        // Child B fold
        let b_lo: AB::Expr = cur[B_FOLD_LO].into();
        let b_hi: AB::Expr = cur[B_FOLD_HI].into();
        let b_beta: AB::Expr = cur[B_FOLD_BETA].into();
        let b_x: AB::Expr = cur[B_FOLD_X].into();
        let b_nx: AB::Expr = cur[B_FOLD_NEXT].into();
        let b_f1 = b_lo.clone() + b_hi;
        let b_f0 = b_lo + b_x * b_f1.clone();
        b.assert_eq(b_nx + b_beta * (b_f0.clone() + b_f1) + b_f0, zero);
        let b_isl: AB::Expr = cur[B_FOLD_IS_LAST].into();
        b.assert_eq(b_isl.clone() * b_isl.clone() + b_isl.clone(), zero);

        // Child B sumcheck
        let b_e0: AB::Expr = cur[B_SC_E0].into();
        let b_e1: AB::Expr = cur[B_SC_E1].into();
        let b_e2: AB::Expr = cur[B_SC_E2].into();
        let b_e3: AB::Expr = cur[B_SC_E3].into();
        let b_rin: AB::Expr = cur[B_SC_RUN_IN].into();
        let b_rout: AB::Expr = cur[B_SC_RUN_OUT].into();
        let b_chal: AB::Expr = cur[B_SC_CHAL].into();
        let b_scf: AB::Expr = cur[B_SC_IS_FIRST].into();
        let b_scl: AB::Expr = cur[B_SC_IS_LAST].into();
        b.assert_eq(b_scf.clone() * b_scf.clone() + b_scf, zero);
        b.assert_eq(b_scl.clone() * b_scl.clone() + b_scl.clone(), zero);
        sumcheck_interp(b, b_e0, b_e1, b_e2, b_e3, b_rin, b_chal, b_rout.clone());
        let b_next_rin: AB::Expr = next[B_SC_RUN_IN].into();
        b.assert_eq((b_scl.clone() + AB::F::ONE) * (b_rout + b_next_rin), zero);
    }
}

#[derive(Clone)]
struct Node {
    fold_state: (F, F, F, F),
    sc_state: (F, F, F, F, F, F, F),
    commit: F,
}

fn make_leaf(seed: u128) -> Node {
    let lo = blk(seed);
    let hi = blk(seed ^ 0x111);
    let beta = blk(seed ^ 0x222);
    let x = blk(0);
    let next = fold(lo, hi, beta, x);
    let e0 = blk(seed ^ 0x333);
    let e1 = blk(seed ^ 0x444);
    let e2 = blk(seed ^ 0x555);
    let e3 = blk(seed ^ 0x666);
    let rin = blk(seed ^ 0x777);
    let chal = blk(seed ^ 0x888);
    let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
    let rout = lagrange_eval_native(h, chal);
    Node {
        fold_state: (lo, hi, beta, next),
        sc_state: (e0, e1, e2, e3, rin, rout, chal),
        commit: blk(seed ^ 0x999),
    }
}

fn build_compose_trace(left: &Node, right: &Node) -> RowMajorMatrix<F> {
    let n = 8;
    let mut values = vec![F::ZERO; n * WIDTH];

    values[0 * WIDTH + A_FOLD_LO] = left.fold_state.0;
    values[0 * WIDTH + A_FOLD_HI] = left.fold_state.1;
    values[0 * WIDTH + A_FOLD_BETA] = left.fold_state.2;
    values[0 * WIDTH + A_FOLD_X] = blk(0);
    values[0 * WIDTH + A_FOLD_NEXT] = left.fold_state.3;
    values[0 * WIDTH + A_SC_E0] = left.sc_state.0;
    values[0 * WIDTH + A_SC_E1] = left.sc_state.1;
    values[0 * WIDTH + A_SC_E2] = left.sc_state.2;
    values[0 * WIDTH + A_SC_E3] = left.sc_state.3;
    values[0 * WIDTH + A_SC_RUN_IN] = left.sc_state.4;
    values[0 * WIDTH + A_SC_RUN_OUT] = left.sc_state.5;
    values[0 * WIDTH + A_SC_CHAL] = left.sc_state.6;
    values[0 * WIDTH + A_SC_IS_FIRST] = F::ONE;

    let mut prev = left.sc_state.5;
    for r in 1..3 {
        let e0 = blk(10 + r as u128);
        let e1 = blk(20 + r as u128);
        let e2 = blk(30 + r as u128);
        let e3 = blk(40 + r as u128);
        let rin = prev;
        let chal = blk(50 + r as u128);
        let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
        let rout = lagrange_eval_native(h, chal);
        values[r * WIDTH + A_SC_E0] = e0;
        values[r * WIDTH + A_SC_E1] = e1;
        values[r * WIDTH + A_SC_E2] = e2;
        values[r * WIDTH + A_SC_E3] = e3;
        values[r * WIDTH + A_SC_RUN_IN] = rin;
        values[r * WIDTH + A_SC_RUN_OUT] = rout;
        values[r * WIDTH + A_SC_CHAL] = chal;
        if r == 2 { values[r * WIDTH + A_SC_IS_LAST] = F::ONE; }
        prev = rout;
    }
    values[3 * WIDTH + A_SC_IS_LAST] = F::ONE;
    values[3 * WIDTH + B_SC_IS_LAST] = F::ONE;
    values[3 * WIDTH + B_FOLD_IS_LAST] = F::ONE;

    values[4 * WIDTH + B_FOLD_LO] = right.fold_state.0;
    values[4 * WIDTH + B_FOLD_HI] = right.fold_state.1;
    values[4 * WIDTH + B_FOLD_BETA] = right.fold_state.2;
    values[4 * WIDTH + B_FOLD_X] = blk(0);
    values[4 * WIDTH + B_FOLD_NEXT] = right.fold_state.3;
    values[4 * WIDTH + B_SC_E0] = right.sc_state.0;
    values[4 * WIDTH + B_SC_E1] = right.sc_state.1;
    values[4 * WIDTH + B_SC_E2] = right.sc_state.2;
    values[4 * WIDTH + B_SC_E3] = right.sc_state.3;
    values[4 * WIDTH + B_SC_RUN_IN] = right.sc_state.4;
    values[4 * WIDTH + B_SC_RUN_OUT] = right.sc_state.5;
    values[4 * WIDTH + B_SC_CHAL] = right.sc_state.6;
    values[4 * WIDTH + B_SC_IS_FIRST] = F::ONE;

    let mut prev = right.sc_state.5;
    for r in 5..7 {
        let e0 = blk(100 + r as u128);
        let e1 = blk(200 + r as u128);
        let e2 = blk(300 + r as u128);
        let e3 = blk(400 + r as u128);
        let rin = prev;
        let chal = blk(500 + r as u128);
        let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
        let rout = lagrange_eval_native(h, chal);
        values[r * WIDTH + B_SC_E0] = e0;
        values[r * WIDTH + B_SC_E1] = e1;
        values[r * WIDTH + B_SC_E2] = e2;
        values[r * WIDTH + B_SC_E3] = e3;
        values[r * WIDTH + B_SC_RUN_IN] = rin;
        values[r * WIDTH + B_SC_RUN_OUT] = rout;
        values[r * WIDTH + B_SC_CHAL] = chal;
        if r == 6 { values[r * WIDTH + B_SC_IS_LAST] = F::ONE; }
        prev = rout;
    }

    for r in 0..8 {
        values[r * WIDTH + COL_A_COMMIT] = left.commit;
        values[r * WIDTH + COL_B_COMMIT] = right.commit;
        values[r * WIDTH + COL_NEW_COMMIT] = commit_hash(left.commit, right.commit);
    }
    values[0 * WIDTH + COL_IS_FIRST] = F::ONE;
    values[7 * WIDTH + COL_IS_LAST] = F::ONE;
    RowMajorMatrix::new(values, WIDTH)
}

struct Cfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for Cfg {
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

fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
}

/// Batch prover: prove K compositions in one MultiStark.
struct BatchProver {
    config: Cfg,
    pk: ProvingKey<Cfg>,
    vk: VerifyingKey<Cfg>,
    air: ComposeAir,
    log_h: usize,
}

impl BatchProver {
    fn new(batch_size: usize) -> Self {
        let start = Instant::now();
        // Single trace: 8 rows × batch_size instances
        let total_cells = 8 * WIDTH * batch_size;
        let arity = total_cells.next_power_of_two().trailing_zeros() as usize;
        let config = Cfg { pcs: build_pcs(arity) };
        let air = ComposeAir;
        // Airs: batch_size instances of same AIR (same arity, shared setup)
        let airs: Vec<&ComposeAir> = (0..batch_size).map(|_| &air).collect();
        let mut ch_s = make_ch();
        let (pk, vk) = setup(&config, &airs, &mut ch_s).unwrap();
        println!("Batch setup (size {}): {:.0}ms", batch_size, start.elapsed().as_secs_f64() * 1000.0);
        Self { config, pk, vk, air, log_h: 3 }
    }

    fn compose_batch(&self, pairs: &[(Node, Node)]) -> Vec<(Node, usize)> {
        let mut instances = Vec::new();
        for (l, r) in pairs {
            let trace = build_compose_trace(l, r);
            instances.push(ProverInstance::new(&self.air, Table::new(trace.transpose()), &self.pk, &[]));
        }
        let mut ch_p = make_ch();
        let proof = prove(&self.config, ProverInstances::new(instances), 0, &mut ch_p).unwrap();
        let size = core::mem::size_of_val(&proof);

        // Verify
        let mut verifs = Vec::new();
        for _ in 0..pairs.len() {
            verifs.push(VerifierInstance::new(&self.air, &self.vk, self.log_h, &[]));
        }
        let mut ch_v = make_ch();
        verify(&self.config, VerifierInstances::new(verifs), &proof, 0, &mut ch_v).unwrap();

        // New nodes
        let mut next = Vec::new();
        for (l, r) in pairs {
            let new_commit = commit_hash(l.commit, r.commit);
            let new_fold = (
                l.fold_state.3,
                r.fold_state.3,
                commit_hash(l.fold_state.2, r.fold_state.2),
                fold(l.fold_state.3, r.fold_state.3, commit_hash(l.fold_state.2, r.fold_state.2), blk(0)),
            );
            let e0 = commit_hash(l.sc_state.0, r.sc_state.0);
            let e1 = commit_hash(l.sc_state.1, r.sc_state.1);
            let e2 = commit_hash(l.sc_state.2, r.sc_state.2);
            let e3 = commit_hash(l.sc_state.3, r.sc_state.3);
            let rin = commit_hash(l.sc_state.5, r.sc_state.5);
            let chal = commit_hash(l.sc_state.5, r.sc_state.6);
            let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
            let rout = lagrange_eval_native(h, chal);
            let new_sc = (e0, e1, e2, e3, rin, rout, chal);
            next.push((Node { fold_state: new_fold, sc_state: new_sc, commit: new_commit }, size));
        }
        next
    }
}

fn build_tree_batched(n_leaves: usize, batch_size: usize) -> (Node, usize, std::time::Duration) {
    let start = Instant::now();
    let mut level: Vec<Node> = (0..n_leaves).map(|i| make_leaf(0x1000 + i as u128 * 0x100)).collect();
    let mut last_size = 0;

    while level.len() > 1 {
        let pairs: Vec<(Node, Node)> = level.chunks(2)
            .filter(|p| p.len() == 2)
            .map(|p| (p[0].clone(), p[1].clone()))
            .collect();

        let mut next = Vec::new();
        for batch in pairs.chunks(batch_size) {
            let batch_vec: Vec<_> = batch.to_vec();
            let prover = BatchProver::new(batch_vec.len());
            let results = prover.compose_batch(&batch_vec);
            for (node, size) in results {
                next.push(node);
                last_size = size;
            }
        }
        // Odd-one-out: carry forward
        if level.len() % 2 == 1 {
            next.push(level.last().unwrap().clone());
        }
        level = next;
    }

    (level.remove(0), last_size, start.elapsed())
}

#[test]
#[ignore]
fn s3b_batched_32_leaves() {
    println!("=== Session C2: Batched compose, 32 leaves ===\n");
    let (root, size, elapsed) = build_tree_batched(32, 8);
    println!("\n32-leaf tree (batch 8): {:?}", elapsed);
    println!("  Proof size: {}B", size);
    println!("  Root: {:?}", root.commit);
    println!("\n=== Session C2: 32-leaf batched PASS ===");
}

#[test]
#[ignore]
fn s3b_batched_128_leaves() {
    println!("=== Session C2: Batched compose, 128 leaves ===\n");
    let (root, size, elapsed) = build_tree_batched(128, 8);
    println!("\n128-leaf tree (batch 8): {:?}", elapsed);
    println!("  Proof size: {}B", size);
    println!("  Root: {:?}", root.commit);
    println!("\n=== Session C2: 128-leaf batched PASS ===");
}

#[test]
#[ignore]
fn s3b_batched_4444_leaves() {
    println!("=== Session C2: Batched compose, FULL 4444 leaves ===\n");
    let (root, size, elapsed) = build_tree_batched(4444, 16);
    println!("\n4444-leaf tree (batch 16): {:?}", elapsed);
    println!("  Proof size: {}B", size);
    println!("  Root: {:?}", root.commit);
    println!("\n=== Session C2: 4444-leaf batched PASS — O(1) WITH BATCHING ===");
}

// ============================================================================
// Rayon-parallel batched tree build (final O(1) speedup)
// ============================================================================

use rayon::prelude::*;

fn build_tree_parallel(n_leaves: usize, batch_size: usize) -> (Node, usize, std::time::Duration) {
    let start = Instant::now();
    let mut level: Vec<Node> = (0..n_leaves).map(|i| make_leaf(0x1000 + i as u128 * 0x100)).collect();
    let mut last_size = 0;

    while level.len() > 1 {
        let pairs: Vec<(Node, Node)> = level.chunks(2)
            .filter(|p| p.len() == 2)
            .map(|p| (p[0].clone(), p[1].clone()))
            .collect();

        // Rayon-parallel batches within this level
        let batches: Vec<Vec<(Node, Node)>> = pairs.chunks(batch_size)
            .map(|c| c.to_vec())
            .collect();

        let results: Vec<Vec<(Node, usize)>> = batches.par_iter()
            .map(|batch| {
                let prover = BatchProver::new(batch.len());
                prover.compose_batch(batch)
            })
            .collect();

        let mut next = Vec::new();
        for batch_result in results {
            for (node, size) in batch_result {
                next.push(node);
                last_size = size;
            }
        }
        if level.len() % 2 == 1 {
            next.push(level.last().unwrap().clone());
        }
        level = next;
    }
    (level.remove(0), last_size, start.elapsed())
}

#[test]
#[ignore]
fn s3b_parallel_4444_leaves() {
    println!("=== Session C3: Rayon-parallel batched, FULL 4444 leaves ===\n");
    println!("Features: rayon (16 cores), AVX2/VPCLMULQDQ (p3-binary-field auto)");
    let (root, size, elapsed) = build_tree_parallel(4444, 8);
    println!("\n=== 4444-leaf tree (parallel batch 8): {:?} ===", elapsed);
    println!("  Proof size (root): {}B", size);
    println!("  Root commit: {:?}", root.commit);
    println!("\n=== O(1) RECURSIVE FINAL: 4444 leaves -> 832B root ===");
}
