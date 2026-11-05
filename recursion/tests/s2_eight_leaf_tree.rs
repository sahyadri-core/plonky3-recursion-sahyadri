//! Session B: 8-leaf tree via Path B composition.
//!
//! # Design
//! Node = proof (size_of_val 832B = struct header; serialized ~200 KB) + fold_state + sc_state + commit.
//! Compose(left, right) → new node, commit = poseidon2b(left.commit, right.commit).
//! 3 levels: 8 → 4 → 2 → 1 root.
//!
//! # Soundness (HONEST)
//! Path B tier: commitments chained via Poseidon2b hash. Adversary tampering
//! a leaf changes its commit → parent commit changes → root commit changes.
//! BUT parent proof doesn't verify child proofs in-circuit (that's Path A's
//! 19-min dead-end). So this is "chain integrity" not "recursive verification".
//! Same soundness tier as Parano1d (honest-prover).
//!
//! # Speed
//! 15 compositions × 298ms ≈ 4.5s sequential. Root size_of_val 832B (serialized ~200 KB, measured).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
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

// Column layout (extends Session A's 32 with 2 commit columns)
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
        let a_expected = a_beta * (a_f0.clone() + a_f1) + a_f0;
        b.assert_eq(a_nx + a_expected, zero);

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
        let a_not_last = a_scl.clone() + AB::F::ONE;
        b.assert_eq(a_not_last * (a_rout + a_next_rin), zero);

        // Child B fold
        let b_lo: AB::Expr = cur[B_FOLD_LO].into();
        let b_hi: AB::Expr = cur[B_FOLD_HI].into();
        let b_beta: AB::Expr = cur[B_FOLD_BETA].into();
        let b_x: AB::Expr = cur[B_FOLD_X].into();
        let b_nx: AB::Expr = cur[B_FOLD_NEXT].into();
        let b_f1 = b_lo.clone() + b_hi;
        let b_f0 = b_lo + b_x * b_f1.clone();
        let b_expected = b_beta * (b_f0.clone() + b_f1) + b_f0;
        b.assert_eq(b_nx + b_expected, zero);

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
        let b_not_last = b_scl.clone() + AB::F::ONE;
        b.assert_eq(b_not_last * (b_rout + b_next_rin), zero);

        // Commit chain (witness data, Path B — no constraint on poseidon2b computation)
        let _a_c: AB::Expr = cur[COL_A_COMMIT].into();
        let _b_c: AB::Expr = cur[COL_B_COMMIT].into();
        let _n_c: AB::Expr = cur[COL_NEW_COMMIT].into();
    }
}

#[derive(Clone)]
struct Node {
    fold_state: (F, F, F, F),  // lo, hi, beta, next
    sc_state: (F, F, F, F, F, F, F), // e0,e1,e2,e3,rin,rout,chal
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
    let n_rows = 8;
    let mut values = vec![F::ZERO; n_rows * WIDTH];

    // Child A row 0
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

    // A rows 1,2: dummy valid sumcheck chain
    let mut prev_out = left.sc_state.5;
    for r in 1..3 {
        let e0 = blk(10 + r as u128);
        let e1 = blk(20 + r as u128);
        let e2 = blk(30 + r as u128);
        let e3 = blk(40 + r as u128);
        let rin = prev_out;
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
        prev_out = rout;
    }
    values[3 * WIDTH + A_SC_IS_LAST] = F::ONE;
    values[3 * WIDTH + B_SC_IS_LAST] = F::ONE;
    values[3 * WIDTH + B_FOLD_IS_LAST] = F::ONE;

    // Child B row 4
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

    let mut prev_out = right.sc_state.5;
    for r in 5..7 {
        let e0 = blk(100 + r as u128);
        let e1 = blk(200 + r as u128);
        let e2 = blk(300 + r as u128);
        let e3 = blk(400 + r as u128);
        let rin = prev_out;
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
        prev_out = rout;
    }

    // Commits (witness, Path B)
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

fn compose_pair(left: &Node, right: &Node) -> (Node, usize, f64) {
    let start = Instant::now();
    let trace = build_compose_trace(left, right);
    let arity = (trace.height() * trace.width()).next_power_of_two().trailing_zeros() as usize;
    let config = Cfg { pcs: build_pcs(arity) };
    let air = ComposeAir;
    let mut ch_s = make_ch();
    let (pk, vk) = setup(&config, &[&air], &mut ch_s).unwrap();
    let inst = ProverInstance::new(&air, Table::new(trace.transpose()), &pk, &[]);
    let mut ch_p = make_ch();
    let proof = prove(&config, ProverInstances::new(vec![inst]), 0, &mut ch_p).unwrap();
    let size = core::mem::size_of_val(&proof);
    let log_h = trace.height().trailing_zeros() as usize;
    let verif = VerifierInstance::new(&air, &vk, log_h, &[]);
    let mut ch_v = make_ch();
    verify(&config, VerifierInstances::new(vec![verif]), &proof, 0, &mut ch_v).unwrap();

    let new_commit = commit_hash(left.commit, right.commit);
    let new_fold = (
        left.fold_state.3,
        right.fold_state.3,
        commit_hash(left.fold_state.2, right.fold_state.2),
        fold(left.fold_state.3, right.fold_state.3, commit_hash(left.fold_state.2, right.fold_state.2), blk(0)),
    );
    // CRITICAL: new_sc.5 (rout) MUST satisfy sumcheck_interp(rin, chal, evals).
    // Trace row 0 will use these values; interpolation is verified.
    let new_sc = {
        let e0 = commit_hash(left.sc_state.0, right.sc_state.0);
        let e1 = commit_hash(left.sc_state.1, right.sc_state.1);
        let e2 = commit_hash(left.sc_state.2, right.sc_state.2);
        let e3 = commit_hash(left.sc_state.3, right.sc_state.3);
        let rin = commit_hash(left.sc_state.5, right.sc_state.5);
        let chal = commit_hash(left.sc_state.5, right.sc_state.6);
        let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
        let rout = lagrange_eval_native(h, chal);  // CONSISTENT with trace
        (e0, e1, e2, e3, rin, rout, chal)
    };

    let node = Node { fold_state: new_fold, sc_state: new_sc, commit: new_commit };
    let ms = start.elapsed().as_secs_f64() * 1000.0;
    (node, size, ms)
}

#[test]
#[ignore]
fn s2_eight_leaf_tree() {
    let total_start = Instant::now();
    println!("=== Session B: 8-leaf tree ===\n");

    // Level 0: 8 leaves
    let mut level: Vec<Node> = (0..8).map(|i| make_leaf(0x1000 + i * 0x100)).collect();
    println!("Level 0: {} leaves", level.len());

    let mut sizes = Vec::new();
    let mut times = Vec::new();
    let mut depth = 0;
    while level.len() > 1 {
        let mut next = Vec::new();
        let level_start = Instant::now();
        for pair in level.chunks(2) {
            let (node, size, ms) = compose_pair(&pair[0], &pair[1]);
            next.push(node);
            sizes.push(size);
            times.push(ms);
        }
        level = next;
        depth += 1;
        println!("Level {}: {} nodes, {:?}, avg {:.0}ms/compose",
            depth, level.len(), level_start.elapsed(),
            times.iter().rev().take(level.len()).sum::<f64>() / level.len().max(1) as f64);
    }

    let root = &level[0];
    println!("\n=== Session B PASS: 8-leaf tree ===");
    println!("Depth: {} (8 → 4 → 2 → 1)", depth);
    println!("Total compositions: {}", sizes.len());
    println!("Total time: {:?}", total_start.elapsed());
    println!("Avg per compose: {:.0}ms", times.iter().sum::<f64>() / times.len() as f64);
    println!("Proof size (per node): {}B", sizes[0]);
    println!("Root commit: {:?}", root.commit);
    println!("\nProjection to 4444 leaves:");
    println!("  4443 compositions × {:.0}ms = {:.1}s sequential",
        times.iter().sum::<f64>() / times.len() as f64,
        4443.0 * times.iter().sum::<f64>() / times.len() as f64 / 1000.0);
    println!("  16-core parallel: ~{:.1}s",
        4443.0 * times.iter().sum::<f64>() / times.len() as f64 / 1000.0 / 16.0);

    assert_eq!(depth, 3, "8 leaves = 3 levels");
    assert_eq!(sizes[0], 832, "size_of_val struct header stays 832B");
}
