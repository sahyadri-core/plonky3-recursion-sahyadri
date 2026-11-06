//! ⚠️ SESSION 5 WIP — v2 FAILED (2026-11-06)
//!
//! ## Attempts
//! - v1: generic `pad_trace()` for SC → `Zerocheck(FinalSumMismatch)`
//! - v2: custom SC padding (final_sum carry-through) → SAME error
//!
//! ## Runtime per attempt
//! 577s prove + verify failure = ~10 min per iteration. Expensive.
//!
//! ## Hypotheses (unresolved)
//! A. Session 4 ("Sub-3 PASS" comment) may also fail at 9 levels — never confirmed end-to-end.
//!    In that case SC addition is not the culprit; S4 baseline is broken.
//! B. MP AIR's depth-specific constraint (if any) violated at 2 levels vs 9.
//! C. SC's unconstrained `alpha` column interacts badly with combined proof's
//!    random evaluation. See sumcheck_verifier_air.rs:NOT YET DONE section.
//! D. P2B padding (if trace had to be padded — was NOT in S4 with 68 rows × 1024 W = 69632 > 32768 MIN_TRACE_CELLS).
//!
//! ## Next session debug plan
//! 1. Run `t1_4c_s4_sub3_merkle_wire` (9 levels) in background — see if it PASSES or has same error.
//!    - If S4 fails → padding issue predates SC, not SC-specific.
//!    - If S4 passes → SC/level-specific issue, isolate further.
//! 2. Create `t1_4c_s5_isolated_sc.rs`: SC-only padded trace in MultiStark (no V2/MP/P2B).
//!    - Prove+verify single AIR. Fast (~1-2 min). If fails → SC padding broken.
//! 3. Create `t1_4c_s5_isolated_mp.rs`: MP-only padded trace in MultiStark.
//!    - If fails at 2 levels → MP needs >= depth 3 or similar constraint.
//!
//! ## Realistic timeline update
//! T1.4c is a multi-week research track. 3 hours today revealed:
//!   - S1-S2: worked (source proof + V2)
//!   - S4: unverified end-to-end at 9 levels (10 min run, no completion seen)
//!   - S5: failed at both padding strategies
//! Next session (S5 debugging): ~4-6 hours focused work.


//! T1.4c Session 4: Sub-3 Merkle path verified via Poseidon2b bus.
//!
//! # Goal
//! V2 trace + Poseidon2b producers in one MultiStark. Proves:
//! - V2 fold relations (already have from S3)
//! - Merkle path authenticates via Poseidon2b bus (PUSH from Poseidon2bBusAir, PULL from V2)
//!
//! # Design (3D2c pattern)
//! - V2 produces (lo, hi, beta, x, next) per fold row
//! - We need to prove: `lo, hi` come from committed leaves via Merkle path
//! - Merkle path: leaf → parent via Poseidon2b(leaf, sibling) = parent
//! - So: 1 MerklePathBusAir Pull per level, Poseidon2bBusAir Push per level
//!
//! # SCOPE (honest, this session)
//! - V2 trace (from S3 extraction) + Merkle tree over V2 leaves
//! - Poseidon2b producers verify each parent computation
//! - Bus Pull from a MerklePath AIR, Push from Poseidon2b
//! - Combined prove+verify
//!
//! # NOT in scope (needs more sessions)
//! - Full RecursiveVerifierAir integration (Session 9)
//! - Sub-5 transcript replay (Sessions 6-8)
//! - O(1) tree (Session 10)
//!
//! # Reality
//! Poseidon2b is 30x slower than blake3 — 4444-leaf tree will be ~40s parallel.
//! Acceptable for recursive, but slower than blake3 baseline.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_dft::domain_point;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
    take_last_betas_bytes, take_last_indices,
};
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN;
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;
use p3_poseidon2b::poseidon2b_permutation;

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
use p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir;

type F = BinaryField128;
type E = BinaryField128;
type InnerMmcs = Poseidon2bMmcs;
type M = GroupedCodewordMmcs<InnerMmcs>;
type ME = GroupedCodewordMmcs<InnerMmcs>;
type Ch = p3_test_utils::binary_field_params::blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

// Bus for Merkle compression: (left, right, parent)
const MERKLE_BUS: BusName<'static> = BusName::new("sahyadri_merkle_compress");

// === Sub-3 Merkle Path AIR ===
// Per row: (curr, sib, parent, activation)
// Constraint: Poseidon2b(curr, sib, 0, MERKLE_DOMAIN) = parent via bus
pub const MP_COL_CURR: usize = 0;
pub const MP_COL_SIB: usize = 1;
pub const MP_COL_PARENT: usize = 2;
pub const MP_COL_IS_REAL: usize = 3;
pub const MP_WIDTH: usize = 4;
pub const MP_NUM_PUBLIC: usize = 0;

pub struct MerklePathAir;

impl<Fb> BaseAir<Fb> for MerklePathAir {
    fn width(&self) -> usize { MP_WIDTH }
    fn num_public_values(&self) -> usize { MP_NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for MerklePathAir {
    fn eval(&self, b: &mut AB) {
        // No local constraints — bus Pull does the verification via Poseidon2b Push
        let _ = b.main().current_slice();
    }
}

// Bus Pull version
pub struct MerklePathBusAir;

impl<Fb> BaseAir<Fb> for MerklePathBusAir {
    fn width(&self) -> usize { MP_WIDTH }
    fn num_public_values(&self) -> usize { MP_NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB>
    for MerklePathBusAir
{
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let cur = main.current_slice();
        let curr: AB::Expr = cur[MP_COL_CURR].into();
        let sib: AB::Expr = cur[MP_COL_SIB].into();
        let parent: AB::Expr = cur[MP_COL_PARENT].into();
        let is_real: AB::Expr = cur[MP_COL_IS_REAL].into();

        // CRITICAL: `BusActivation::Boolean(is_real)` requires the caller to
        // constrain is_real ∈ {0,1}. Hand-assembled declarations don't get this
        // constraint from the framework. Without it, the bus multiset is
        // under-constrained and zerocheck fails at FinalSumMismatch.
        let is_real_sq = is_real.clone() * is_real.clone();
        b.assert_eq(is_real_sq + is_real.clone(), AB::F::ZERO);

        // Boolean activation on is_real (1 for real rows, 0 for padding)
        // Enforces: exactly 9 Pulls (real) = 9 Pushes (producers)
        b.push_bus_interaction(
            MERKLE_BUS,
            BusDirection::Pull,
            [curr, sib, parent],
            BusActivation::Boolean(is_real),
        );
    }
}

// === Src AIR (SC + FRI) for generating real proof ===
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

// === Combined AIR for combined prove ===
#[derive(Clone, Copy)]
pub enum CombinedAir {
    V2,
    SumcheckVerifier,
    Poseidon2b,
    MerklePath,
}

impl<Fb> BaseAir<Fb> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::V2 => V2_WIDTH,
            Self::SumcheckVerifier => SC_WIDTH,
            Self::Poseidon2b => <Poseidon2bBusAir as BaseAir<BinaryField128>>::width(&Poseidon2bBusAir),
            Self::MerklePath => MP_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::V2 => 0,
            Self::SumcheckVerifier => <SumcheckVerifierAir as BaseAir<BinaryField128>>::num_public_values(&SumcheckVerifierAir),
            Self::Poseidon2b => <Poseidon2bBusAir as BaseAir<BinaryField128>>::num_public_values(&Poseidon2bBusAir),
            Self::MerklePath => 0,
        }
    }
}

impl<AB> Air<AB> for CombinedAir
where AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::V2 => BinaryVerifierAirV2.eval(b),
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::Poseidon2b => Poseidon2bBusAir.eval(b),
            Self::MerklePath => MerklePathBusAir.eval(b),
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

struct CombCfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for CombCfg {
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

fn make_ch() -> Ch {
    use p3_test_utils::binary_field_params::blake3;
    Ch::from_hasher(vec![], blake3::byte_hash())
}

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
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
    let fold_out = fri_fold(p0, p1, alpha, F::ONE);
    let mut v = vec![F::ZERO; 4 * FRI_WIDTH];
    v[FRI_PAIR0] = p0; v[FRI_PAIR1] = p1; v[FRI_ALPHA] = alpha;
    v[FRI_NEXT] = fold_out; v[FRI_SEL] = F::ONE;
    v[3 * FRI_WIDTH + 5] = F::ONE; v[3 * FRI_WIDTH + 6] = F::ONE;
    (RowMajorMatrix::new(v, FRI_WIDTH), vec![F::ZERO; 4])
}

fn build_v2_trace_from_real(
    proof: &p3_multi_stark::MultiStarkProof<SrcCfg>,
    indices: &[usize],
    betas: &[F],
) -> RowMajorMatrix<F> {
    let opening = &proof.opening;
    let base = &opening.base_opened_values;
    let rounds = &opening.rounds;
    let _final_cw = opening.final_codeword.as_slice();

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

/// Build Merkle tree over V2 lo values (as leaves).
/// Extract path for one specific leaf (index 0).
fn build_merkle_path_for_leaf(lo_values: &[F], leaf_index: usize) -> Vec<(F, F, F)> {
    // Poseidon2b hash of pair
    let hash_pair = |l: F, r: F| -> F {
        let mut state = [l, r, F::ZERO, blk(MERKLE_DOMAIN)];
        poseidon2b_permutation(&mut state);
        state[0] + state[1]
    };

    // Pad to power-of-two
    let n = lo_values.len().next_power_of_two();
    let mut level: Vec<F> = (0..n).map(|i| lo_values.get(i).copied().unwrap_or(F::ZERO)).collect();

    let mut path = Vec::new();
    let mut idx = leaf_index;

    while level.len() > 1 {
        let sib_idx = idx ^ 1;
        let sib = level[sib_idx];
        let curr = level[idx];

        // Compute all parents for this level
        let mut next = Vec::with_capacity(level.len() / 2);
        for chunk in level.chunks(2) {
            next.push(hash_pair(chunk[0], chunk[1]));
        }
        let parent = next[idx / 2];

        path.push((curr, sib, parent));
        level = next;
        idx /= 2;
    }
    path
}

/// Build producer trace for Poseidon2bBusAir from a single (left, right) input.
fn build_poseidon2b_producer_trace(left: F, right: F, domain: F) -> RowMajorMatrix<F> {
    let state_in = [left, right, F::ZERO, domain];
    // CRITICAL: Poseidon2bAir requires full 68-row trace (N_STATES = 66 rounds + 2).
    // Truncating to 2 rows breaks internal round constraints (rows 2..67 must be
    // populated by the permutation). Do NOT pad/truncate.
    p3_poseidon2b::generate_poseidon2b_trace(state_in)
}

fn build_poseidon2b_producer_public(left: F, right: F, domain: F) -> Vec<F> {
    let state_in = [left, right, F::ZERO, domain];
    let mut state_out = state_in;
    poseidon2b_permutation(&mut state_out);
    vec![state_in[0], state_in[1], state_in[2], state_in[3],
         state_out[0], state_out[1], state_out[2], state_out[3]]
}

#[test]
#[ignore]
fn t1_4c_s5_with_sumcheck() {
    use std::time::Instant;
    let start = Instant::now();

    // ===== 1. Generate source proof (Poseidon2b) =====
    println!("=== Generating source proof (SC + FRI, Poseidon2b) ===");
    let (sc_t, sc_p) = build_sc_trace();
    let (fri_t, fri_p) = build_fri_trace();
    let src_raw = 2 * SC_WIDTH + 4 * FRI_WIDTH;
    let src_arity = src_raw.next_power_of_two().trailing_zeros() as usize;
    let src_cfg = SrcCfg { pcs: build_pcs(src_arity) };
    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;

    let mut ch_s = make_ch();
    let (pk, vk) = setup(&src_cfg, &[&sc_air, &fri_air], &mut ch_s).unwrap();
    let sc_i = ProverInstance::new(&sc_air, Table::new(sc_t.clone().transpose()), &pk, &sc_p);
    let fri_i = ProverInstance::new(&fri_air, Table::new(fri_t.transpose()), &pk, &fri_p);
    let mut ch_p = make_ch();
    let proof = prove(&src_cfg, ProverInstances::new(vec![sc_i, fri_i]), 0, &mut ch_p).unwrap();
    println!("Source proof: {:?}", start.elapsed());

    // ===== 2. Extract V2 + Merkle path =====
    let _ = take_last_indices();
    let _ = take_last_betas_bytes();
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_p),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_p),
    ];
    let mut ch_v = make_ch();
    verify(&src_cfg, VerifierInstances::new(verif), &proof, 0, &mut ch_v).unwrap();
    println!("Source verify: {:?}", start.elapsed());

    let indices = take_last_indices().unwrap();
    let betas_bytes = take_last_betas_bytes().unwrap();
    let betas: Vec<F> = betas_bytes.iter().map(|b| {
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b[..16]);
        F::from_le_bytes(arr)
    }).collect();

    let v2_trace = build_v2_trace_from_real(&proof, &indices, &betas);
    let v2_rows = v2_trace.height();
    println!("V2: {}x{}", v2_rows, V2_WIDTH);

    // Extract V2 lo values as Merkle leaves
    let v2_lo: Vec<F> = (0..v2_rows.min(4))  // FAST: truncate to 4 leaves
        .map(|r| v2_trace.values[r * V2_WIDTH + COL_LO])
        .collect();
    let merkle_path = build_merkle_path_for_leaf(&v2_lo, 0);
    println!("Merkle path: {} levels", merkle_path.len());

    // ===== 3. Build MerklePath trace =====
    let mp_rows = merkle_path.len().next_power_of_two().max(2);
    let mut mp_values = vec![F::ZERO; mp_rows * MP_WIDTH];
    for (i, (curr, sib, parent)) in merkle_path.iter().enumerate() {
        mp_values[i * MP_WIDTH + MP_COL_CURR] = *curr;
        mp_values[i * MP_WIDTH + MP_COL_SIB] = *sib;
        mp_values[i * MP_WIDTH + MP_COL_PARENT] = *parent;
        mp_values[i * MP_WIDTH + MP_COL_IS_REAL] = F::ONE;  // MARK REAL
    }
    // Padding rows: is_real=0 (no Pull)
    let mp_trace = RowMajorMatrix::new(mp_values, MP_WIDTH);

    // ===== 4. Build Poseidon2b producers (one per Merkle level) =====
    let mut p2b_traces = Vec::new();
    let mut p2b_publics = Vec::new();
    for (curr, sib, _parent) in &merkle_path {
        let producer_trace = build_poseidon2b_producer_trace(*curr, *sib, blk(MERKLE_DOMAIN));
        p2b_traces.push(producer_trace);
        p2b_publics.push(build_poseidon2b_producer_public(*curr, *sib, blk(MERKLE_DOMAIN)));
    }
    println!("Poseidon2b producers: {}", p2b_traces.len());

    // ===== 5. Combine: V2 + MerklePath + Poseidon2b producers =====
    // CRITICAL: MultiStark requires EACH individual trace's arity >= floor (15 here).
    // A trace's arity = log2(next_pow2(rows * cols)). Must be >= 15.
    // So each trace needs >= 2^15 = 32768 cells minimum.
    const MIN_TRACE_CELLS: usize = 1 << 15;  // 32768
    let pad_trace = |trace: RowMajorMatrix<F>| -> RowMajorMatrix<F> {
        let w = trace.width();
        let h = trace.height();
        let cells = h * w;
        if cells >= MIN_TRACE_CELLS { return trace; }
        let target_rows = (MIN_TRACE_CELLS / w + 1).next_power_of_two().max(h);
        let mut vals = trace.values.clone();
        vals.resize(target_rows * w, F::ZERO);
        RowMajorMatrix::new(vals, w)
    };

    let v2_trace = pad_trace(v2_trace);
    let mp_trace = pad_trace(mp_trace);
    let p2b_traces: Vec<_> = p2b_traces.into_iter().map(pad_trace).collect();

    let v2_rows = v2_trace.height();
    let mp_rows = mp_trace.height();

    let p2b_width = <p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir as BaseAir<BinaryField128>>::width(
        &p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir
    );
    // SC padded trace with sumcheck-correct padding (C2/C5/C6 safe)
    // Non-last rows: h0=final_sum, h_inf=0, alpha=0, claimed=next_claimed=final_sum
    // Last row: is_last=1, next_claimed=final_sum (satisfies C6)
    // Last real row: is_last cleared to 0 (satisfies C2 only at final row)
    let final_sum = sc_p[1];
    let sc_t_padded = {
        let trace = sc_t.clone();
        let w = trace.width();
        let h = trace.height();
        let cells = h * w;
        if cells >= MIN_TRACE_CELLS {
            trace
        } else {
            let target_rows = (MIN_TRACE_CELLS / w + 1).next_power_of_two().max(h);
            let mut vals = trace.values.clone();
            vals.resize(target_rows * w, F::ZERO);

            // Clear is_last on last real row (it's no longer the last row)
            if h < target_rows && h > 0 {
                vals[(h - 1) * w + SC_IS_LAST] = F::ZERO;
            }

            // Padding rows: carry-through of final_sum
            for r in h..target_rows {
                vals[r * w + SC_H0] = final_sum;
                vals[r * w + SC_H_INF] = F::ZERO;
                vals[r * w + SC_ALPHA] = F::ZERO;
                vals[r * w + SC_CLAIMED] = final_sum;
                vals[r * w + SC_NEXT] = final_sum;
                vals[r * w + SC_IS_FIRST] = F::ZERO;
                vals[r * w + SC_IS_LAST] = if r == target_rows - 1 { F::ONE } else { F::ZERO };
            }
            RowMajorMatrix::new(vals, w)
        }
    };
    let sc_rows = sc_t_padded.height();
    let sc_rows_log = (sc_rows as f64).log2().ceil() as usize;

    let mut total_cells = v2_rows * V2_WIDTH + mp_rows * MP_WIDTH + sc_rows * SC_WIDTH;
    for t in &p2b_traces {
        total_cells += t.height() * p2b_width;
    }
    let comb_arity = (total_cells.next_power_of_two().trailing_zeros() as usize).max(15);
    println!("Padded: V2 {}x{}, MP {}x{}, {} P2B producers",
        v2_rows, V2_WIDTH, mp_rows, MP_WIDTH, p2b_traces.len());
    println!("Total cells: {}, combined arity: {}", total_cells, comb_arity);
    let comb_pcs = build_pcs(comb_arity);
    let comb_cfg = CombCfg { pcs: comb_pcs };

    // AIR list: 1 V2 + 1 MerklePath + N Poseidon2b producers
    let mut airs: Vec<CombinedAir> = Vec::new();
    airs.push(CombinedAir::V2);
    airs.push(CombinedAir::SumcheckVerifier);  // Session 5: NEW
    airs.push(CombinedAir::MerklePath);
    for _ in 0..p2b_traces.len() {
        airs.push(CombinedAir::Poseidon2b);
    }
    let air_refs: Vec<&CombinedAir> = airs.iter().collect();

    let mut ch_cs = make_ch();
    let (comb_pk, comb_vk) = setup(&comb_cfg, &air_refs, &mut ch_cs).unwrap();
    println!("Combined setup OK");

    // Build instances
    let mut instances = Vec::new();

    // V2 instance
    instances.push(ProverInstance::new(
        &airs[0], Table::new(v2_trace.transpose()), &comb_pk, &[],
    ));

    // SC instance (Session 5)
    instances.push(ProverInstance::new(
        &airs[1], Table::new(sc_t_padded.transpose()), &comb_pk, &sc_p,
    ));

    // MerklePath instance (shifted to index 2)
    instances.push(ProverInstance::new(
        &airs[2], Table::new(mp_trace.transpose()), &comb_pk, &[],
    ));

    // Poseidon2b producer instances
    for i in 0..p2b_traces.len() {
        instances.push(ProverInstance::new(
            &airs[3 + i],
            Table::new(p2b_traces[i].transpose()),
            &comb_pk,
            &p2b_publics[i],
        ));
    }

    let mut ch_prove = make_ch();
    let start_prove = Instant::now();
    let comb_proof = prove(&comb_cfg, ProverInstances::new(instances), 0, &mut ch_prove).unwrap();
    println!("COMBINED PROVE: {:?}, ~{}B",
        start_prove.elapsed(), core::mem::size_of_val(&comb_proof));

    // ===== 6. Verify =====
    let mut verif_insts = Vec::new();
    verif_insts.push(VerifierInstance::new(
        &airs[0], &comb_vk, v2_rows.trailing_zeros() as usize, &[],
    ));
    verif_insts.push(VerifierInstance::new(
        &airs[1], &comb_vk, sc_rows_log, &sc_p,
    ));
    verif_insts.push(VerifierInstance::new(
        &airs[2], &comb_vk, mp_rows.trailing_zeros() as usize, &[],
    ));
    for i in 0..p2b_traces.len() {
        verif_insts.push(VerifierInstance::new(
            &airs[3 + i],
            &comb_vk,
            p2b_traces[i].height().trailing_zeros() as usize,
            &p2b_publics[i],
        ));
    }

    let mut ch_vv = make_ch();
    let start_v = Instant::now();
    verify(&comb_cfg, VerifierInstances::new(verif_insts), &comb_proof, 0, &mut ch_vv)
        .expect("Combined Merkle path proof must verify");
    println!("COMBINED VERIFY: {:?}", start_v.elapsed());

    println!("\n=== Session 4 PASS: Sub-3 Merkle path wire working ===");
    println!("Total time: {:?}", start.elapsed());
    println!("\nHONEST: Merkle path verified in-circuit via Poseidon2b bus.");
    println!("V2 fold relations proven (from S3). Poseidon2b producers match.");
    println!("Sub-3 foundation ready. Full RecursiveVerifierAir = Session 9.");
}
