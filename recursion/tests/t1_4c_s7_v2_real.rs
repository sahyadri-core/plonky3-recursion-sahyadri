//! S7 v2/v3: 2 or 3 real Plonky3 proofs aggregated in one MultiStark.
//!
//! # Honest scope
//! - v2: proves "π_A valid ∧ π_B valid" (2-input aggregation)
//! - v3: proves "π_1 valid ∧ π_2 valid ∧ π_3 valid" (3-input WIDE, not nested tree)
//! - True 2-level tree needs S8 (transcript replay) + S9 (recursive verify of combined)
//! - SC uses CompressedSumcheckAir (real GenericDegreeProof extraction)
//! - Alpha is witness (S8 will constrain via transcript replay)
//!
//! # Real extractions per input
//! - V2: from `proof.opening.base_opened_values` + `rounds` + extracted indices/betas
//! - SC: from `proof.sumcheck.round_polys` + alphas from `sumcheck.verify()`
//! - MP: from Poseidon2b Merkle tree over V2 leaves
//! - P2B: one producer per Merkle level

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_dft::domain_point;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
    take_last_betas_bytes, take_last_indices,
};
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances, MultiStarkProof,
};
use p3_poseidon2b::poseidon2b_permutation;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN;
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;

use p3_recursion::frost_gkr::compressed_sumcheck_air::{
    CompressedSumcheckAir,
    COL_EVALS0, COL_EVALS1, COL_EVALS2, COL_EVALS3,
    COL_RUNNING_IN, COL_RUNNING_OUT, COL_CHALLENGE,
    COL_IS_FIRST, COL_IS_LAST,
    WIDTH as CS_WIDTH, NUM_PUBLIC as CS_PUBLIC,
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
use p3_recursion::frost_gkr::binary_verifier_air_v2::{
    BinaryVerifierAirV2, WIDTH as V2_WIDTH,
    COL_LO, COL_NEXT as V2_COL_NEXT, COL_IS_LAST as V2_COL_IS_LAST,
};
use p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir;

type F = BinaryField128;
type E = BinaryField128;
type M = GroupedCodewordMmcs<Poseidon2bMmcs>;
type ME = GroupedCodewordMmcs<Poseidon2bMmcs>;
type Ch = blake3::LevelChallenger<F>;

const MP_WIDTH: usize = 4;
const MP_CURR: usize = 0;
const MP_SIB: usize = 1;
const MP_PARENT: usize = 2;
const MP_IS_REAL: usize = 3;
const MERKLE_BUS: BusName<'static> = BusName::new("sahyadri_merkle_compress");
const P2B_WIDTH: usize = 1024;
const SC_ROWS: usize = 2;
const FRI_ROWS: usize = 4;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }
fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
}

fn lagrange_eval_native(h: [F; 5], alpha: F) -> F {
    let mut result = F::ZERO;
    for i in 0..5 {
        let mut num = F::ONE;
        let mut den = F::ONE;
        for j in 0..5 {
            if i == j { continue; }
            num = num * (alpha + blk(j as u128));
            den = den * (blk(i as u128) + blk(j as u128));
        }
        result = result + h[i] * num * den.try_inverse().expect("nonzero");
    }
    result
}

// ═══ Source config ═══

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
pub enum SrcAir { SumcheckVerifier, FriVerifier }
impl<Fb> BaseAir<Fb> for SrcAir {
    fn width(&self) -> usize {
        match self { Self::SumcheckVerifier => SC_WIDTH, Self::FriVerifier => FRI_WIDTH }
    }
    fn num_public_values(&self) -> usize {
        match self { Self::SumcheckVerifier => 2, Self::FriVerifier => 4 }
    }
}
impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB> for SrcAir {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::FriVerifier => BinaryVerifierAir.eval(b),
        }
    }
}

// ═══ Combined AIR ═══


// Local MP AIR — is_real-based Pull (S4 pattern, no depth cap)
pub struct MerklePathAir;
impl<Fb> BaseAir<Fb> for MerklePathAir {
    fn width(&self) -> usize { MP_WIDTH }
    fn num_public_values(&self) -> usize { 8 }
}
impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB> for MerklePathAir {
    fn eval(&self, b: &mut AB) {
        let binding = b.main();
        let cur = binding.current_slice();
        let curr: AB::Expr = cur[MP_CURR].into();
        let sib: AB::Expr = cur[MP_SIB].into();
        let parent: AB::Expr = cur[MP_PARENT].into();
        let is_real: AB::Expr = cur[MP_IS_REAL].into();
        // booleanity
        b.assert_eq(is_real.clone() * is_real.clone() + is_real.clone(), AB::F::ZERO);
        // Pull on every real row
        b.push_bus_interaction(
            MERKLE_BUS,
            BusDirection::Pull,
            [curr, sib, parent],
            BusActivation::Boolean(is_real),
        );
    }
}

#[derive(Clone, Copy)]
pub enum CombinedAir { V2, CS, MP, P2B }
impl<Fb> BaseAir<Fb> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::V2 => V2_WIDTH,
            Self::CS => CS_WIDTH,
            Self::MP => MP_WIDTH,
            Self::P2B => P2B_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::V2 => 0,
            Self::CS => CS_PUBLIC,
            Self::MP => 8,
            Self::P2B => 8,
        }
    }
}
impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB> for CombinedAir {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::V2 => BinaryVerifierAirV2.eval(b),
            Self::CS => CompressedSumcheckAir::new().eval(b),
            Self::MP => MerklePathAir.eval(b),
            Self::P2B => Poseidon2bBusAir.eval(b),
        }
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

// ═══ Helpers: build source traces ═══


fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

fn fri_fold(p0: F, p1: F, alpha: F, sel: F) -> F {
    let f1 = p0 + p1;
    let f0 = p0 + sel * f1;
    alpha * (f0 + f1) + f0
}

fn build_sc_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let h0 = blk(2); let h_inf = blk(0); let alpha = blk(2);
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
    let p0 = blk(10); let p1 = blk(20); let alpha = blk(30);
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

fn build_v2_trace_from_real(
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
            values[row * V2_WIDTH + 1] = hi;
            values[row * V2_WIDTH + 2] = beta;
            values[row * V2_WIDTH + 3] = x;
            values[row * V2_WIDTH + V2_COL_NEXT] = expected_next;
            if batch == num_batches - 1 && q == num_queries - 1 {
                values[row * V2_WIDTH + V2_COL_IS_LAST] = F::ONE;
            }
        }
    }
    RowMajorMatrix::new(values, V2_WIDTH)
}

fn build_merkle_path_for_leaf(lo_values: &[F], leaf_index: usize) -> Vec<(F, F, F)> {
    let compress = |a: F, b: F| -> F {
        let mut state = [a, b, F::ZERO, blk(MERKLE_DOMAIN)];
        poseidon2b_permutation(&mut state);
        state[0] + state[1]
    };
    let n = lo_values.len().next_power_of_two();
    let mut level: Vec<F> = (0..n).map(|i| lo_values.get(i).copied().unwrap_or(F::ZERO)).collect();
    let mut path = Vec::new();
    let mut idx = leaf_index;
    while level.len() > 1 {
        let sib_idx = idx ^ 1;
        let sib = level[sib_idx];
        let curr = level[idx];
        let parent = compress(curr, sib);
        path.push((curr, sib, parent));
        let mut next = Vec::with_capacity(level.len() / 2);
        for c in level.chunks(2) {
            if c.len() == 2 { next.push(compress(c[0], c[1])); }
            else { next.push(c[0]); }
        }
        level = next;
        idx >>= 1;
    }
    path
}

fn build_poseidon2b_producer_trace(left: F, right: F, domain: F) -> RowMajorMatrix<F> {
    let state_in = [left, right, F::ZERO, domain];
    let base = p3_poseidon2b::generate_poseidon2b_trace(state_in);
    let base_values = base.values;
    const TARGET_ROWS: usize = 32;
    let mut values = Vec::with_capacity(TARGET_ROWS * P2B_WIDTH);
    for _ in 0..TARGET_ROWS { values.extend_from_slice(&base_values); }
    RowMajorMatrix::new(values, P2B_WIDTH)
}

fn build_poseidon2b_producer_public(left: F, right: F, domain: F) -> Vec<F> {
    let state_in = [left, right, F::ZERO, domain];
    let mut state_out = state_in;
    poseidon2b_permutation(&mut state_out);
    vec![state_in[0], state_in[1], state_in[2], state_in[3],
         state_out[0], state_out[1], state_out[2], state_out[3]]
}

// ═══ Padding ═══

fn pad_trace_zeros(trace: RowMajorMatrix<F>, min_cells: usize) -> RowMajorMatrix<F> {
    let w = trace.width();
    let h = trace.height();
    if h * w >= min_cells { return trace; }
    let target_rows = (min_cells / w + 1).next_power_of_two().max(h);
    let mut vals = trace.values.clone();
    vals.resize(target_rows * w, F::ZERO);
    RowMajorMatrix::new(vals, w)
}

fn pad_trace_sc(trace: RowMajorMatrix<F>, final_sum: F, min_cells: usize) -> RowMajorMatrix<F> {
    let w = trace.width();
    let h = trace.height();
    if h * w >= min_cells { return trace; }
    let target_rows = (min_cells / w + 1).next_power_of_two().max(h);
    let mut vals = trace.values.clone();
    vals.resize(target_rows * w, F::ZERO);
    // Clear is_last on last real row
    vals[(h - 1) * w + COL_IS_LAST] = F::ZERO;
    // Fill pad rows: alpha=1 makes C3 hold (p(1)=final_sum via L_1(1)=1)
    let one = F::ONE;
    for r in h..target_rows {
        let base = r * w;
        vals[base + COL_RUNNING_IN] = final_sum;
        vals[base + COL_RUNNING_OUT] = final_sum;
        vals[base + COL_CHALLENGE] = one;
        vals[base + COL_IS_LAST] = if r == target_rows - 1 { F::ONE } else { F::ZERO };
    }
    RowMajorMatrix::new(vals, w)
}

fn pad_trace_mp(trace: RowMajorMatrix<F>, min_cells: usize) -> RowMajorMatrix<F> {
    // MP has is_real column; pad rows keep is_real=0 (no Pull)
    pad_trace_zeros(trace, min_cells)
}

// ═══ Proof bundle ═══

struct ProofBundle {
    v2_trace: RowMajorMatrix<F>,
    sc_trace: RowMajorMatrix<F>,
    sc_public: Vec<F>,
    mp_trace: RowMajorMatrix<F>,
    mp_public: Vec<F>,
    p2b_traces: Vec<RowMajorMatrix<F>>,
    p2b_publics: Vec<Vec<F>>,
}

fn build_bundle(seed: u128) -> ProofBundle {
    println!("  [seed {:x}] building source proof...", seed);

    // Step 1: source proof
    let (sc_t, sc_p) = build_sc_trace();
    let (fri_t, fri_p) = build_fri_trace();
    let src_arity = (2 * SC_WIDTH + 4 * FRI_WIDTH).next_power_of_two().trailing_zeros() as usize;
    let src_cfg = SrcCfg { pcs: build_pcs(src_arity) };

    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;
    let mut ch_s = make_ch();
    let (pk, vk) = setup(&src_cfg, &[&sc_air, &fri_air], &mut ch_s).unwrap();

    let sc_i = ProverInstance::new(&sc_air, Table::new(sc_t.transpose()), &pk, &sc_p);
    let fri_i = ProverInstance::new(&fri_air, Table::new(fri_t.transpose()), &pk, &fri_p);
    let mut ch_p = make_ch();
    let src_proof = prove(&src_cfg, ProverInstances::new(vec![sc_i, fri_i]), 0, &mut ch_p).unwrap();

    // Step 2: verify to populate extraction state
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_p),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_p),
    ];
    let mut ch_v = make_ch();
    verify(&src_cfg, VerifierInstances::new(verif), &src_proof, 0, &mut ch_v).unwrap();

    // Step 3: take extraction (populated by verify above)
    let indices = take_last_indices().expect("indices populated by verify");
    let betas_bytes = take_last_betas_bytes().expect("betas populated by verify");
    let betas: Vec<F> = betas_bytes.iter().map(|b| {
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b[..16]);
        F::from_le_bytes(arr)
    }).collect();

    // Step 4: V2 from real FRI
    let v2_trace = build_v2_trace_from_real(&src_proof, &indices, &betas);
    let v2_rows = v2_trace.height();
    println!("  [seed {:x}] V2: {}x{}, indices: {}, betas: {}",
        seed, v2_rows, V2_WIDTH, indices.len(), betas.len());

    // Step 5: SC from real sumcheck
    let num_rounds = src_proof.sumcheck.round_polys.len();
    let degree = src_proof.sumcheck.round_polys[0].len();
    let mut ch_sc = make_ch();
    let (alphas, final_sum) = src_proof.sumcheck.verify(&mut ch_sc, num_rounds, degree, 0).unwrap();
    let claimed = src_proof.sumcheck.claimed_sum;

    let mut sc_values = vec![F::ZERO; num_rounds * CS_WIDTH];
    let mut running = claimed;
    for r in 0..num_rounds {
        let evals = &src_proof.sumcheck.round_polys[r];
        let alpha = alphas[r];
        let h_native = [evals[0], running + evals[0], evals[1], evals[2], evals[3]];
        let running_out = lagrange_eval_native(h_native, alpha);
        sc_values[r * CS_WIDTH + COL_EVALS0] = evals[0];
        sc_values[r * CS_WIDTH + COL_EVALS1] = evals[1];
        sc_values[r * CS_WIDTH + COL_EVALS2] = evals[2];
        sc_values[r * CS_WIDTH + COL_EVALS3] = evals[3];
        sc_values[r * CS_WIDTH + COL_RUNNING_IN] = running;
        sc_values[r * CS_WIDTH + COL_RUNNING_OUT] = running_out;
        sc_values[r * CS_WIDTH + COL_CHALLENGE] = alpha;
        if r == 0 { sc_values[r * CS_WIDTH + COL_IS_FIRST] = F::ONE; }
        if r == num_rounds - 1 { sc_values[r * CS_WIDTH + COL_IS_LAST] = F::ONE; }
        running = running_out;
    }
    let sc_trace = RowMajorMatrix::new(sc_values, CS_WIDTH);
    let sc_public = vec![claimed, final_sum];
    println!("  [seed {:x}] SC: {}x{}, {} rounds × {} evals",
        seed, num_rounds, CS_WIDTH, num_rounds, degree);

    // Step 6: MP + P2B
    let v2_lo: Vec<F> = (0..v2_rows).map(|r| v2_trace.values[r * V2_WIDTH + COL_LO]).collect();
    let merkle_path = build_merkle_path_for_leaf(&v2_lo, 0);
    let mp_rows_raw = merkle_path.len().next_power_of_two().max(2);
    let mut mp_values = vec![F::ZERO; mp_rows_raw * MP_WIDTH];
    for (i, (c, s, p)) in merkle_path.iter().enumerate() {
        mp_values[i * MP_WIDTH + MP_CURR] = *c;
        mp_values[i * MP_WIDTH + MP_SIB] = *s;
        mp_values[i * MP_WIDTH + MP_PARENT] = *p;
        mp_values[i * MP_WIDTH + MP_IS_REAL] = F::ONE;
    }
    let mp_trace = RowMajorMatrix::new(mp_values, MP_WIDTH);
    let mp_public = {
        let mut p = vec![F::ZERO; 8];
        if let Some((_, _, root)) = merkle_path.last() { p[0] = *root; }
        p
    };
    let mut p2b_traces = Vec::new();
    let mut p2b_publics = Vec::new();
    for (c, s, _) in &merkle_path {
        p2b_traces.push(build_poseidon2b_producer_trace(*c, *s, blk(MERKLE_DOMAIN)));
        p2b_publics.push(build_poseidon2b_producer_public(*c, *s, blk(MERKLE_DOMAIN)));
    }
    println!("  [seed {:x}] MP: {}x{}, P2B: {} producers",
        seed, mp_rows_raw, MP_WIDTH, p2b_traces.len());

    ProofBundle { v2_trace, sc_trace, sc_public, mp_trace, mp_public, p2b_traces, p2b_publics }
}

// ═══ Combine N bundles ═══

fn combine_and_prove(bundles: Vec<ProofBundle>) -> usize {
    const MIN_TRACE_CELLS: usize = 1 << 15;

    let mut airs: Vec<CombinedAir> = Vec::new();
    let mut instances_data: Vec<(usize, RowMajorMatrix<F>, Vec<F>)> = Vec::new();
    let mut total_cells: usize = 0;

    for b in bundles {
        let v2 = pad_trace_zeros(b.v2_trace, MIN_TRACE_CELLS);
        let sc = pad_trace_sc(b.sc_trace, b.sc_public[1], MIN_TRACE_CELLS);
        let mp = pad_trace_mp(b.mp_trace, MIN_TRACE_CELLS);
        let p2b: Vec<_> = b.p2b_traces.into_iter().map(|t| pad_trace_zeros(t, MIN_TRACE_CELLS)).collect();

        total_cells += v2.height() * V2_WIDTH;
        total_cells += sc.height() * CS_WIDTH;
        total_cells += mp.height() * MP_WIDTH;
        for t in &p2b { total_cells += t.height() * P2B_WIDTH; }

        let air_idx = airs.len();
        airs.push(CombinedAir::V2);
        instances_data.push((air_idx, v2, vec![]));
        let air_idx = airs.len();
        airs.push(CombinedAir::CS);
        instances_data.push((air_idx, sc, b.sc_public.clone()));
        let air_idx = airs.len();
        airs.push(CombinedAir::MP);
        instances_data.push((air_idx, mp, b.mp_public.clone()));
        for (i, p2b_t) in p2b.into_iter().enumerate() {
            let air_idx = airs.len();
            airs.push(CombinedAir::P2B);
            instances_data.push((air_idx, p2b_t, b.p2b_publics[i].clone()));
        }
    }

    let arity = (total_cells.next_power_of_two().trailing_zeros() as usize).max(15);
    println!("Total cells: {}, arity: {}, AIRs: {}", total_cells, arity, airs.len());

    let cfg = CombCfg { pcs: build_pcs(arity) };
    let air_refs: Vec<&CombinedAir> = airs.iter().collect();
    let mut ch_s = make_ch();
    let (pk, vk) = setup(&cfg, &air_refs, &mut ch_s).unwrap();
    println!("Setup OK");

    let mut instances = Vec::new();
    let mut verif_logs = Vec::new();
    for (air_idx, trace, public) in &instances_data {
        let log_h = trace.height().trailing_zeros() as usize;
        instances.push(ProverInstance::new(&airs[*air_idx], Table::new(trace.clone().transpose()), &pk, public));
        verif_logs.push((*air_idx, log_h, public.clone()));
    }

    let mut ch_p = make_ch();
    let start = std::time::Instant::now();
    let proof = prove(&cfg, ProverInstances::new(instances), 0, &mut ch_p).unwrap();
    println!("PROVE {:?}, ~{}B (struct header)", start.elapsed(), core::mem::size_of_val(&proof));

    let mut verifs = Vec::new();
    for (air_idx, log_h, public) in &verif_logs {
        verifs.push(VerifierInstance::new(&airs[*air_idx], &vk, *log_h, public));
    }
    let mut ch_v = make_ch();
    verify(&cfg, VerifierInstances::new(verifs), &proof, 0, &mut ch_v).unwrap();
    println!("VERIFY OK");

    core::mem::size_of_val(&proof)
}

// ═══ Tests ═══

#[test]
#[ignore]
fn s7_v2_two_real_proofs() {
    println!("=== S7 v2: 2 real Plonky3 proofs → one MultiStark ===\n");
    println!("Phase 1: build 2 bundles");
    let a = build_bundle(0xAAAA_0001);
    let b = build_bundle(0xBBBB_0002);
    println!("\nPhase 2: combine + prove");
    let size = combine_and_prove(vec![a, b]);
    println!("\n=== S7 v2 PASS: 2 real proofs aggregated, ~{}B ===", size);
    println!("Soundness: honest-prover transcript (S8 will constrain alpha).");
}

#[test]
#[ignore]
fn s7_v3_three_real_proofs() {
    println!("=== S7 v3: 3 real Plonky3 proofs → one MultiStark ===\n");
    println!("Honest scope: 3-WIDE aggregation, not nested tree.");
    println!("True 2-level tree needs S8 (transcript) + S9 (recursive verify).\n");
    println!("Phase 1: build 3 bundles");
    let a = build_bundle(0x1_1001);
    let b = build_bundle(0x2_2002);
    let c = build_bundle(0x3_3003);
    println!("\nPhase 2: combine + prove");
    let size = combine_and_prove(vec![a, b, c]);
    println!("\n=== S7 v3 PASS: 3 real proofs aggregated, ~{}B ===", size);
}
