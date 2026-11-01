//! Path A assembly: SC + CompressedSumcheck + FRI in one MultiStark.
//!
//! # Goal
//! Verify that Path A's three AIRs can coexist in a single MultiStark
//! proof, using REAL MultiStarkProof data (extracted, not synthetic).
//!
//! # Pipeline
//! 1. Generate real proof (SC + FRI, 2 AIRs) → MultiStarkProof
//! 2. Extract sumcheck data + alphas (via Plonky3 native verify)
//! 3. Build CompressedSumcheckAir trace from extracted data
//! 4. Combine SC + CS + FRI traces in one MultiStark
//! 5. PROVE + VERIFY
//!
//! # Soundness status
//! - SC verifies its own fold constraints
//! - CS verifies extracted sumcheck (semantic match with Plonky3)
//! - FRI verifies its own fold
//! - Public values bound across all three (Path B statement binding)
//!
//! # NOT in scope
//! - Alpha in-circuit (transcript replay): next 3-5 day research
//! - Bit gadget byte binding: next 3-5 days
//! - Adversarial soundness: requires alpha in-circuit

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

const SC_ROWS: usize = 2;
const FRI_ROWS: usize = 4;

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

// Combined assembly AIR
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
            Self::CompressedSumcheck => {
                // Note: CompressedSumcheckAir has state (lagrange coeffs).
                // For assembly test, we instantiate it fresh. In production,
                // it would be pre-instantiated and passed by reference.
                CompressedSumcheckAir::new().eval(b);
            }
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

fn lagrange_eval_native(h: [F; 5], alpha: F) -> F {
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

#[test]
#[ignore]
fn path_a_three_air_assembly() {
    // ========== 1. Generate real proof ==========
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let raw_cells = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH;
    let src_arity = raw_cells.next_power_of_two().trailing_zeros() as usize;

    let src_config = build_config(src_arity);
    let sc_src = SrcAir::SumcheckVerifier;
    let fri_src = SrcAir::FriVerifier;
    let mut ch_s = make_ch();
    let (src_pk, _) = setup(&src_config, &[&sc_src, &fri_src], &mut ch_s).unwrap();

    let sc_inst = ProverInstance::new(&sc_src, Table::new(sc_trace.transpose()), &src_pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_src, Table::new(fri_trace.transpose()), &src_pk, &fri_public);
    let mut ch_p = make_ch();
    let proof = prove(&src_config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_p).unwrap();
    println!("Real proof generated, ~{} B", core::mem::size_of_val(&proof));

    // ========== 2. Extract sumcheck + alphas ==========
    let num_rounds = proof.sumcheck.round_polys.len();
    let degree = proof.sumcheck.round_polys[0].len();
    let claimed = proof.sumcheck.claimed_sum;
    let mut ch_v = make_ch();
    let (alphas_point, final_sum) = proof.sumcheck.verify(&mut ch_v, num_rounds, degree, 0).unwrap();
    println!("Sumcheck: {} rounds, degree {}, claimed=0x0", num_rounds, degree);

    // ========== 3. Build CS trace from extracted data ==========
    let mut cs_values = vec![F::ZERO; num_rounds * CS_WIDTH];
    let mut running = claimed;
    for r in 0..num_rounds {
        let evals = &proof.sumcheck.round_polys[r];
        let alpha = alphas_point[r];
        let h_native: [F; 5] = [evals[0], running + evals[0], evals[1], evals[2], evals[3]];
        let running_out = lagrange_eval_native(h_native, alpha);
        cs_values[r * CS_WIDTH + COL_EVALS0] = evals[0];
        cs_values[r * CS_WIDTH + COL_EVALS1] = evals[1];
        cs_values[r * CS_WIDTH + COL_EVALS2] = evals[2];
        cs_values[r * CS_WIDTH + COL_EVALS3] = evals[3];
        cs_values[r * CS_WIDTH + COL_RUNNING_IN] = running;
        cs_values[r * CS_WIDTH + COL_RUNNING_OUT] = running_out;
        cs_values[r * CS_WIDTH + COL_CHALLENGE] = alpha;
        if r == 0 { cs_values[r * CS_WIDTH + COL_IS_FIRST] = F::ONE; }
        if r == num_rounds - 1 { cs_values[r * CS_WIDTH + COL_IS_LAST] = F::ONE; }
        running = running_out;
    }

    // Pad CS to power-of-2
    let cs_target_rows = num_rounds.next_power_of_two().max(2);
    cs_values.resize(cs_target_rows * CS_WIDTH, F::ZERO);
    let cs_trace = RowMajorMatrix::new(cs_values, CS_WIDTH);
    let cs_public = vec![claimed, final_sum];

    // ========== 4. Combine SC + CS + FRI in one MultiStark ==========
    // Note: SC and FRI are regenerated (small) -- CS is new
    let (sc_trace_asm, sc_public_asm) = build_sc_trace();
    let (fri_trace_asm, fri_public_asm) = build_fri_trace();

    let total_cells = SC_ROWS * SC_WIDTH + cs_target_rows * CS_WIDTH + FRI_ROWS * FRI_WIDTH;
    let arity = total_cells.next_power_of_two().trailing_zeros() as usize;
    println!("Assembly arity = {}", arity);

    let config = build_config(arity);
    let sc_air = AssemblyAir::SumcheckVerifier;
    let cs_air = AssemblyAir::CompressedSumcheck;
    let fri_air = AssemblyAir::FriVerifier;

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &cs_air, &fri_air], &mut ch_setup).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace_asm.transpose()), &pk, &sc_public_asm);
    let cs_inst = ProverInstance::new(&cs_air, Table::new(cs_trace.transpose()), &pk, &cs_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace_asm.transpose()), &pk, &fri_public_asm);

    let mut ch_prove = make_ch();
    let start = Instant::now();
    let asm_proof = prove(
        &config,
        ProverInstances::new(vec![sc_inst, cs_inst, fri_inst]),
        0,
        &mut ch_prove,
    ).unwrap();
    let prove_time = start.elapsed();
    println!("ASSEMBLY PROVE {:?}, ~{} B", prove_time, core::mem::size_of_val(&asm_proof));

    // ========== 5. Verify ==========
    let sc_log_h = SC_ROWS.trailing_zeros() as usize;
    let cs_log_h = cs_target_rows.trailing_zeros() as usize;
    let fri_log_h = FRI_ROWS.trailing_zeros() as usize;

    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, sc_log_h, &sc_public_asm),
        VerifierInstance::new(&cs_air, &vk, cs_log_h, &cs_public),
        VerifierInstance::new(&fri_air, &vk, fri_log_h, &fri_public_asm),
    ];
    let mut ch_v = make_ch();
    let start = Instant::now();
    verify(&config, VerifierInstances::new(verif), &asm_proof, 0, &mut ch_v)
        .expect("Path A 3-AIR assembly must verify");
    println!("ASSEMBLY VERIFY {:?}", start.elapsed());

    println!("\n=== Path A 3-AIR ASSEMBLY PASS ===");
    println!("SC + CompressedSumcheck + FRI all coexist");
    println!("CompressedSumcheck bound to real proof's sumcheck data");
}

#[test]
#[ignore]
fn path_a_assembly_rejects_tampered_cs() {
    // Same pipeline but tamper CS's public final_sum
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let raw_cells = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH;
    let src_arity = raw_cells.next_power_of_two().trailing_zeros() as usize;
    let src_config = build_config(src_arity);
    let sc_src = SrcAir::SumcheckVerifier;
    let fri_src = SrcAir::FriVerifier;
    let mut ch_s = make_ch();
    let (src_pk, _) = setup(&src_config, &[&sc_src, &fri_src], &mut ch_s).unwrap();
    let sc_inst = ProverInstance::new(&sc_src, Table::new(sc_trace.transpose()), &src_pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_src, Table::new(fri_trace.transpose()), &src_pk, &fri_public);
    let mut ch_p = make_ch();
    let proof = prove(&src_config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_p).unwrap();

    let num_rounds = proof.sumcheck.round_polys.len();
    let degree = proof.sumcheck.round_polys[0].len();
    let claimed = proof.sumcheck.claimed_sum;
    let mut ch_v = make_ch();
    let (alphas_point, final_sum) = proof.sumcheck.verify(&mut ch_v, num_rounds, degree, 0).unwrap();

    let mut cs_values = vec![F::ZERO; num_rounds * CS_WIDTH];
    let mut running = claimed;
    for r in 0..num_rounds {
        let evals = &proof.sumcheck.round_polys[r];
        let alpha = alphas_point[r];
        let h_native: [F; 5] = [evals[0], running + evals[0], evals[1], evals[2], evals[3]];
        let running_out = lagrange_eval_native(h_native, alpha);
        cs_values[r * CS_WIDTH + COL_EVALS0] = evals[0];
        cs_values[r * CS_WIDTH + COL_EVALS1] = evals[1];
        cs_values[r * CS_WIDTH + COL_EVALS2] = evals[2];
        cs_values[r * CS_WIDTH + COL_EVALS3] = evals[3];
        cs_values[r * CS_WIDTH + COL_RUNNING_IN] = running;
        cs_values[r * CS_WIDTH + COL_RUNNING_OUT] = running_out;
        cs_values[r * CS_WIDTH + COL_CHALLENGE] = alpha;
        if r == 0 { cs_values[r * CS_WIDTH + COL_IS_FIRST] = F::ONE; }
        if r == num_rounds - 1 { cs_values[r * CS_WIDTH + COL_IS_LAST] = F::ONE; }
        running = running_out;
    }
    let cs_target_rows = num_rounds.next_power_of_two().max(2);
    cs_values.resize(cs_target_rows * CS_WIDTH, F::ZERO);
    let cs_trace = RowMajorMatrix::new(cs_values, CS_WIDTH);

    // TAMPER: CS's public final_sum != what trace proves
    let mut cs_public = vec![claimed, final_sum];
    cs_public[1] = cs_public[1] + F::ONE;

    let (sc_trace_asm, sc_public_asm) = build_sc_trace();
    let (fri_trace_asm, fri_public_asm) = build_fri_trace();
    let total_cells = SC_ROWS * SC_WIDTH + cs_target_rows * CS_WIDTH + FRI_ROWS * FRI_WIDTH;
    let arity = total_cells.next_power_of_two().trailing_zeros() as usize;
    let config = build_config(arity);
    let sc_air = AssemblyAir::SumcheckVerifier;
    let cs_air = AssemblyAir::CompressedSumcheck;
    let fri_air = AssemblyAir::FriVerifier;
    let mut ch_s2 = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &cs_air, &fri_air], &mut ch_s2).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace_asm.transpose()), &pk, &sc_public_asm);
    let cs_inst = ProverInstance::new(&cs_air, Table::new(cs_trace.transpose()), &pk, &cs_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace_asm.transpose()), &pk, &fri_public_asm);
    let mut ch_pp = make_ch();
    let asm_proof = prove(
        &config,
        ProverInstances::new(vec![sc_inst, cs_inst, fri_inst]),
        0,
        &mut ch_pp,
    ).unwrap();

    let sc_log_h = SC_ROWS.trailing_zeros() as usize;
    let cs_log_h = cs_target_rows.trailing_zeros() as usize;
    let fri_log_h = FRI_ROWS.trailing_zeros() as usize;
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, sc_log_h, &sc_public_asm),
        VerifierInstance::new(&cs_air, &vk, cs_log_h, &cs_public),
        VerifierInstance::new(&fri_air, &vk, fri_log_h, &fri_public_asm),
    ];
    let mut ch_vv = make_ch();
    let result = verify(&config, VerifierInstances::new(verif), &asm_proof, 0, &mut ch_vv);
    assert!(result.is_err(), "tampered CS public must fail verify");
    println!("PASS: tampered CS public rejected: {:?}", result.err());
}
