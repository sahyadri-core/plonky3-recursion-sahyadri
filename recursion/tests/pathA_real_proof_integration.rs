//! Path A integration: CompressedSumcheckAir verifies real proof's sumcheck.
//!
//! # Semantic validation (this test)
//! 1. Generate real MultiStarkProof (SC + FRI, 2 AIRs)
//! 2. Extract sumcheck: `proof.sumcheck.round_polys` + `claimed_sum`
//! 3. Extract alphas via Plonky3's native verifier
//! 4. Build CompressedSumcheckAir trace with this data
//! 5. PROVE + VERIFY with CompressedSumcheckAir
//! 6. **KEY ASSERT**: our interpolation final value == Plonky3's `final_sum`
//!
//! If (6) passes, our Lagrange interpolation semantics exactly match Plonky3's.
//! This is the prerequisite for full Path A (transcript replay is remaining).
//!
//! # Not in scope
//! - Alpha derivation from transcript (in-circuit) -- T1.5d Path A step 4
//! - Bit gadget byte binding to Blake3 block -- separate (BitDecompAir)
//! - Full adversarial soundness -- requires alpha in-circuit

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

/// Native 5-point Lagrange interpolation over {0,1,2,3,4}.
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
fn compressed_sumcheck_validates_real_proof_semantics() {
    // ========== 1. Generate real proof (SC + FRI, 2 AIRs) ==========
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let raw_cells = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH;
    let arity = raw_cells.next_power_of_two().trailing_zeros() as usize;
    println!("Generating proof: arity {}", arity);

    let config = build_config(arity);
    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;
    let mut ch_setup = make_ch();
    let (pk, _vk) = setup(&config, &[&sc_air, &fri_air], &mut ch_setup).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);
    let mut ch_prove = make_ch();
    let proof = prove(&config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_prove).unwrap();

    let num_rounds = proof.sumcheck.round_polys.len();
    let degree = proof.sumcheck.round_polys[0].len();
    println!("Real proof sumcheck: {} rounds x {} evals", num_rounds, degree);
    assert_eq!(num_rounds, 2, "expected 2 rounds");
    assert_eq!(degree, 4, "expected 4 evals per round");

    // ========== 2. Extract alphas via Plonky3's native verifier ==========
    let mut ch_v = make_ch();
    let (alphas_point, final_sum) = proof.sumcheck
        .verify(&mut ch_v, num_rounds, degree, 0)
        .expect("Plonky3 native verify must succeed");
    println!("Plonky3 final_sum = {:?}", final_sum);
    println!("Plonky3 alphas[0] = {:?}", alphas_point[0]);

    // ========== 3. Build CompressedSumcheckAir trace from real data ==========
    let claimed = proof.sumcheck.claimed_sum;
    println!("claimed_sum = {:?}", claimed);

    let mut values = vec![F::ZERO; num_rounds * CS_WIDTH];
    let mut running = claimed;
    for r in 0..num_rounds {
        let evals = &proof.sumcheck.round_polys[r];
        let alpha = alphas_point[r];
        // Reconstruct h(0)..h(4) from [evals[0], sum+evals[0], evals[1], evals[2], evals[3]]
        let h_native: [F; 5] = [evals[0], running + evals[0], evals[1], evals[2], evals[3]];
        let running_out = lagrange_eval_native(h_native, alpha);

        values[r * CS_WIDTH + COL_EVALS0] = evals[0];
        values[r * CS_WIDTH + COL_EVALS1] = evals[1];
        values[r * CS_WIDTH + COL_EVALS2] = evals[2];
        values[r * CS_WIDTH + COL_EVALS3] = evals[3];
        values[r * CS_WIDTH + COL_RUNNING_IN] = running;
        values[r * CS_WIDTH + COL_RUNNING_OUT] = running_out;
        values[r * CS_WIDTH + COL_CHALLENGE] = alpha;
        if r == 0 { values[r * CS_WIDTH + COL_IS_FIRST] = F::ONE; }
        if r == num_rounds - 1 { values[r * CS_WIDTH + COL_IS_LAST] = F::ONE; }
        running = running_out;
    }

    // ========== 4. KEY VALIDATION: our interp == Plonky3's ==========
    assert_eq!(running, final_sum,
        "SEMANTIC MATCH: our final running_out must equal Plonky3's final_sum");
    println!("\n*** SEMANTIC MATCH: our interp == Plonky3's ***");

    // ========== 5. Prove + verify with CompressedSumcheckAir ==========
    let cs_air = CompressedSumcheckAir::new();
    let cs_trace = RowMajorMatrix::new(values, CS_WIDTH);
    let cs_public = vec![claimed, final_sum];

    // Pad to power-of-2 with dummy rows (is_first=0, is_last=0, all zero)
    let target_rows = num_rounds.next_power_of_two().max(2);
    let mut padded = cs_trace.values.clone();
    padded.resize(target_rows * CS_WIDTH, F::ZERO);
    let padded_trace = RowMajorMatrix::new(padded, CS_WIDTH);
    let log_h = target_rows.trailing_zeros() as usize;

    let cs_arity = (target_rows * CS_WIDTH).next_power_of_two().trailing_zeros() as usize;
    println!("CS arity = {}, log_h = {}", cs_arity, log_h);
    let cs_config = build_config(cs_arity);
    let mut ch_s = make_ch();
    let (cs_pk, cs_vk) = setup(&cs_config, &[&cs_air], &mut ch_s).unwrap();

    let inst = ProverInstance::new(&cs_air, Table::new(padded_trace.transpose()), &cs_pk, &cs_public);
    let mut ch_p = make_ch();
    let cs_proof = prove(&cs_config, ProverInstances::new(vec![inst]), 0, &mut ch_p).unwrap();
    println!("PROVE {:?}, ~{}B", std::time::Instant::now().elapsed(), core::mem::size_of_val(&cs_proof));

    let verif = VerifierInstance::new(&cs_air, &cs_vk, log_h, &cs_public);
    let mut ch_vv = make_ch();
    verify(&cs_config, VerifierInstances::new(vec![verif]), &cs_proof, 0, &mut ch_vv)
        .expect("CompressedSumcheckAir must verify real proof's sumcheck");

    println!("\n=== Path A INTEGRATION PASS ===");
    println!("CompressedSumcheckAir verifies REAL proof's sumcheck");
    println!("Our Lagrange interpolation matches Plonky3 exactly");
}

#[test]
#[ignore]
fn compressed_sumcheck_rejects_tampered_alpha() {
    // Build valid trace (from real proof), then tamper alpha -> prove fails
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let raw_cells = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH;
    let arity = raw_cells.next_power_of_two().trailing_zeros() as usize;
    let config = build_config(arity);
    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;
    let mut ch_setup = make_ch();
    let (pk, _) = setup(&config, &[&sc_air, &fri_air], &mut ch_setup).unwrap();
    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);
    let mut ch_p = make_ch();
    let proof = prove(&config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_p).unwrap();

    let mut ch_v = make_ch();
    let num_rounds = proof.sumcheck.round_polys.len();
    let degree = proof.sumcheck.round_polys[0].len();
    let (alphas_point, final_sum) = proof.sumcheck.verify(&mut ch_v, num_rounds, degree, 0).unwrap();
    let claimed = proof.sumcheck.claimed_sum;

    let mut values = vec![F::ZERO; num_rounds * CS_WIDTH];
    let mut running = claimed;
    for r in 0..num_rounds {
        let evals = &proof.sumcheck.round_polys[r];
        let alpha = if r == 0 { alphas_point[r] + F::ONE } else { alphas_point[r] };
        let h_native: [F; 5] = [evals[0], running + evals[0], evals[1], evals[2], evals[3]];
        let running_out = lagrange_eval_native(h_native, alpha);
        values[r * CS_WIDTH + COL_EVALS0] = evals[0];
        values[r * CS_WIDTH + COL_EVALS1] = evals[1];
        values[r * CS_WIDTH + COL_EVALS2] = evals[2];
        values[r * CS_WIDTH + COL_EVALS3] = evals[3];
        values[r * CS_WIDTH + COL_RUNNING_IN] = running;
        values[r * CS_WIDTH + COL_RUNNING_OUT] = running_out;
        values[r * CS_WIDTH + COL_CHALLENGE] = alpha;
        if r == 0 { values[r * CS_WIDTH + COL_IS_FIRST] = F::ONE; }
        if r == num_rounds - 1 { values[r * CS_WIDTH + COL_IS_LAST] = F::ONE; }
        running = running_out;
    }

    // Constraints are checked in `verify()` or `check_constraints()`, NOT `prove()`.
    // Use `check_constraints` on the tampered trace -- it panics on violated constraint.
    use p3_air::check_constraints;
    let cs_air = CompressedSumcheckAir::new();
    let target_rows = num_rounds.next_power_of_two().max(2);
    let mut padded = values.clone();
    padded.resize(target_rows * CS_WIDTH, F::ZERO);
    let cs_trace = RowMajorMatrix::new(padded, CS_WIDTH);
    let cs_public = vec![claimed, final_sum];

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&cs_air, &cs_trace, &cs_public);
    }));
    match result {
        Err(_) => println!("PASS: tampered alpha rejected (C3/C5 violated)"),
        Ok(_) => panic!("tampered alpha must fail"),
    }
}
