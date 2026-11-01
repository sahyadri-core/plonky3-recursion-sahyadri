//! T1.2b step 3: diagnose FRI fold relationship.
//!
//! # Goal
//! Discover: how do `opened_values[r][q]` (1 symbol per query) fold into
//! `opened_values[r+1][q']`? Test hypotheses:
//!   H1: pairs = adjacent queries (q, q+1), fold to q/2
//!   H2: base_opened_values pairs with opened_values[0]
//!   H3: alpha derived from challenge (need replay)
//!
//! # Method
//! For each hypothesis, test if fold(pair, alpha) matches next-round values
//! for ANY alpha guess. Report which hypothesis has any matches.
//!
//! # Real
//! Uses real proof data. Diagnostic only. Reveals structure.

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
pub enum SrcAir { SumcheckVerifier, FriVerifier }

impl<F> BaseAir<F> for SrcAir {
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

fn build_config(arity: usize) -> Cfg {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Tree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    let round = RoundTree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    Cfg { pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap() }
}

fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
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
    let fo = p0 + blk(1) * (p0 + p1) + alpha * (p1 + blk(1) * (p0 + p1));
    let mut v = vec![F::ZERO; 4 * FRI_WIDTH];
    v[FRI_PAIR0] = p0; v[FRI_PAIR1] = p1; v[FRI_ALPHA] = alpha;
    v[FRI_NEXT] = fo; v[FRI_SEL] = F::ONE;
    v[3 * FRI_WIDTH + 5] = F::ONE; v[3 * FRI_WIDTH + 6] = F::ONE;
    (RowMajorMatrix::new(v, FRI_WIDTH), vec![F::ZERO; 4])
}

#[test]
#[ignore]
fn diagnose_fold_structure() {
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
    let num_rounds = opening.rounds.len();
    let num_queries = opening.rounds[0].opened_values.len();

    println!("=== Diagnostic ===");
    println!("Rounds: {}, Queries: {}", num_rounds, num_queries);
    println!("Base opened_values count: {}", opening.base_opened_values.len());
    println!("Base_opened_values[0] = {:?}", opening.base_opened_values[0]);

    // Print first 4 values of round 0
    println!("\nRound 0 first 4 queries:");
    for q in 0..4.min(num_queries) {
        println!("  q[{}] = {:?}", q, opening.rounds[0].opened_values[q]);
    }

    println!("\nRound 1 first 4 queries:");
    for q in 0..4.min(num_queries) {
        println!("  q[{}] = {:?}", q, opening.rounds[1].opened_values[q]);
    }

    // Hypothesis H1: (2i, 2i+1) fold to i in next round with alpha=1
    println!("\n=== Hypothesis H1: adjacent-query pairing, alpha=1 ===");
    for alpha_val in [1u128, 2, 3, 0] {
        let alpha = blk(alpha_val);
        let mut matches = 0;
        let mut total = 0;
        for r in 0..num_rounds.min(3) {
            let next_count = if r + 1 < num_rounds {
                opening.rounds[r + 1].opened_values.len()
            } else { break };
            for i in 0..next_count.min(10) {
                if 2 * i + 1 >= num_queries { break; }
                let p0 = opening.rounds[r].opened_values[2 * i][0];
                let p1 = opening.rounds[r].opened_values[2 * i + 1][0];
                let folded = p0 + alpha * (p0 + p1);
                let next = opening.rounds[r + 1].opened_values[i][0];
                total += 1;
                if folded == next { matches += 1; }
            }
        }
        println!("  alpha={}: {}/{} matches", alpha_val, matches, total);
    }

    // Hypothesis H2: base_opened_values fold to round 0
    println!("\n=== Hypothesis H2: base fold to round 0 ===");
    for alpha_val in [1u128, 2, 3, 0] {
        let alpha = blk(alpha_val);
        let mut matches = 0;
        let mut total = 0;
        let base = &opening.base_opened_values;
        for i in 0..base.len().min(10) {
            if 2 * i + 1 >= base.len() { break; }
            let p0 = base[2 * i][0];
            let p1 = base[2 * i + 1][0];
            let folded = p0 + alpha * (p0 + p1);
            let next = opening.rounds[0].opened_values[i][0];
            total += 1;
            if folded == next { matches += 1; }
        }
        println!("  alpha={}: {}/{} matches", alpha_val, matches, total);
    }

    // Hypothesis H3: verify sumcheck first, then try PCS-native with alpha
    println!("\n=== Sumcheck alphas (native) ===");
    let mut ch_v = make_ch();
    let nsc = proof.sumcheck.round_polys.len();
    let dsc = proof.sumcheck.round_polys[0].len();
    let (sc_alphas, _sc_final) = proof.sumcheck.verify(&mut ch_v, nsc, dsc, 0).unwrap();
    println!("  sumcheck alphas count = {}", sc_alphas.iter().count());
    println!("  sumcheck alpha[0] = {:?}", sc_alphas[0]);

    println!("\n=== T1.2b step 3 DIAGNOSTIC COMPLETE ===");
    println!("Report: see hypotheses above. Matching hypothesis = correct fold model.");
}
