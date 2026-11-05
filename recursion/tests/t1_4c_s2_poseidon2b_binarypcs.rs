//! T1.4c Session 2: Poseidon2bMmcs integrated with BinaryPcs.
//!
//! # Goal
//! Prove+verify a small MultiStark proof with BinaryPcs using
//! Poseidon2bMmcs (instead of blake3::LevelMmcs).
//!
//! # What this validates
//! - `GroupedCodewordMmcs<Poseidon2bMmcs>` type-checks
//! - BinaryPcs commit/prove/verify works with Poseidon2b
//! - Proof size sanity: size_of_val ~832 B (struct header); serialized ~200 KB expected
//!
//! # Not in scope (Session 3)
//! - Migration of T1.2b/T1.3 tests (type swap + regression re-run)
//! - 3D2c Merkle bus wiring (Session 4)
//!
//! # Status
//! This is the FIRST real integration test. If this passes, Poseidon2b is
//! a viable Merkle backend for BinaryPcs. If it fails with type errors or
//! verification failures, we have concrete blockers to fix.

use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;

use p3_recursion::frost_gkr::sumcheck_verifier_air::{
    SumcheckVerifierAir,
    COL_H0 as SC_H0, COL_H_INF as SC_H_INF, COL_ALPHA as SC_ALPHA,
    COL_CLAIMED as SC_CLAIMED, COL_NEXT_CLAIMED as SC_NEXT,
    COL_IS_FIRST as SC_IS_FIRST, COL_IS_LAST as SC_IS_LAST,
    WIDTH as SC_WIDTH,
};

type F = BinaryField128;
type E = BinaryField128;

// === KEY CHANGE: Poseidon2bMmcs instead of blake3::LevelMmcs ===
type InnerMmcs = Poseidon2bMmcs;
type M = GroupedCodewordMmcs<InnerMmcs>;
type ME = GroupedCodewordMmcs<InnerMmcs>;

// For binary field, F == E, so M == ME
// (In general case, would need a challenge-field variant of Poseidon2bMmcs)

// Challenger still uses blake3 (PCS transcript challenge, independent of Merkle)
type Ch = p3_test_utils::binary_field_params::blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

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

fn make_ch() -> Ch {
    use p3_test_utils::binary_field_params::blake3;
    Ch::from_hasher(vec![], blake3::byte_hash())
}

fn build_config(arity: usize) -> Cfg {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    // Poseidon2bMmcs directly (no field hash / no compression wrapper needed)
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
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

#[test]
#[ignore]
fn poseidon2b_binarypcs_prove_verify() {
    use std::time::Instant;

    println!("=== Poseidon2bMmcs + BinaryPcs integration ===");

    let (trace, public) = build_sc_trace();
    let raw = trace.height() * trace.width();
    let arity = raw.next_power_of_two().trailing_zeros() as usize;
    println!("Trace: {}x{}, arity {}", trace.height(), trace.width(), arity);

    let config = build_config(arity);

    let mut ch_s = make_ch();
    let (pk, vk) = setup(&config, &[&SumcheckVerifierAir], &mut ch_s).unwrap();
    println!("Setup OK");

    let inst = ProverInstance::new(&SumcheckVerifierAir, Table::new(trace.transpose()), &pk, &public);
    let mut ch_p = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![inst]), 0, &mut ch_p).unwrap();
    let prove_time = start.elapsed();
    println!("PROVE: {:?}, ~{}B", prove_time, core::mem::size_of_val(&proof));

    let log_h = trace.height().trailing_zeros() as usize;
    let verif = VerifierInstance::new(&SumcheckVerifierAir, &vk, log_h, &public);
    let mut ch_v = make_ch();
    let start = Instant::now();
    verify(&config, VerifierInstances::new(vec![verif]), &proof, 0, &mut ch_v)
        .expect("Poseidon2b proof must verify");
    let verify_time = start.elapsed();
    println!("VERIFY: {:?}", verify_time);

    println!("\n=== Session 2 PASS: Poseidon2bMmcs integrated with BinaryPcs ===");
    println!("Prove {:?}, Verify {:?}", prove_time, verify_time);

    // Sanity: proof size should be small (832B-ish)
    let size = core::mem::size_of_val(&proof);
    assert!(size < 5000, "proof size {} larger than expected", size);
}
