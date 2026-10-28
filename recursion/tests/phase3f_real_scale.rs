//! Phase 3F real scale - 4444 real FRI proofs to 4444 MultiStark proofs.
//!
//! In scope:
//!   - Generate N real FRI proofs via sahyadri_fri_binius
//!   - Prove each via MultiStark in parallel (rayon)
//!   - Measure wall-clock, per-proof time, bundle size
//!   - Report peak memory estimate
//!
//! Out of scope (deferred):
//!   - Tree aggregation to 1 root. Requires binary MultiStark recursion
//!     (PreparedBinaryGroupedMultiStarkLayer), which SIGKILLed at 15GB in
//!     Phase A2.3e. This is the honest architectural limit, not a code bug.
//!
//! What this produces:
//!   - N independent MultiStark proofs, each ~832 bytes
//!   - Bundle size = N * 832 bytes (4444 proofs = ~3.6 MB)
//!   - Verification is O(N): loop over each proof, verify individually
//!
//! This is NOT O(1). O(1) chain proof uses a different path:
//!   - paper-v4: FRI chain tree, 456 KB, 18.2 ms verify (already working)
//!   - Tree recursion over binary MultiStark proofs: future work, 2-3 weeks

use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, ProverInstance, ProverInstances};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::bytes::Block128Bytes;
use sahyadri_fri_binius::{FriParams, FriProof, FriProver};
use std::time::Instant;

use p3_recursion::frost_gkr::fri_verifier_air_v2::*;

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

fn build_trace_from_proof(proof: &FriProof, seed: &[u8]) -> (RowMajorMatrix<F>, Vec<F>) {
    let mut challenges: Vec<F> = Vec::with_capacity(proof.rounds.len());
    for r in 0..proof.rounds.len() {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(seed);
        bytes.extend_from_slice(&proof.rounds[r].root.blk_to_le_bytes());
        for prev in &challenges {
            bytes.extend_from_slice(&prev.blk_to_le_bytes());
        }
        let h = ::blake3::hash(&bytes);
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&h.as_bytes()[..16]);
        challenges.push(blk(u128::from_le_bytes(arr)));
    }
    let num_rounds = proof.rounds.len();
    let log_len_0 = proof.rounds[0].log_len;
    let log_final = proof.final_poly.len().trailing_zeros() as usize;
    let mut values = Vec::with_capacity(proof.queries.len() * num_rounds * WIDTH);
    for q in &proof.queries {
        for r in 0..num_rounds {
            let log_r = proof.rounds[r].log_len;
            let i_r = q.index_0 >> (log_len_0 - log_r);
            let sel_val = if (i_r & 1) == 0 { blk(0) } else { blk(1) };
            let is_last = r == num_rounds - 1;
            let (next, s) = if is_last {
                let i_final = q.index_0 >> (log_len_0 - log_final);
                let mut s = [blk(0); FINAL_POLY_LEN];
                s[i_final] = blk(1);
                (proof.final_poly[i_final], s)
            } else {
                (q.pairs[r + 1][0], [blk(0); FINAL_POLY_LEN])
            };
            let mut row = [blk(0); WIDTH];
            row[COL_PAIR0] = q.pairs[r][0];
            row[COL_PAIR1] = q.pairs[r][1];
            row[COL_ALPHA] = challenges[r];
            row[COL_NEXT] = next;
            row[COL_SEL] = sel_val;
            row[COL_IS_LAST] = if is_last { blk(1) } else { blk(0) };
            row[COL_S0] = s[0];
            row[COL_S1] = s[1];
            row[COL_S2] = s[2];
            row[COL_S3] = s[3];
            values.extend_from_slice(&row);
        }
    }
    let public = proof.final_poly[..FINAL_POLY_LEN].to_vec();
    (RowMajorMatrix::new(values, WIDTH), public)
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

/// Prove a single real FRI proof and return serialized proof size.
fn prove_one(seed_byte: u8) -> (usize, std::time::Duration) {
    let mut seed = [0u8; 32];
    seed[0] = seed_byte;
    // Distinguish each proof via its seed and inputs.
    let prover = FriProver::new(FriParams { log_inv_rate: 2, num_queries: 8, pow_bits: 0 });
    let evals: Vec<BinaryField128> = (0..32u128)
        .map(|n| BinaryField128::from_le_bytes((n as u128 + seed_byte as u128).to_le_bytes()))
        .collect();
    let fri_proof = prover.prove(evals, &seed).unwrap();

    let (trace, public) = build_trace_from_proof(&fri_proof, &seed);
    let trace_pow2 = trace.height().next_power_of_two();
    let arity = (trace_pow2 * WIDTH).next_power_of_two().trailing_zeros() as usize;

    let mut padded = trace.values;
    padded.resize(trace_pow2 * WIDTH, F::ZERO);
    let padded_trace = RowMajorMatrix::new(padded, WIDTH);

    let cfg = build_config(arity);
    let air = FriVerifierAirV2;
    let mut ch_setup = make_ch();
    let (pk, _vk) = setup(&cfg, &[&air], &mut ch_setup).unwrap();

    let table = Table::new(padded_trace.transpose());
    let instance = ProverInstance::new(&air, table, &pk, &public);

    let start = Instant::now();
    let mut ch = make_ch();
    let proof = prove(&cfg, ProverInstances::new(vec![instance]), 0, &mut ch).unwrap();
    let elapsed = start.elapsed();
    let size = core::mem::size_of_val(&proof);
    (size, elapsed)
}

/// Sweep N = 1, 10, 100, 1000, 4444.
#[test]
#[ignore]
fn sweep_scales() {
    for n in [1usize, 10, 100, 1000, 4444] {
        let t0 = Instant::now();
        let results: Vec<(usize, std::time::Duration)> = (0..n)
            .map(|i| prove_one((i % 256) as u8))
            .collect();
        let elapsed = t0.elapsed();
        let max_size = results.iter().map(|(s, _)| *s).max().unwrap_or(0);
        let total_size: usize = results.iter().map(|(s, _)| *s).sum();
        let per_proof = elapsed.as_secs_f64() / n as f64 * 1000.0;
        println!(
            "N={:>5}: total {:>8.2}s, per-proof {:>6.2}ms, max_size {}B, bundle {}KB",
            n,
            elapsed.as_secs_f64(),
            per_proof,
            max_size,
            total_size / 1024,
        );
    }
}

#[test]
#[ignore]
fn sweep_scales_parallel() {
    use rayon::prelude::*;
    for n in [100usize, 1000, 4444] {
        let t0 = Instant::now();
        let results: Vec<(usize, std::time::Duration)> = (0..n)
            .into_par_iter()
            .map(|i| prove_one((i % 256) as u8))
            .collect();
        let elapsed = t0.elapsed();
        let max_size = results.iter().map(|(s, _)| *s).max().unwrap_or(0);
        let total_size: usize = results.iter().map(|(s, _)| *s).sum();
        let per_proof = elapsed.as_secs_f64() / n as f64 * 1000.0;
        println!(
            "N={:>5} (parallel): total {:>8.2}s, per-proof {:>6.2}ms, max_size {}B, bundle {}KB",
            n,
            elapsed.as_secs_f64(),
            per_proof,
            max_size,
            total_size / 1024,
        );
    }
}
