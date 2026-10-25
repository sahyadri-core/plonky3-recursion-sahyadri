//! Phase 3E: real FRI proof → MultiStark proof. Measure time + size.
//!
//! Path C: Val = Challenge = BinaryField128.

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

/// Inline copy of build_trace_from_proof (was a test helper).
fn build_trace_from_proof(proof: &FriProof, seed: &[u8]) -> (RowMajorMatrix<F>, Vec<F>) {
    assert!(proof.final_poly.len() >= FINAL_POLY_LEN);

    // Derive per-round challenges.
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
    let n_rows = proof.queries.len() * num_rounds;
    let mut values = Vec::with_capacity(n_rows * WIDTH);

    for q in &proof.queries {
        for r in 0..num_rounds {
            let pair0 = q.pairs[r][0];
            let pair1 = q.pairs[r][1];
            let alpha = challenges[r];
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
            row[COL_PAIR0] = pair0;
            row[COL_PAIR1] = pair1;
            row[COL_ALPHA] = alpha;
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

#[test]
#[ignore]
fn prove_real_fri_proof() {
    let prover = FriProver::new(FriParams { log_inv_rate: 2, num_queries: 8, pow_bits: 0 });
    let seed = b"3e-prove";
    let evals: Vec<BinaryField128> = (0..32u128)
        .map(|n| BinaryField128::from_le_bytes(n.to_le_bytes()))
        .collect();
    let fri_proof = prover.prove(evals, seed).unwrap();

    let (trace, public) = build_trace_from_proof(&fri_proof, seed);
    println!("trace: {} x {}", trace.height(), trace.width());

    let trace_pow2 = trace.height().next_power_of_two();
    let arity = (trace_pow2 * WIDTH).next_power_of_two().trailing_zeros() as usize;

    let mut padded = trace.values;
    padded.resize(trace_pow2 * WIDTH, F::ZERO);
    let padded_trace = RowMajorMatrix::new(padded, WIDTH);

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
    let config = Cfg {
        pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap(),
    };

    let air = FriVerifierAirV2;
    let mut ch_setup = make_ch();
    let (pk, _vk) = setup(&config, &[&air], &mut ch_setup).unwrap();

    let table = Table::new(padded_trace.transpose());
    let instance = ProverInstance::new(&air, table, &pk, &public);

    let mut ch = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![instance]), 0, &mut ch).unwrap();
    let elapsed = start.elapsed();

    println!("PROOF GENERATED:");
    println!("  time  = {:?}", elapsed);
    println!("  size  = ~{} B", core::mem::size_of_val(&proof));
    println!("  arity = {}", arity);
}
