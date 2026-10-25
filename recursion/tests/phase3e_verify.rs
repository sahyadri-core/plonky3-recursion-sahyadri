//! Phase 3E verify: prove + verify with retained VK, plus tamper end-to-end.

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
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::bytes::Block128Bytes;
use sahyadri_fri_binius::{FriParams, FriProver};
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

fn build_trace_from_proof(
    proof: &sahyadri_fri_binius::FriProof,
    seed: &[u8],
) -> (RowMajorMatrix<F>, Vec<F>) {
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

#[test]
#[ignore]
fn full_pipeline_prove_and_verify() {
    // 1. Generate FRI proof
    let prover = FriProver::new(FriParams { log_inv_rate: 2, num_queries: 8, pow_bits: 0 });
    let seed = b"3e-verify";
    let evals: Vec<BinaryField128> = (0..32u128)
        .map(|n| BinaryField128::from_le_bytes(n.to_le_bytes()))
        .collect();
    let fri_proof = prover.prove(evals, seed).unwrap();

    // 2. Build trace + public
    let (trace, public) = build_trace_from_proof(&fri_proof, seed);
    let trace_pow2 = trace.height().next_power_of_two();
    let mut padded = trace.values;
    padded.resize(trace_pow2 * WIDTH, F::ZERO);
    let padded_trace = RowMajorMatrix::new(padded, WIDTH);

    let arity = (trace_pow2 * WIDTH).next_power_of_two().trailing_zeros() as usize;
    let log_height = trace_pow2.trailing_zeros() as usize;
    println!("trace {}x{}, arity {}, log_height {}",
        padded_trace.height(), padded_trace.width(), arity, log_height);

    // 3. Setup — retain both pk AND vk
    let config = build_config(arity);
    let air = FriVerifierAirV2;
    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&air], &mut ch_setup).unwrap();

    // 4. Prove
    let table = Table::new(padded_trace.transpose());
    let instance = ProverInstance::new(&air, table, &pk, &public);
    let mut ch_prove = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![instance]), 0, &mut ch_prove).unwrap();
    let prove_time = start.elapsed();
    println!("PROVE: {:?}, ~{} B", prove_time, core::mem::size_of_val(&proof));

    // 5. Verify with a fresh challenger
    let mut ch_verify = make_ch();
    let instances = VerifierInstances::new(vec![
        VerifierInstance::new(&air, &vk, log_height, &public)
    ]);
    let start = Instant::now();
    verify(&config, instances, &proof, 0, &mut ch_verify)
        .expect("honest proof must verify");
    let verify_time = start.elapsed();
    println!("VERIFY: {:?}", verify_time);

    println!("\n=== 3E END-TO-END PASS ===");
    println!("prove  {:?}", prove_time);
    println!("verify {:?}", verify_time);
    println!("size   ~{} B", core::mem::size_of_val(&proof));
}

#[test]
#[ignore]
fn tampered_fri_proof_fails_verify() {
    let prover = FriProver::new(FriParams { log_inv_rate: 2, num_queries: 8, pow_bits: 0 });
    let seed = b"3e-verify-tamper";
    let evals: Vec<BinaryField128> = (0..32u128)
        .map(|n| BinaryField128::from_le_bytes(n.to_le_bytes()))
        .collect();
    let mut fri_proof = prover.prove(evals, seed).unwrap();

    // Tamper a pair value
    if let Some(q) = fri_proof.queries.first_mut() {
        if let Some(pair) = q.pairs.first_mut() {
            pair[0] = blk(u128::MAX);
        }
    }

    // Build trace from tampered proof
    let (trace, public) = build_trace_from_proof(&fri_proof, seed);
    let trace_pow2 = trace.height().next_power_of_two();
    let mut padded = trace.values;
    padded.resize(trace_pow2 * WIDTH, F::ZERO);
    let padded_trace = RowMajorMatrix::new(padded, WIDTH);

    let arity = (trace_pow2 * WIDTH).next_power_of_two().trailing_zeros() as usize;
    let log_height = trace_pow2.trailing_zeros() as usize;

    let config = build_config(arity);
    let air = FriVerifierAirV2;
    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&air], &mut ch_setup).unwrap();

    let table = Table::new(padded_trace.transpose());
    let instance = ProverInstance::new(&air, table, &pk, &public);
    let mut ch_prove = make_ch();
    let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(&config, ProverInstances::new(vec![instance]), 0, &mut ch_prove)
    }));

    match prove_result {
        Ok(Ok(proof)) => {
            // Prover emitted a proof; verifier must reject
            let mut ch_verify = make_ch();
            let instances = VerifierInstances::new(vec![
                VerifierInstance::new(&air, &vk, log_height, &public)
            ]);
            let verify_result = verify(&config, instances, &proof, 0, &mut ch_verify);
            assert!(verify_result.is_err(),
                "tampered FRI proof must fail verify (prover emitted proof)");
            println!("PASS: prover emitted, verifier rejected");
        }
        Ok(Err(_)) | Err(_) => {
            println!("PASS: prover rejected tampered trace");
        }
    }
}
