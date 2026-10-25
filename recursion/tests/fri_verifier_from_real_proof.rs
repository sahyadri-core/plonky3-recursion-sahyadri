//! Phase 3E: build FriVerifierAirV2 trace from a real FRI proof.
//!
//! STATUS: skeleton with documented field blocker.
//!
//! The FriVerifierAirV2 in `p3-recursion` uses a generic `AB::F` — it works
//! over any field the multi-stark config accepts. The FRI proof produced by
//! `sahyadri-fri-binius` is over `BinaryField128`. Plonky3's `MultiStarkConfig`
//! requires `Challenge: ExtensionField<Val>`. For binary fields:
//!
//!   (Val, Challenge) pairs that Plonky3 supports natively:
//!     (BF8, BF64), (BF16, BF128), (BF32, BF128), (BF64, BF128)
//!
//! BinaryField128 has no extension field in Plonky3's tower — the next level
//! is GF(2^256), which Plonky3 does not ship. Two workarounds:
//!
//!   Path A: build FRI over BF64 (crate-level change, 1-2 days)
//!   Path B: add GF(2^256) extension via hekate-math (2-3 days)
//!
//! Until then, this file's test extracts the *shape* of a real FRI proof
//! and prints what the trace would look like — so the trace builder and the
//! memory/time measurements in 3F can be validated against real data
//! dimensions.
//!
//! Once Path A or B lands, the `build_trace_from_proof` function swaps from
//! the synthetic `build_trace` in `fri_verifier_v2_scale.rs` to this one.

use p3_recursion::frost_gkr::blake3_bridge::RAW_WIDTH;
use sahyadri_fri_binius::{
    FriParams, FriProver, FriProof,
};

// Local F = BF128 since that matches the FRI proof field.
type B = p3_binary_field::BinaryField128;

fn block(n: u128) -> B {
    B::from_le_bytes(n.to_le_bytes())
}

/// Sample FRI params small enough to fit in a unit test but representative
/// of shape (4 rounds, 8 queries, no grinding).
fn params() -> FriParams {
    FriParams { log_inv_rate: 2, num_queries: 8, pow_bits: 0 }
}

fn sample_evals() -> Vec<B> {
    (0..32u128).map(block).collect()
}

#[test]
fn real_fri_proof_shape() {
    let prover = FriProver::new(params());
    let seed = b"3e-shape";
    let proof: FriProof = prover.prove(sample_evals(), seed).unwrap();

    // Print the shape a real trace builder would consume.
    let log_len_0 = proof.rounds[0].log_len;
    let num_rounds = proof.rounds.len();
    let num_queries = proof.queries.len();
    let rows = num_queries * num_rounds;

    println!("real FRI proof shape:");
    println!("  rounds       = {}", num_rounds);
    println!("  queries      = {}", num_queries);
    println!("  log_len_0    = {}", log_len_0);
    println!("  final_poly   = {}", proof.final_poly.len());
    println!("  trace rows   = queries * rounds = {}", rows);
    println!("  trace width  = 10 (FriVerifierAirV2)");
    println!("  total cells  = {}", rows * 10);
    println!("  arity        = {}", (rows * 10).next_power_of_two().trailing_zeros());

    // Sanity: shape must match what build_trace_from_proof would iterate.
    assert!(num_rounds >= 2);
    assert!(!proof.queries.is_empty());
    assert!(proof.final_poly.len().is_power_of_two());

    // Reference: FW's RAW_WIDTH exports (unrelated to FRI, but confirms
    // the crate imports resolve).
    println!("  (blake3 raw width for reference: {})", RAW_WIDTH);
}

#[test]
#[ignore]
fn trace_builder_pending_field_alignment() {
    // Full `build_trace_from_proof` implementation lands after Path A or B.
    // The trace row layout is:
    //
    //   for each query q:
    //     for each round r:
    //       pair0 = q.pairs[r][0]
    //       pair1 = q.pairs[r][1]
    //       alpha = challenges[r]    (derived from rounds commitment chain)
    //       i_r   = q.index_0 >> (log_len_0 - rounds[r].log_len)
    //       sel   = (i_r & 1) as u64
    //       is_last = (r == num_rounds - 1) as u64
    //       next, s[0..4] = if is_last {
    //           i_final = q.index_0 >> (log_len_0 - log2(final_poly.len()))
    //           (final_poly[i_final], one_hot(i_final, 4))
    //       } else {
    //           (q.pairs[r+1][0], zeros)
    //       }
    //
    // Public inputs = final_poly[0..4].
    todo!("Blocked on field alignment (Path A or Path B)");
}
