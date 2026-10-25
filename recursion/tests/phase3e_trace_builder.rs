//! Phase 3E: build FriVerifierAirV2 trace from a real FRI proof.
//!
//! Path C validated (2026-10-25): `Val = Challenge = BinaryField128` is
//! accepted by Plonky3 MultiStark. So we run MultiStark directly on BF128
//! and feed it a trace derived from `sahyadri_fri_binius::FriProof`.
//!
//! Trace layout: one row per (query, round). For each query q and round r:
//!   pair0    = q.pairs[r][0]
//!   pair1    = q.pairs[r][1]
//!   alpha    = challenges[r]
//!   i_r      = q.index_0 >> (log_len_0 - rounds[r].log_len)
//!   sel      = i_r & 1
//!   is_last  = (r == num_rounds - 1)
//!   next, s  = if is_last { (final_poly[i_final], one_hot(i_final, 4)) }
//!              else        { (q.pairs[r+1][0], zeros) }
//!
//! `challenges` are re-derived from `rounds[r].root` via the same hash as
//! the FRI verifier. Both use blake3 over (seed || root || prior challenges).

use p3_binary_field::BinaryField128 as Block128;
use p3_matrix::dense::RowMajorMatrix;
use sahyadri_fri_binius::{FriParams, FriProof, FriProver};
use sahyadri_fri_binius::bytes::Block128Bytes;

use p3_recursion::frost_gkr::fri_verifier_air_v2::*;

type F = Block128;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

/// Re-derive per-round challenges exactly as the FRI verifier does.
///
/// `sahyadri-fri-binius` seeds the challenge derivation from the seed and
/// each round's commitment root. The verifier code in that crate does:
///
///   bytes = seed || root || prior_challenges
///   h = blake3(bytes); challenge = h[0..16] as Block128
///
/// We mirror that order here so the trace we build matches what the FRI
/// verifier accepts.
fn derive_challenges(proof: &FriProof, seed: &[u8]) -> Vec<F> {
    let mut challenges: Vec<F> = Vec::with_capacity(proof.rounds.len());
    for r in 0..proof.rounds.len() {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(seed);
        bytes.extend_from_slice(&proof.rounds[r].root.blk_to_le_bytes());
        for prev in &challenges {
            bytes.extend_from_slice(&prev.blk_to_le_bytes());
        }
        let h = blake3::hash(&bytes);
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&h.as_bytes()[..16]);
        challenges.push(blk(u128::from_le_bytes(arr)));
    }
    challenges
}

fn one_hot(idx: usize) -> [F; FINAL_POLY_LEN] {
    let mut s = [blk(0); FINAL_POLY_LEN];
    if idx < FINAL_POLY_LEN {
        s[idx] = blk(1);
    }
    s
}

/// Build the MultiStark trace for `FriVerifierAirV2` from a real FRI proof.
///
/// Rows are ordered query-major: q0r0, q0r1, ..., q0rR, q1r0, ...
/// Public inputs = proof.final_poly[0..4].
pub fn build_trace_from_proof(proof: &FriProof, seed: &[u8]) -> (RowMajorMatrix<F>, Vec<F>) {
    assert!(proof.final_poly.len() >= FINAL_POLY_LEN,
        "need at least {} final_poly cells", FINAL_POLY_LEN);

    let challenges = derive_challenges(proof, seed);
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
            let shift = log_len_0 - log_r;
            let i_r = q.index_0 >> shift;
            let sel_val = if (i_r & 1) == 0 { blk(0) } else { blk(1) };
            let is_last = r == num_rounds - 1;

            let (next, s) = if is_last {
                let i_final = q.index_0 >> (log_len_0 - log_final);
                (proof.final_poly[i_final], one_hot(i_final))
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

#[cfg(test)]
mod tests {
    use p3_matrix::Matrix;
    use super::*;

    fn params() -> FriParams {
        FriParams { log_inv_rate: 2, num_queries: 8, pow_bits: 0 }
    }

    fn sample_evals() -> Vec<Block128> {
        (0..32u128).map(blk).collect()
    }

    #[test]
    fn trace_shape_matches_expected() {
        let prover = FriProver::new(params());
        let seed = b"3e-trace";
        let proof = prover.prove(sample_evals(), seed).unwrap();

        let (trace, public) = build_trace_from_proof(&proof, seed);

        assert_eq!(trace.width(), WIDTH);
        assert_eq!(trace.height(), proof.queries.len() * proof.rounds.len());
        assert_eq!(public.len(), NUM_PUBLIC);

        println!("trace: {} rows x {} cols", trace.height(), trace.width());
        println!("public: {} cells", public.len());
    }

    #[test]
    fn trace_passes_constraints() {
        use p3_air::check_constraints;

        let prover = FriProver::new(params());
        let seed = b"3e-constraints";
        let proof = prover.prove(sample_evals(), seed).unwrap();
        let (trace, public) = build_trace_from_proof(&proof, seed);

        let air = FriVerifierAirV2;
        check_constraints(&air, &trace, &public);
    }

    #[test]
    fn trace_fails_if_proof_tampered() {
        use p3_air::check_constraints;

        let prover = FriProver::new(params());
        let seed = b"3e-tamper";
        let mut proof = prover.prove(sample_evals(), seed).unwrap();

        // Flip a pair value — fold constraint should catch it
        if let Some(q) = proof.queries.first_mut() {
            if let Some(pair) = q.pairs.first_mut() {
                pair[0] = blk(u128::MAX);
            }
        }

        let (trace, public) = build_trace_from_proof(&proof, seed);
        let air = FriVerifierAirV2;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &trace, &public);
        }));
        assert!(result.is_err(), "tampered FRI proof must fail constraints");
    }

    #[test]
    fn trace_fails_if_public_mismatched() {
        use p3_air::check_constraints;

        let prover = FriProver::new(params());
        let seed = b"3e-pub";
        let proof = prover.prove(sample_evals(), seed).unwrap();
        let (trace, mut public) = build_trace_from_proof(&proof, seed);

        // Tamper the public final_poly cell
        public[0] = public[0] + blk(1);

        let air = FriVerifierAirV2;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &trace, &public);
        }));
        assert!(result.is_err(), "tampered public input must fail");
    }
}
