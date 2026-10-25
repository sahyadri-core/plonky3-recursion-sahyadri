//! Day 4a: prove one verifier AIR end-to-end via WHIR.
//!
//! Design notes:
//! - ExtractionAir has width 512, single-row semantics (no cross-row constraints).
//! - We pad to a 512 x 512 square trace so Table/WHIR accept it.
//! - log_height = 9 (2^9 = 512 rows).
//! - If arity mismatch occurs, try log_height + log_width = 18 next.

#![cfg(feature = "frost-gkr")]

use p3_binary_field::BinaryField128;
use p3_circuit::ops::ByteHash;
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::artifact::{
    BinaryNativeVerifierSpec, BinaryNativeWhirAuthority, BinaryNativeWhirPcsParameters,
};
use p3_recursion::verifier::VerifierLimits;
use p3_whir::{FoldingFactor, ProtocolParameters, SecurityAssumption};

use p3_recursion::frost_gkr::extraction_air::ExtractionAir;

type F = BinaryField128;

fn fe(v: u128) -> F {
    F::from_le_bytes(v.to_le_bytes())
}

fn protocol() -> ProtocolParameters {
    ProtocolParameters {
        security_level: 16,
        pow_bits: 0,
        round_log_inv_rates: vec![],
        folding_factor: FoldingFactor::Constant(1),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 2,
    }
}

#[test]
fn prove_extraction_air_whir() {
    let width = 512;
    let height = 512;

    // Build one valid ExtractionAir row.
    let mut valid_row = vec![fe(0); width];
    valid_row[0] = fe(0xDEAD);
    valid_row[1] = fe(0xBEEF);
    for sqz in 0..8 {
        for lane in 0..4 {
            valid_row[2 + sqz * 4 + lane] = fe((sqz as u128 + 1) * 100 + (lane as u128 + 1));
        }
    }
    for i in 0..7 {
        valid_row[34 + 2 * i] = valid_row[2 + i * 4];
        valid_row[34 + 2 * i + 1] = valid_row[2 + i * 4 + 1];
    }
    valid_row[34 + 14] = valid_row[2 + 7 * 4];

    // Public values: digest(2) + rho(15) = 17 elements.
    let mut public: Vec<F> = Vec::with_capacity(17);
    public.push(valid_row[0]);
    public.push(valid_row[1]);
    public.extend_from_slice(&valid_row[34..34 + 15]);

    // Duplicate row to fill 512 x 512.
    let values: Vec<F> = (0..height).flat_map(|_| valid_row.iter().copied()).collect();
    let trace = RowMajorMatrix::new(values, width);

    let log_trace_height = 9usize; // 2^9 = 512 rows
    let arity = 18usize; // log2(512 * 512) // 2^9 = 512 rows

    let spec = BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(
            arity,
            protocol(),
            ByteHash::Keccak256,
            0,
        )
        .expect("pcs parameters"),
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"day4-extraction-v1".to_vec(),
        sumcheck_pow_bits: 0,
        max_tau_draws: 64,
        security_bits: 4,
    };

    let mut limits = VerifierLimits::default();
    limits.max_metadata_entries = 1 << 20;

    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![ExtractionAir],
        vec![log_trace_height],
        spec,
        &limits,
    )
    .expect("whir setup");

    let expected: Vec<Vec<F>> = vec![public];
    let proof = prover.prove(&expected, vec![trace]).expect("prove");
    let _checked = authority
        .verify_native(&proof, &expected)
        .expect("verify");

    println!("SUCCESS: single ExtractionAir WHIR proof round-tripped");
}
