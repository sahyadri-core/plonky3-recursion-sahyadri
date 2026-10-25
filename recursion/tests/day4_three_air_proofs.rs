//! Day 4b: prove all three verifier AIRs independently via WHIR.
//! Each proof round-trips. Composition into one aggregate proof is Day 5.

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
use p3_recursion::frost_gkr::pcs_open_air::PcsOpenAir;
use p3_recursion::frost_gkr::verifier_air::FrostGkrVerifierAir;

type F = BinaryField128;

fn fe(v: u128) -> F { F::from_le_bytes(v.to_le_bytes()) }

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

fn limits() -> VerifierLimits {
    let mut l = VerifierLimits::default();
    l.max_metadata_entries = 1 << 22;
    l
}


#[test]
fn prove_extraction_air() {
    let width = 512; let height = 512; let log_trace_height = 9; let arity = 18;
    let mut row = vec![fe(0); width];
    let values: Vec<F> = (0..height).flat_map(|_| row.iter().copied()).collect();
    let trace = RowMajorMatrix::new(values, width);
    // Public inputs for ExtractionAir: digest(2) + rho(15) = 17
    let public = vec![fe(0); 17];
    let _ = &mut row; // silence
    let spec = BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(arity, protocol(), ByteHash::Keccak256, 0).unwrap(),
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"day4b-extraction".to_vec(),
        sumcheck_pow_bits: 0, max_tau_draws: 128, security_bits: 8,
    };
    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![ExtractionAir], vec![log_trace_height], spec, &limits(),
    ).expect("setup");
    let expected = vec![public];
    let proof = prover.prove(&expected, vec![trace]).expect("prove");
    authority.verify_native(&proof, &expected).expect("verify");
    println!("ExtractionAir: SUCCESS");
}

#[test]
fn prove_pcs_open_air() {
    // Same shape, different AIR and public count.
    // PcsOpenAir: 1 commitment + 15 eval_point + 1 claim = 17
    let width = 512; let height = 512; let log_trace_height = 9; let arity = 18;
    let row = vec![fe(0); width];
    let values: Vec<F> = (0..height).flat_map(|_| row.iter().copied()).collect();
    let trace = RowMajorMatrix::new(values, width);
    let public = vec![fe(0); 17];
    let spec = BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(arity, protocol(), ByteHash::Keccak256, 0).unwrap(),
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"day4b-pcs-open".to_vec(),
        sumcheck_pow_bits: 0, max_tau_draws: 128, security_bits: 8,
    };
    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![PcsOpenAir], vec![log_trace_height], spec, &limits(),
    ).expect("setup");
    let expected = vec![public];
    let proof = prover.prove(&expected, vec![trace]).expect("prove");
    authority.verify_native(&proof, &expected).expect("verify");
    println!("PcsOpenAir: SUCCESS");
}

#[test]
fn prove_frost_gkr_verifier_air() {
    // FrostGkrVerifierAir: 16 public values (rho[0..15] + claim)
    let width = 512; let height = 512; let log_trace_height = 9; let arity = 18;
    let row = vec![fe(0); width];
    let values: Vec<F> = (0..height).flat_map(|_| row.iter().copied()).collect();
    let trace = RowMajorMatrix::new(values, width);
    let public = vec![fe(0); 16];
    let spec = BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(arity, protocol(), ByteHash::Keccak256, 0).unwrap(),
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"day4b-verifier".to_vec(),
        sumcheck_pow_bits: 0, max_tau_draws: 128, security_bits: 8,
    };
    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![FrostGkrVerifierAir], vec![log_trace_height], spec, &limits(),
    ).expect("setup");
    let expected = vec![public];
    let proof = prover.prove(&expected, vec![trace]).expect("prove");
    authority.verify_native(&proof, &expected).expect("verify");
    println!("FrostGkrVerifierAir: SUCCESS");
}
