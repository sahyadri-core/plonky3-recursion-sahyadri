//! Day 6: chain batch proofs via PreparedNativeBinaryWhirLayer.
//!
//! IMPORTANT: prove_verified() re-proves ONE proof recursively.
//! It does NOT aggregate N independent proofs into one.
//! This test confirms the API mechanics work; N-batch aggregation needs
//! a 2-input layer that does not exist yet in the fork.

#![cfg(feature = "frost-gkr")]

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_circuit::ops::ByteHash;
use p3_circuit::{CircuitConstructionLimits};
use p3_circuit_prover::direct::DirectCircuitLimits;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::MultiStarkProof;
use p3_recursion::artifact::{
    ArtifactLimits, BinaryNativeVerifierSpec, BinaryNativeWhirAuthority,
    BinaryNativeWhirConfig, BinaryNativeWhirPcsParameters,
};
use p3_recursion::prepared::{
    NativeBinaryRecursionOptions, PreparedNativeBinaryWhirLayer,
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
        security_level: 12,
        pow_bits: 0,
        round_log_inv_rates: vec![],
        folding_factor: FoldingFactor::Constant(4),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 2,
    }
}

fn limits() -> VerifierLimits {
    let mut l = VerifierLimits::default();
    l.max_metadata_entries = 1 << 24;
    l.max_log_domain_or_degree = 31;
    l.max_rounds = 256;
    l
}

fn options(depth: usize) -> NativeBinaryRecursionOptions {
    NativeBinaryRecursionOptions {
        main: protocol(),
        preprocessed: protocol(),
        cap_height: 4,
        initial_bytes: format!("sahyadri-day6-layer-{depth}").into_bytes(),
        sumcheck_pow_bits: 0,
        max_tau_draws: 128,
        security_bits: 8,
        max_pcs_codeword_cells: 1 << 31,
        artifact_limits: ArtifactLimits {
            verifier: limits(),
            ..ArtifactLimits::default()
        },
    }
}

#[derive(Clone, Copy)]
enum VerifierAir {
    Extraction, PcsOpen, Sumcheck,
}
impl<F2> BaseAir<F2> for VerifierAir {
    fn width(&self) -> usize { 512 }
    fn num_public_values(&self) -> usize { 17 }
}
impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for VerifierAir {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::Extraction => ExtractionAir.eval(b),
            Self::PcsOpen => PcsOpenAir.eval(b),
            Self::Sumcheck => FrostGkrVerifierAir.eval(b),
        }
    }
}

fn trace(width: usize, height: usize) -> RowMajorMatrix<F> {
    let row = vec![fe(0); width];
    let values: Vec<F> = (0..height).flat_map(|_| row.iter().copied()).collect();
    RowMajorMatrix::new(values, width)
}

fn batch_spec() -> BinaryNativeVerifierSpec<BinaryNativeWhirPcsParameters<F>> {
    BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(20, protocol(), ByteHash::Keccak256, 0)
            .expect("pcs"),
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"sahyadri-batch".to_vec(),
        sumcheck_pow_bits: 0,
        max_tau_draws: 128,
        security_bits: 8,
    }
}

fn prove_batch(_seed: u128) -> (MultiStarkProof<BinaryNativeWhirConfig<F>>, Vec<Vec<F>>) {
    let spec = batch_spec();
    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![VerifierAir::Extraction, VerifierAir::PcsOpen, VerifierAir::Sumcheck],
        vec![9, 9, 9], spec, &limits(),
    ).expect("batch setup");

    // Public inputs must match the zero trace (same pattern as Day 5a).
    let expected: Vec<Vec<F>> = vec![
        vec![fe(0); 17],
        vec![fe(0); 17],
        vec![fe(0); 17],
    ];
    let traces = vec![trace(512, 512), trace(512, 512), trace(512, 512)];
    let proof = prover.prove(&expected, traces).expect("batch prove");
    let _ = authority.verify_native(&proof, &expected).expect("batch verify");
    (proof, expected)
}

#[test]
fn smoke_chain_one_layer() {
    // 1. Prove 3 batch proofs
    let (proof0, public0) = prove_batch(1000);
    println!("batch 0 proved");

    // 2. Verify proof0 -> checked token
    let spec = batch_spec();
    let (_, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![VerifierAir::Extraction, VerifierAir::PcsOpen, VerifierAir::Sumcheck],
        vec![9, 9, 9], spec, &limits(),
    ).expect("authority setup");
    let checked = authority.verify_native(&proof0, &public0).expect("verify batch0");

    // 3. Prepare layer, prove one recursion step
    let circuit_limits = DirectCircuitLimits {
        max_witnesses: 1 << 24,     // 16M (layer 1 needs ~2.5M)
        max_operations: 1 << 24,
        max_trace_cells: 1 << 29,   // 512M
    };
    let construction_limits = CircuitConstructionLimits {
        max_expression_nodes: 1 << 24,
        max_pending_connects: 1 << 24,
        max_non_primitive_calls: 1 << 20,
        max_non_primitive_slots: 1 << 27,
    };
    let layer = PreparedNativeBinaryWhirLayer::from_native_authority_with_construction_limits(
        &authority, options(1), &circuit_limits, &construction_limits,
    ).expect("layer setup");

    let recursive = layer.prove_verified(&checked).expect("prove layer");
    let _ = layer.verify(&recursive, &public0).expect("verify layer");

    println!("SUCCESS: one recursion layer over batch 0");
}
