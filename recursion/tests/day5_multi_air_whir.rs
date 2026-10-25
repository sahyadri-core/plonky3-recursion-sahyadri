//! Day 5a: prove all 3 verifier AIRs in a single multi-AIR WHIR proof.
//!
//! BinaryNativeWhirAuthority::setup takes a homogeneous Vec<A>, so we
//! wrap the 3 AIR types in one enum that dispatches eval().
//!
//! All AIRs share width = 512. Public counts: Extraction=17, PcsOpen=17,
//! Sumcheck=16. Enum reports 17 for all; Sumcheck ignores slot 16.
//!
//! Arity for 3 AIRs of shape 512x512 each:
//!   total cells = 3 * 262144 = 786432
//!   log2_ceil(786432) = 20

#![cfg(feature = "frost-gkr")]

use p3_air::{Air, AirBuilder, BaseAir};
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
    l.max_log_domain_or_degree = 22;
    l
}

fn trace(width: usize, height: usize) -> RowMajorMatrix<F> {
    let row = vec![fe(0); width];
    let values: Vec<F> = (0..height).flat_map(|_| row.iter().copied()).collect();
    RowMajorMatrix::new(values, width)
}

#[derive(Clone, Copy)]
enum VerifierAir {
    Extraction,
    PcsOpen,
    Sumcheck,
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

#[test]
fn prove_three_airs_together() {
    let width = 512;
    let height = 512;
    let log_trace_height = 9;
    let arity = 20;

    let spec = BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(
            arity, protocol(), ByteHash::Keccak256, 0,
        ).expect("pcs parameters"),
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"day5-multi-air".to_vec(),
        sumcheck_pow_bits: 0,
        max_tau_draws: 128,
        security_bits: 8,
    };

    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![
            VerifierAir::Extraction,
            VerifierAir::PcsOpen,
            VerifierAir::Sumcheck,
        ],
        vec![log_trace_height, log_trace_height, log_trace_height],
        spec,
        &limits(),
    ).expect("multi-air setup");

    // All three instances have 17 public values (Sumcheck's 17th is padding).
    let expected: Vec<Vec<F>> = vec![
        vec![fe(0); 17],
        vec![fe(0); 17],
        vec![fe(0); 17],
    ];

    let traces = vec![trace(width, height), trace(width, height), trace(width, height)];

    let proof = prover.prove(&expected, traces).expect("multi-air prove");
    let _checked = authority.verify_native(&proof, &expected).expect("multi-air verify");

    println!("SUCCESS: 3-AIR WHIR proof round-tripped (arity=20)");
}
