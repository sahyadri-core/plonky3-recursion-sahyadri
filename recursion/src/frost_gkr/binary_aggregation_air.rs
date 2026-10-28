//! BinaryAggregationAir - Phase 3F tree recursion (scaffold).
//!
//! Verifies two binary MultiStark proofs in-circuit. Produces a new
//! MultiStarkProof asserting "both inputs valid".
//!
//! Status: SKELETON. Full constraints need:
//!   1. In-circuit verification of a binary FRI proof (fold + Merkle + bus)
//!   2. In-circuit verification of a binary MultiStark bus balance
//!   3. Public input binding (the two input proofs' commitments)
//!
//! This is the missing circuit that Plonky3 does not provide for binary
//! field. It is the only path to O(1) constant-size proof for the 4444
//! FRI verifier proofs.
//!
//! Estimated effort: 3-5 days for full implementation.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;

/// Two-input binary aggregation verifier.
///
/// One instance proves: "proof A valid AND proof B valid".
/// Tree of instances reduces N proofs to 1 root.
pub struct BinaryAggregationAir {
    /// Width of a single MultiStark verifier circuit (bytes in-circuit).
    pub inner_verifier_width: usize,
}

/// Number of public inputs: two 32-byte commitments (as 16 Block128 each).
pub const AGG_PUBLIC: usize = 32;

/// Placeholder width. Real width will be 2x inner verifier + witness columns.
pub const AGG_WIDTH: usize = 4096;

impl<F> BaseAir<F> for BinaryAggregationAir {
    fn width(&self) -> usize { AGG_WIDTH }
    fn num_public_values(&self) -> usize { AGG_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for BinaryAggregationAir {
    fn eval(&self, b: &mut AB) {
        let _ = b; // placeholder — Path B parked, constraints in future session
        // Phase 3F-1 (skeleton): no constraints yet.
        //
        // Phase 3F-2 (next):
        //   - Bind witness[0..inner_verifier_width] to proof A's trace
        //   - Assert all of proof A's FRI constraints
        //   - Bind witness[inner_verifier_width..2*inner_verifier_width] to proof B
        //   - Assert all of proof B's FRI constraints
        //   - Bind public[0..16] to commitment(A), public[16..32] to commitment(B)
        //
        // Phase 3F-3:
        //   - Output: new commitment = hash(A_commit, B_commit)
        //   - Tree: log2(4444) = 12 levels, each level halves proofs
        //
        // The circuit needs the binary FRI verifier (FriVerifierAirV2's
        // constraints) instantiated twice, one per input proof. This is
        // the recursive composition that Plonky3's `build_and_prove_aggregation_layer`
        // does for prime fields but not for binary.
    }
}
