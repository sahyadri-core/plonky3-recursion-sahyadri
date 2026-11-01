//! RecursiveVerifierAir — T1.4c real O(1) foundation.
//!
//! Verifies a MultiStark proof IN-CIRCUIT, producing a new proof that
//! attests to the previous one's validity. Enables O(1) tree aggregation.
//!
//! # Architecture (see RECURSIVE_VERIFIER_DESIGN.md)
//! This AIR is a SCAFFOLD that will grow to combine:
//! - Sub-1: BinaryVerifierAirV2 constraints (FRI fold)
//! - Sub-2: CompressedSumcheckAir constraints (sumcheck)
//! - Sub-3: Merkle path verification (Poseidon2b bus)
//! - Sub-4: Public input binding
//! - Sub-5: Transcript replay (Blake3 — hardest, deferred)
//!
//! # Current state (Milestone A)
//! - Layout with clear column ranges for each sub-component
//! - Placeholder for the combination
//! - Tests for the foundation
//!
//! # Honest
//! This is a FOUNDATION scaffold. Full recursive verification is 6-9
//! sessions of research-grade work (Steps B-F in design doc). Today's
//! deliverable is a clean architectural foundation — no fake "O(1) done".

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

// ============================================================================
// Column layout — reserved ranges for each sub-component
// ============================================================================

/// Sub-1: FRI fold chain (BinaryVerifierAirV2 cols: lo, hi, beta, x, next, is_last)
pub const SUB1_START: usize = 0;
pub const SUB1_WIDTH: usize = 6;
pub const SUB1_END: usize = SUB1_START + SUB1_WIDTH;

/// Sub-2: Sumcheck (CompressedSumcheckAir cols: evals[0..4], running_in,
/// running_out, challenge, is_first, is_last)
pub const SUB2_START: usize = SUB1_END;
pub const SUB2_WIDTH: usize = 9;
pub const SUB2_END: usize = SUB2_START + SUB2_WIDTH;

/// Sub-3: Merkle path (reserved for Poseidon2b bus integration)
/// Placeholder — actual columns filled in Step B.
pub const SUB3_START: usize = SUB2_END;
pub const SUB3_WIDTH: usize = 0;  // to be expanded
pub const SUB3_END: usize = SUB3_START + SUB3_WIDTH;

/// Sub-4: Public binding (SC's 2 public values + FRI's 4 final_poly = 6)
pub const SUB4_START: usize = SUB3_END;
pub const SUB4_WIDTH: usize = 6;
pub const SUB4_END: usize = SUB4_START + SUB4_WIDTH;

/// Sub-5: Transcript replay — Blake3 absorb chain (scaffold, 3 compressions
/// per challenge derivation: commitment absorb, poly absorb, sample).
pub const SUB5_START: usize = SUB4_END;
pub const SUB5_PER_ROUND: usize = 24;  // 3 Blake3 compressions × 8 state words
pub const SUB5_MAX_ROUNDS: usize = 16;  // up to 16 fold rounds
pub const SUB5_WIDTH: usize = SUB5_PER_ROUND * SUB5_MAX_ROUNDS;
pub const SUB5_END: usize = SUB5_START + SUB5_WIDTH;

/// Control columns
pub const COL_IS_FIRST: usize = SUB5_END;
pub const COL_IS_LAST: usize = SUB5_END + 1;
pub const COL_STAGE: usize = SUB5_END + 2;  // 0=fold, 1=sumcheck, 2=bind
pub const WIDTH: usize = SUB5_END + 3;
pub const NUM_PUBLIC: usize = 0;

// ============================================================================
// Stage markers
// ============================================================================

/// Stage 0: fold verification rows
pub const STAGE_FOLD: u128 = 0;
/// Stage 1: sumcheck verification rows
pub const STAGE_SUMCHECK: u128 = 1;
/// Stage 2: public binding row
pub const STAGE_BIND: u128 = 2;

// ============================================================================
// AIR
// ============================================================================

pub struct RecursiveVerifierAir;

impl<F> BaseAir<F> for RecursiveVerifierAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for RecursiveVerifierAir {
    fn eval(&self, b: &mut AB) {
        let zero = AB::F::ZERO;

        let main = b.main();
        let cur = main.current_slice();

        let is_first: AB::Expr = cur[COL_IS_FIRST].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();

        // C0: booleanity of control flags
        b.assert_eq(is_first.clone() * is_first.clone() + is_first.clone(), zero);
        b.assert_eq(is_last.clone() * is_last.clone() + is_last.clone(), zero);

        // ===== Sub-1: FRI fold constraints (ACTIVE) =====
        // Rows with stage = STAGE_FOLD have the real fold relation.
        let stage: AB::Expr = cur[COL_STAGE].into();
        let fold_stage_const = AB::F::from_le_bytes(STAGE_FOLD.to_le_bytes());

        // Convert stage to boolean "is_fold_stage"
        // In char-2: comparing stage != 0 can be done via (stage == 0) = stage + 1
        // We want: is_fold_stage * (fold_relation) = 0
        // Since stage ∈ {0,1,2}, is_fold_stage = (stage == 0) = 1 + stage[0] + ... (doesn't work for >1)
        // Simple approach: constrain stage ∈ {0,1,2} then gate on stage==0.

        // Enforce stage ∈ {0,1,2} via: stage * (stage+1) * (stage+2) = 0  (degree 3)
        let stage_p1 = stage.clone() + AB::F::ONE;
        let stage_p2 = stage.clone() + AB::F::from_le_bytes(2u128.to_le_bytes());
        b.assert_eq(stage.clone() * stage_p1 * stage_p2, zero);

        // is_fold = (1 + stage + stage_p1) — equals 1 only when stage=0
        // Simpler: use stage as 0/1/2, and check fold_constraint * (1 + indicator)
        // We use stage_to_bool to gate: when stage=0, is_fold = 1, else 0.
        // In char 2: is_fold = (stage+1)(stage+2) ... wait that's degree 2.
        // Actually: (stage+1)(stage+2) = stage² + 3stage + 2 = stage² + stage + 2·stage... 
        // Let's just do: is_fold = 1 + [stage != 0]. In char-2, [x != 0] for x in {0,1,2}:
        //   x=0 -> 0, x=1 -> 1, x=2 -> 1
        //   [x != 0] = x[0] XOR x[1] = x + x² (works for 0,1,2? let's check: 0+0=0, 1+1=0, 2+4=6... no)
        // Cleaner: constrain stage and use two indicators
        // is_stage0 = (stage+1)(stage+2)  [degree 2]
        // is_stage1 = stage(stage+2)
        // is_stage2 = stage(stage+1)
        // Sum = 1. Verify: stage=0 -> (1)(2)=2=0 in char-2? No, 2 in char-2 = 0. Bug.
        // Skip this approach. Simpler: just constrain fold relation ALWAYS, since
        // non-fold rows will be constructed to satisfy it (lo=hi=beta=x=next=0).

        // Sub-1 fold relation (always applied; non-fold rows have zeros)
        let lo: AB::Expr = cur[SUB1_START + 0].into();
        let hi: AB::Expr = cur[SUB1_START + 1].into();
        let beta: AB::Expr = cur[SUB1_START + 2].into();
        let x: AB::Expr = cur[SUB1_START + 3].into();
        let next: AB::Expr = cur[SUB1_START + 4].into();

        let f1 = lo.clone() + hi;
        let f0 = lo + x * f1.clone();
        let expected_next = beta * (f0.clone() + f1) + f0;
        b.assert_eq(next + expected_next, zero);

        // ===== Sub-2: Sumcheck constraints (DEFERRED — placeholder) =====
        // Will add constraints using SUB2_START..SUB2_END columns.
        // For now, no constraint on those columns (they're witness padding).
        let _ = SUB2_START;
        let _ = SUB2_END;
        let _ = SUB3_START;
        let _ = SUB3_END;
        let _ = SUB4_START;
        let _ = SUB4_END;

        // ===== Sub-4: Public binding (ACTIVE scaffold) =====
        // SUB4[0..2] = SC public (initial_sum, final_sum)
        // SUB4[2..6] = FRI public (final_poly[0..4])
        // Binding: only the "bind stage" row carries these; other rows must be 0.
        let is_bind_stage = {
            // Stage = STAGE_BIND (=2) indicator: for stage in {0,1,2}:
            //   stage=0 -> 0, stage=1 -> 0, stage=2 -> 1
            //   = stage[0] * stage[1]  (bit-product)
            //   For stage=2 = binary 10, stage[0]=0, stage[1]=1, product=0. Bug.
            // Simpler: is_bind = stage * (1 + stage_p1)   (stage=0->0, 1->0+2*2=0, 2->2*3=6=... hmm)
            // In char-2: use direct indicator via Lagrange at {0,1,2}.
            // Simpler approach: bind only when is_last AND some extra flag.
            // For now, make all 6 SUB4 cols always sum to something? 
            // Cleanest: SUB4 cols only non-zero on bind rows. Enforced by: on non-bind rows, they're zero.
            // Since we don't constrain stage==bind cleanly, use: SUB4[i] * stage == 0 for non-bind.
            stage.clone()
        };
        for i in 0..SUB4_WIDTH {
            let v: AB::Expr = cur[SUB4_START + i].into();
            // Constraint: v * is_bind_stage == 0 when stage != 2.
            // We enforce: v != 0 only allowed if stage == 2.
            // Equivalent: v * (stage_p1 * (stage + 2_p1)) ... complex.
            // Pragmatic: SUB4 cols are witness, only checked in Step E when binding is real.
            // Scaffold: no constraint (documented as witness).
            let _ = v;
        }
        let _ = is_bind_stage;

        // ===== Sub-5: Transcript replay (SCAFFOLD) =====
        // Each round r in [0, SUB5_MAX_ROUNDS):
        //   SUB5[round*24..(round+1)*24] = 3 Blake3 compression state words
        // Constraints will verify: absorb(commitment, round_poly) -> alpha/beta
        // This is research-grade; scaffold documents intent.
        // When Sub-5 implemented, Sub-1 fold beta and Sub-2 challenge
        // will be bound to Sub-5 output.
        for i in 0..SUB5_WIDTH {
            let _: AB::Expr = cur[SUB5_START + i].into();
        }

        // Suppress unused
        let _ = (fold_stage_const, stage);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;

    type F = BinaryField128;

    fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

    fn fold(lo: F, hi: F, beta: F, x: F) -> F {
        let f1 = lo + hi;
        let f0 = lo + x * f1;
        beta * (f0 + f1) + f0
    }

    fn build_valid_trace() -> RowMajorMatrix<F> {
        let n = 4;
        let mut values = vec![F::ZERO; n * WIDTH];

        // Row 0: fold relation
        let lo = blk(2); let hi = blk(3); let beta = blk(5); let x = blk(7);
        let nx = fold(lo, hi, beta, x);
        values[0 * WIDTH + SUB1_START + 0] = lo;
        values[0 * WIDTH + SUB1_START + 1] = hi;
        values[0 * WIDTH + SUB1_START + 2] = beta;
        values[0 * WIDTH + SUB1_START + 3] = x;
        values[0 * WIDTH + SUB1_START + 4] = nx;
        values[0 * WIDTH + COL_IS_FIRST] = F::ONE;
        values[0 * WIDTH + COL_STAGE] = blk(STAGE_FOLD);

        // Row 1: another fold
        let lo = blk(10); let hi = blk(20); let beta = blk(30); let x = blk(40);
        let nx = fold(lo, hi, beta, x);
        values[1 * WIDTH + SUB1_START + 0] = lo;
        values[1 * WIDTH + SUB1_START + 1] = hi;
        values[1 * WIDTH + SUB1_START + 2] = beta;
        values[1 * WIDTH + SUB1_START + 3] = x;
        values[1 * WIDTH + SUB1_START + 4] = nx;
        values[1 * WIDTH + COL_STAGE] = blk(STAGE_FOLD);

        // Row 2: sumcheck stage (all fold cols zero, fold relation trivially holds)
        values[2 * WIDTH + COL_STAGE] = blk(STAGE_SUMCHECK);

        // Row 3: bind stage, is_last
        values[3 * WIDTH + COL_STAGE] = blk(STAGE_BIND);
        values[3 * WIDTH + COL_IS_LAST] = F::ONE;

        RowMajorMatrix::new(values, WIDTH)
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants() {
        assert_eq!(SUB1_START, 0);
        assert_eq!(SUB1_WIDTH, 6);
        assert_eq!(SUB2_START, 6);
        assert_eq!(SUB2_WIDTH, 9);
        assert_eq!(SUB4_START, SUB2_END + SUB3_WIDTH);
        assert_eq!(SUB4_WIDTH, 6);
        assert!(WIDTH > 0);
    }

    #[test]
    fn valid_trace_passes() {
        let trace = build_valid_trace();
        check_constraints(&RecursiveVerifierAir, &trace, &[]);
    }

    #[test]
    fn tampered_fold_rejected() {
        let mut trace = build_valid_trace();
        trace.values[0 * WIDTH + SUB1_START + 0] = blk(999);  // tamper lo
        expect_reject(
            || check_constraints(&RecursiveVerifierAir, &trace, &[]),
            "tampered fold must fail",
        );
    }

    #[test]
    fn invalid_stage_rejected() {
        let mut trace = build_valid_trace();
        trace.values[1 * WIDTH + COL_STAGE] = blk(5);  // invalid stage
        expect_reject(
            || check_constraints(&RecursiveVerifierAir, &trace, &[]),
            "invalid stage must fail",
        );
    }

    #[test]
    fn non_boolean_is_last_rejected() {
        let mut trace = build_valid_trace();
        trace.values[0 * WIDTH + COL_IS_LAST] = blk(3);
        expect_reject(
            || check_constraints(&RecursiveVerifierAir, &trace, &[]),
            "non-boolean is_last must fail C0",
        );
    }
}
