//! CompressedSumcheckAir -- Phase T1.5d-PathA (scaffold).
//!
//! Verifies Plonky3's `GenericDegreeProof` compressed sumcheck in-circuit.
//!
//! # Why this exists (Path A)
//! From T1.5d step 2 discovery:
//! - MultiStark uses compressed sumcheck (2 rounds x 4 evals for arity 7)
//! - Round poly = degree-3 poly through {0,1,2,3} (4 evals per round)
//! - running_sum_next = interpolator.eval(evals, running_sum, challenge)
//! - Our SumcheckVerifierAir models 1-round-per-var SC sumcheck (mismatch)
//!
//! Path A redesign: match compressed format. This AIR = per-round verification
//! of the compressed sumcheck.
//!
//! # Row layout (WIDTH = 9)
//! - 0: h0 (poly eval at 0)
//! - 1: h1 (poly eval at 1)
//! - 2: h2 (poly eval at 2)
//! - 3: h3 (poly eval at 3)
//! - 4: running_in (claimed_sum from prev round)
//! - 5: running_out (claimed_sum for next round)
//! - 6: challenge (alpha for this round)
//! - 7: is_first (bool, marks round 0)
//! - 8: is_last (bool, marks final round)
//!
//! # Public
//! - public[0]: initial_claimed_sum
//! - public[1]: final_claimed_sum
//!
//! # Constraints
//! C0: is_first, is_last booleanity
//! C1: is_first -> running_in == public[0]
//! C2: running_in == h0 + h1 (sum over boolean hypercube, deg-3 poly)
//! C3: running_out == interpolate(h0..h3, challenge) [TBD next session]
//! C4: transition: running_out == next_row.running_in
//! C5: is_last -> running_out == public[1]
//!
//! # TODO (next session, after SuffixProver discovery)
//! - C3 interpolation: lagrange at challenge from 4 points
//! - challenge derivation: needs transcript state (Blake3 transcript AIR)
//!
//! # Status: SCAFFOLD
//! Layout + booleanity + C1/C2/C4/C5 implemented. C3 (interpolation) and
//! challenge derivation TBD.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

pub const COL_H0: usize = 0;
pub const COL_H1: usize = 1;
pub const COL_H2: usize = 2;
pub const COL_H3: usize = 3;
pub const COL_RUNNING_IN: usize = 4;
pub const COL_RUNNING_OUT: usize = 5;
pub const COL_CHALLENGE: usize = 6;
pub const COL_IS_FIRST: usize = 7;
pub const COL_IS_LAST: usize = 8;
pub const WIDTH: usize = 9;
pub const NUM_PUBLIC: usize = 2;

pub struct CompressedSumcheckAir;

impl<F> BaseAir<F> for CompressedSumcheckAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for CompressedSumcheckAir {
    fn eval(&self, b: &mut AB) {
        let zero = AB::F::ZERO;
        let one = AB::F::ONE;

        let main = b.main();
        let cur = main.current_slice();
        let next = main.next_slice();

        let h0: AB::Expr = cur[COL_H0].into();
        let h1: AB::Expr = cur[COL_H1].into();
        let h2: AB::Expr = cur[COL_H2].into();
        let h3: AB::Expr = cur[COL_H3].into();
        let running_in: AB::Expr = cur[COL_RUNNING_IN].into();
        let running_out: AB::Expr = cur[COL_RUNNING_OUT].into();
        let _challenge: AB::Expr = cur[COL_CHALLENGE].into();
        let is_first: AB::Expr = cur[COL_IS_FIRST].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();
        let next_running_in: AB::Expr = next[COL_RUNNING_IN].into();

        // C0: booleanity
        b.assert_eq(is_first.clone() * is_first.clone() + is_first.clone(), zero);
        b.assert_eq(is_last.clone() * is_last.clone() + is_last.clone(), zero);

        // C1: first row -- running_in == public[0]
        let init: AB::Expr = b.public_values()[0].into();
        b.assert_eq(is_first.clone() * (running_in.clone() + init), zero);

        // C2: sum over boolean hypercube -- running_in == h0 + h1
        b.assert_eq(running_in.clone() + (h0.clone() + h1.clone()), zero);

        // C3: TODO (interpolation at challenge from h0..h3)
        // For degree-3 poly through {0,1,2,3}:
        // p(x) = sum_i h_i * L_i(x)  where L_i is lagrange basis
        // Currently unconstrained -- TODO next session after SuffixProver discovery.
        // Placeholder: leave running_out as free witness (honest marker)
        let _ = (h2, h3);

        // C4: transition -- running_out == next_row.running_in (except last)
        let not_last = is_last.clone() + one.clone();
        b.assert_eq(
            not_last * (running_out.clone() + next_running_in),
            zero,
        );

        // C5: last row -- running_out == public[1]
        let fin: AB::Expr = b.public_values()[1].into();
        b.assert_eq(is_last.clone() * (running_out.clone() + fin), zero);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_matrix::dense::RowMajorMatrix;

    type F = BinaryField128;

    fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

    fn build_valid_trace() -> (RowMajorMatrix<F>, Vec<F>) {
        // 2 rounds (matching observed MultiStark compressed form)
        let mut values = vec![F::ZERO; 2 * WIDTH];

        // Row 0: is_first=1
        // C2 requires: running_in = h0 + h1 (per-row invariant in char-2)
        let r0_in = blk(1) + blk(2);   // = 1 XOR 2 = 3
        values[COL_H0] = blk(1);
        values[COL_H1] = blk(2);
        values[COL_H2] = blk(3);
        values[COL_H3] = blk(4);
        values[COL_RUNNING_IN] = r0_in;
        values[COL_RUNNING_OUT] = blk(6) + blk(7);  // = 1 (must match next row's running_in)
        values[COL_CHALLENGE] = blk(5);
        values[COL_IS_FIRST] = F::ONE;

        // Row 1: is_last=1
        // C2 requires: running_in = h0 + h1 = 6 XOR 7 = 1
        // C4 requires: this running_in == row 0's running_out (both = 1) ✓
        let r1_in = blk(6) + blk(7);   // = 1
        values[WIDTH + COL_H0] = blk(6);
        values[WIDTH + COL_H1] = blk(7);
        values[WIDTH + COL_H2] = blk(8);
        values[WIDTH + COL_H3] = blk(9);
        values[WIDTH + COL_RUNNING_IN] = r1_in;
        values[WIDTH + COL_RUNNING_OUT] = blk(20);  // final witness (C3 TBD)
        values[WIDTH + COL_CHALLENGE] = blk(11);
        values[WIDTH + COL_IS_LAST] = F::ONE;

        // public = [initial_sum, final_sum]
        let initial = r0_in;
        let final_v = blk(20);
        (RowMajorMatrix::new(values, WIDTH), vec![initial, final_v])
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants() {
        assert_eq!(WIDTH, 9);
        assert_eq!(NUM_PUBLIC, 2);
        assert_eq!(COL_H0, 0);
        assert_eq!(COL_IS_LAST, 8);
    }

    #[test]
    fn valid_trace_passes() {
        let (trace, public) = build_valid_trace();
        check_constraints(&CompressedSumcheckAir, &trace, &public);
    }

    #[test]
    fn tampered_initial_rejected() {
        let (trace, mut public) = build_valid_trace();
        public[0] = blk(999);
        expect_reject(
            || check_constraints(&CompressedSumcheckAir, &trace, &public),
            "tampered initial_sum must fail C1",
        );
    }

    #[test]
    fn tampered_transition_rejected() {
        let (mut trace, public) = build_valid_trace();
        // Break transition: round1.running_in != round0.running_out
        trace.values[WIDTH + COL_RUNNING_IN] = blk(999);
        expect_reject(
            || check_constraints(&CompressedSumcheckAir, &trace, &public),
            "broken transition must fail C4",
        );
    }

    #[test]
    fn tampered_final_rejected() {
        let (trace, mut public) = build_valid_trace();
        public[1] = blk(999);
        expect_reject(
            || check_constraints(&CompressedSumcheckAir, &trace, &public),
            "tampered final_sum must fail C5",
        );
    }
}
