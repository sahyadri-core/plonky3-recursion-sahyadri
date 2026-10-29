//! SumcheckVerifierAir - Phase T1.4b.1 (fold + transition + boundary).
//!
//! Verifies the fold-step structure of a `p3_sumcheck::SumcheckData` in-circuit.
//!
//! # Row layout (WIDTH = 7)
//! | Col | Name         | Meaning |
//! |-----|--------------|---------|
//! | 0   | h0           | h(0)    |
//! | 1   | h_inf        | h(inf)  |
//! | 2   | alpha        | FS chal |
//! | 3   | claimed      | in sum  |
//! | 4   | next_claimed | out sum |
//! | 5   | is_first     | flag    |
//! | 6   | is_last      | flag    |
//!
//! # Public (NUM_PUBLIC = 2)
//! public[0] = initial_sum (round 0's claimed)
//! public[1] = final_sum   (last round's next_claimed)
//!
//! # Constraints (C1-C6)
//! C0: is_first, is_last boolean
//! C1: first row has is_first = 1
//! C2: last  row has is_last  = 1
//! C3: is_first * (claimed + initial_sum) = 0
//! C4: fold: next_claimed = h0 + (claimed + h_inf)*alpha + h_inf*alpha^2
//! C5: transition: next_claimed = next_row.claimed
//! C6: is_last * (next_claimed + final_sum) = 0
//!
//! # NOT YET DONE (C7 - T1.4b.2)
//! alpha derivation. Currently alpha is unconstrained witness. A malicious
//! prover can choose any alpha. Sound against honest prover, not fully
//! adversarial. Fiat-Shamir in-circuit is T1.4b.2's job (strategy TBD).
//!
//! # Soundness scope
//! OK:  fold arithmetic, chain linkage, boundary binding
//! NOT: alpha derivation (T1.4b.2)
//! NOT: interaction with PCS openings (T1.4c)

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

pub const COL_H0: usize = 0;
pub const COL_H_INF: usize = 1;
pub const COL_ALPHA: usize = 2;
pub const COL_CLAIMED: usize = 3;
pub const COL_NEXT_CLAIMED: usize = 4;
pub const COL_IS_FIRST: usize = 5;
pub const COL_IS_LAST: usize = 6;
pub const WIDTH: usize = 7;
pub const NUM_PUBLIC: usize = 2;

pub struct SumcheckVerifierAir;

impl<F> BaseAir<F> for SumcheckVerifierAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for SumcheckVerifierAir {
    fn eval(&self, b: &mut AB) {
        let one = AB::F::ONE;
        let zero = AB::F::ZERO;

        let main = b.main();
        let cur = main.current_slice();
        let next = main.next_slice();

        let h0: AB::Expr = cur[COL_H0].into();
        let h_inf: AB::Expr = cur[COL_H_INF].into();
        let alpha: AB::Expr = cur[COL_ALPHA].into();
        let claimed: AB::Expr = cur[COL_CLAIMED].into();
        let next_claimed: AB::Expr = cur[COL_NEXT_CLAIMED].into();
        let is_first: AB::Expr = cur[COL_IS_FIRST].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();
        let next_claimed_next_row: AB::Expr = next[COL_CLAIMED].into();

        // C0a, C0b: booleanity
        let is_first_sq = is_first.clone() * is_first.clone();
        b.assert_eq(is_first_sq + is_first.clone(), zero);
        let is_last_sq = is_last.clone() * is_last.clone();
        b.assert_eq(is_last_sq + is_last.clone(), zero);

        // C1: first row has is_first = 1
        let first_row: AB::Expr = b.is_first_row().into();
        b.assert_eq(first_row * (is_first.clone() + one), zero);

        // C2: last row has is_last = 1
        let last_row: AB::Expr = b.is_last_row().into();
        b.assert_eq(last_row * (is_last.clone() + one), zero);

        // C3: is_first * (claimed + initial_sum) = 0
        let initial: AB::Expr = b.public_values()[0].into();
        b.assert_eq(is_first.clone() * (claimed.clone() + initial), zero);

        // C4: fold: next_claimed = h0 + (claimed + h_inf)*alpha + h_inf*alpha^2
        let alpha_sq = alpha.clone() * alpha.clone();
        let fold = h0.clone()
            + (claimed.clone() + h_inf.clone()) * alpha.clone()
            + h_inf.clone() * alpha_sq;
        b.assert_eq(next_claimed.clone() + fold, zero);

        // C5: transition: next_claimed = next_row.claimed (when not last row)
        let not_last = is_last.clone() + one;
        b.assert_eq(
            not_last * (next_claimed.clone() + next_claimed_next_row),
            zero,
        );

        // C6: is_last * (next_claimed + final_sum) = 0
        let final_v: AB::Expr = b.public_values()[1].into();
        b.assert_eq(is_last.clone() * (next_claimed.clone() + final_v), zero);

        // TODO(T1.4b.2): C7 - alpha == transcript.round(h0, h_inf, state)
        // Strategy: in-circuit Poseidon2b vs witness + Transcript AIR vs public.
        // Currently alpha is unconstrained witness.
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

    /// Valid trace: h_inf=0, alpha=2 everywhere, h0=0.
    ///   fold reduces to: next_claimed = (claimed + 0)*2 = claimed * 2
    /// Row 0: claimed=1 -> next=2
    /// Row 1: claimed=2 -> next=4
    /// Row 2: claimed=4 -> next=8 (= final_sum)
    ///
    /// Chose alpha=2 (not 1) so tampering h_inf actually changes the fold:
    /// with alpha=1, the h_inf terms cancel in binary field (char 2).
    /// Fold function computed with actual binary-field arithmetic.
    ///
    /// BinaryField128 is tower-based (not polynomial basis), so 2*2 != 4
    /// necessarily. All test values must be computed via the actual field,
    /// not hardcoded from polynomial-basis intuition.
    fn fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
        let alpha_sq = alpha * alpha;
        h0 + (claimed + h_inf) * alpha + h_inf * alpha_sq
    }

    /// Valid trace: h_inf=0, alpha=2, h0=0.
    /// Fold reduces to: next_claimed = claimed * alpha (actual field mult).
    ///
    /// Chained 3 rows: claimed_0 -> claimed_1 = next_0 -> claimed_2 = next_1 -> next_2 (= final).
    fn valid_trace() -> (RowMajorMatrix<F>, Vec<F>) {
        let mut values = vec![F::ZERO; 3 * WIDTH];
        let h0 = blk(0);
        let h_inf = blk(0);
        let alpha = blk(2);

        // Row 0
        let claimed_0 = blk(1);
        let next_0 = fold(h0, h_inf, alpha, claimed_0);
        values[0 * WIDTH + COL_H0] = h0;
        values[0 * WIDTH + COL_H_INF] = h_inf;
        values[0 * WIDTH + COL_ALPHA] = alpha;
        values[0 * WIDTH + COL_CLAIMED] = claimed_0;
        values[0 * WIDTH + COL_NEXT_CLAIMED] = next_0;
        values[0 * WIDTH + COL_IS_FIRST] = F::ONE;
        values[0 * WIDTH + COL_IS_LAST] = F::ZERO;

        // Row 1
        let claimed_1 = next_0;
        let next_1 = fold(h0, h_inf, alpha, claimed_1);
        values[1 * WIDTH + COL_H0] = h0;
        values[1 * WIDTH + COL_H_INF] = h_inf;
        values[1 * WIDTH + COL_ALPHA] = alpha;
        values[1 * WIDTH + COL_CLAIMED] = claimed_1;
        values[1 * WIDTH + COL_NEXT_CLAIMED] = next_1;
        values[1 * WIDTH + COL_IS_FIRST] = F::ZERO;
        values[1 * WIDTH + COL_IS_LAST] = F::ZERO;

        // Row 2
        let claimed_2 = next_1;
        let next_2 = fold(h0, h_inf, alpha, claimed_2);
        values[2 * WIDTH + COL_H0] = h0;
        values[2 * WIDTH + COL_H_INF] = h_inf;
        values[2 * WIDTH + COL_ALPHA] = alpha;
        values[2 * WIDTH + COL_CLAIMED] = claimed_2;
        values[2 * WIDTH + COL_NEXT_CLAIMED] = next_2;
        values[2 * WIDTH + COL_IS_FIRST] = F::ZERO;
        values[2 * WIDTH + COL_IS_LAST] = F::ONE;

        (RowMajorMatrix::new(values, WIDTH), vec![claimed_0, next_2])
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants() {
        assert_eq!(WIDTH, 7);
        assert_eq!(NUM_PUBLIC, 2);
        assert_eq!(COL_H0, 0);
        assert_eq!(COL_IS_LAST, 6);
    }

    #[test]
    fn valid_trace_passes() {
        let (trace, public) = valid_trace();
        check_constraints(&SumcheckVerifierAir, &trace, &public);
    }

    #[test]
    fn tampered_h_inf_rejected() {
        let (mut trace, public) = valid_trace();
        trace.values[0 * WIDTH + COL_H_INF] = blk(1);
        expect_reject(
            || check_constraints(&SumcheckVerifierAir, &trace, &public),
            "tampered h_inf must fail fold",
        );
    }

    #[test]
    fn tampered_claimed_rejected() {
        let (mut trace, public) = valid_trace();
        trace.values[1 * WIDTH + COL_CLAIMED] = blk(99);
        expect_reject(
            || check_constraints(&SumcheckVerifierAir, &trace, &public),
            "tampered claimed must fail transition",
        );
    }

    #[test]
    fn tampered_final_sum_rejected() {
        let (trace, mut public) = valid_trace();
        public[1] = blk(999);
        expect_reject(
            || check_constraints(&SumcheckVerifierAir, &trace, &public),
            "tampered final_sum must fail C6",
        );
    }
}
