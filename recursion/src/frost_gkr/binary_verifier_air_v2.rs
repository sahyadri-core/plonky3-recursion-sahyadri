//! BinaryVerifierAirV2 — Phase T1.2b-step2: real fold formula with `x` column.
//!
//! T1.2b validated fold_pair on real Plonky3 proof data (427/427 = 100%):
//!   f1 = lo + hi
//!   f0 = lo + x * f1     where x = domain_point(next_position << 1)
//!   next = beta * (f0 + f1) + f0
//!
//! Current BinaryVerifierAir models a different (simplified) fold; V2 has
//! the actual `x` column so real proof data can be proven in-circuit.
//!
//! # Layout (WIDTH = 6)
//! - 0: lo       (pair0)
//! - 1: hi       (pair1)
//! - 2: beta     (fold challenge)
//! - 3: x        (domain_point(next_position << 1))
//! - 4: next     (folded result)
//! - 5: is_last  (bool, marks last row)
//!
//! # Public inputs
//! None. Fold relation is verified per-row using witness (lo, hi, beta, x, next).
//! Higher layers bind these to commitments via PCS.
//!
//! # Constraints
//! C0: is_last ∈ {0,1}
//! C1: next == beta * (f0 + f1) + f0   where f1 = lo+hi, f0 = lo+x*f1
//!
//! # Soundness
//! Per-row fold correctness. Tampering any of lo/hi/beta/x/next breaks C1.
//!
//! # Missing (next steps)
//! - Binding to committed codewords (PCS-level integration)
//! - Reverse: extracting x from next_position in-circuit (domain_point AIR)
//! For now, x is witness; higher layer proves x = domain_point(...)

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

pub const COL_LO: usize = 0;
pub const COL_HI: usize = 1;
pub const COL_BETA: usize = 2;
pub const COL_X: usize = 3;
pub const COL_NEXT: usize = 4;
pub const COL_IS_LAST: usize = 5;
pub const WIDTH: usize = 6;
pub const NUM_PUBLIC: usize = 0;

pub struct BinaryVerifierAirV2;

impl<F> BaseAir<F> for BinaryVerifierAirV2 {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for BinaryVerifierAirV2 {
    fn eval(&self, b: &mut AB) {
        let zero = AB::F::ZERO;
        let one = AB::F::ONE;

        let main = b.main();
        let cur = main.current_slice();

        let lo: AB::Expr = cur[COL_LO].into();
        let hi: AB::Expr = cur[COL_HI].into();
        let beta: AB::Expr = cur[COL_BETA].into();
        let x: AB::Expr = cur[COL_X].into();
        let next: AB::Expr = cur[COL_NEXT].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();

        // C0: is_last booleanity
        b.assert_eq(is_last.clone() * is_last.clone() + is_last.clone(), zero);

        // C1: real fold relation
        // f1 = lo + hi
        // f0 = lo + x * f1
        // next = beta * (f0 + f1) + f0
        let f1 = lo.clone() + hi;
        let f0 = lo + x * f1.clone();
        let expected = beta * (f0.clone() + f1) + f0;
        b.assert_eq(next + expected, zero);

        // Suppress unused variable warning
        let _ = one;
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

    /// Compute fold_pair result from (lo, hi, beta, x).
    fn fold(lo: F, hi: F, beta: F, x: F) -> F {
        let f1 = lo + hi;
        let f0 = lo + x * f1;
        beta * (f0 + f1) + f0
    }

    fn build_valid_trace() -> RowMajorMatrix<F> {
        // 4 rows, each a valid fold relation.
        let mut values = vec![F::ZERO; 4 * WIDTH];

        // Row 0: lo=1, hi=2, beta=3, x=0 -> fold = 3*(3+... wait let me compute
        // f1 = 1+2 = 3, f0 = 1 + 0*3 = 1, next = 3*(1+3) + 1 = 3*2 + 1 = 6+1... 
        // Hmm char 2, addition is XOR. Let me be careful.
        // Actually easier: use fold() function directly
        let lo0 = blk(1); let hi0 = blk(2); let beta0 = blk(3); let x0 = blk(0);
        let next0 = fold(lo0, hi0, beta0, x0);
        values[COL_LO] = lo0;
        values[COL_HI] = hi0;
        values[COL_BETA] = beta0;
        values[COL_X] = x0;
        values[COL_NEXT] = next0;

        // Row 1
        let lo1 = blk(10); let hi1 = blk(20); let beta1 = blk(30); let x1 = blk(4);
        let next1 = fold(lo1, hi1, beta1, x1);
        values[WIDTH + COL_LO] = lo1;
        values[WIDTH + COL_HI] = hi1;
        values[WIDTH + COL_BETA] = beta1;
        values[WIDTH + COL_X] = x1;
        values[WIDTH + COL_NEXT] = next1;

        // Row 2
        let lo2 = blk(100); let hi2 = blk(200); let beta2 = blk(7); let x2 = blk(1000);
        let next2 = fold(lo2, hi2, beta2, x2);
        values[2 * WIDTH + COL_LO] = lo2;
        values[2 * WIDTH + COL_HI] = hi2;
        values[2 * WIDTH + COL_BETA] = beta2;
        values[2 * WIDTH + COL_X] = x2;
        values[2 * WIDTH + COL_NEXT] = next2;

        // Row 3 (is_last)
        let lo3 = blk(1); let hi3 = blk(1); let beta3 = blk(5); let x3 = blk(8);
        let next3 = fold(lo3, hi3, beta3, x3);
        values[3 * WIDTH + COL_LO] = lo3;
        values[3 * WIDTH + COL_HI] = hi3;
        values[3 * WIDTH + COL_BETA] = beta3;
        values[3 * WIDTH + COL_X] = x3;
        values[3 * WIDTH + COL_NEXT] = next3;
        values[3 * WIDTH + COL_IS_LAST] = F::ONE;

        RowMajorMatrix::new(values, WIDTH)
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants() {
        assert_eq!(WIDTH, 6);
        assert_eq!(NUM_PUBLIC, 0);
        assert_eq!(COL_LO, 0);
        assert_eq!(COL_IS_LAST, 5);
    }

    #[test]
    fn valid_trace_passes() {
        let trace = build_valid_trace();
        check_constraints(&BinaryVerifierAirV2, &trace, &[]);
    }

    #[test]
    fn tampered_lo_rejected() {
        let mut trace = build_valid_trace();
        trace.values[0 * WIDTH + COL_LO] = blk(999);
        expect_reject(
            || check_constraints(&BinaryVerifierAirV2, &trace, &[]),
            "tampered lo must fail fold",
        );
    }

    #[test]
    fn tampered_hi_rejected() {
        let mut trace = build_valid_trace();
        trace.values[1 * WIDTH + COL_HI] = blk(999);
        expect_reject(
            || check_constraints(&BinaryVerifierAirV2, &trace, &[]),
            "tampered hi must fail fold",
        );
    }

    #[test]
    fn tampered_beta_rejected() {
        let mut trace = build_valid_trace();
        trace.values[2 * WIDTH + COL_BETA] = blk(999);
        expect_reject(
            || check_constraints(&BinaryVerifierAirV2, &trace, &[]),
            "tampered beta must fail fold",
        );
    }

    #[test]
    fn tampered_x_rejected() {
        let mut trace = build_valid_trace();
        trace.values[0 * WIDTH + COL_X] = blk(999);
        expect_reject(
            || check_constraints(&BinaryVerifierAirV2, &trace, &[]),
            "tampered x must fail fold",
        );
    }

    #[test]
    fn tampered_next_rejected() {
        let mut trace = build_valid_trace();
        trace.values[3 * WIDTH + COL_NEXT] = blk(999);
        expect_reject(
            || check_constraints(&BinaryVerifierAirV2, &trace, &[]),
            "tampered next must fail fold",
        );
    }

    #[test]
    fn non_boolean_is_last_rejected() {
        let mut trace = build_valid_trace();
        trace.values[0 * WIDTH + COL_IS_LAST] = blk(2);
        expect_reject(
            || check_constraints(&BinaryVerifierAirV2, &trace, &[]),
            "non-boolean is_last must fail C0",
        );
    }
}
