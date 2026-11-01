//! CompressedSumcheckAir -- T1.5d Path A (semantically correct for Plonky3).
//!
//! Verifies Plonky3's `GenericDegreeProof` compressed sumcheck in-circuit.
//!
//! # Column semantics (matching Plonky3 exactly)
//! Plonky3's `RoundPolyInterpolator::eval` reconstructs:
//!   full = [evals[0], sum-h(0), evals[1], evals[2], evals[3]]  (5 points)
//!   h(0) = evals[0]
//!   h(1) = sum + h(0)          [derived, NOT transmitted]
//!   h(2) = evals[1]
//!   h(3) = evals[2]
//!   h(4) = evals[3]
//!
//! Domain = {0, 1, 2, 3, 4} (integer-valued field elements).
//! running_out = p(alpha) where p interpolates full over domain.
//!
//! # Layout (WIDTH = 9)
//! - 0: evals[0] = h(0)
//! - 1: evals[1] = h(2)  [NOT h(1)!]
//! - 2: evals[2] = h(3)
//! - 3: evals[3] = h(4)
//! - 4: running_in (sum from prev round / claimed_sum for round 0)
//! - 5: running_out = p(alpha)
//! - 6: alpha (challenge)
//! - 7: is_first (bool)
//! - 8: is_last (bool)
//!
//! # Public
//! - public[0]: initial_claimed_sum
//! - public[1]: final_claimed_sum
//!
//! # Constraints
//! C0: is_first, is_last booleanity
//! C1: is_first -> running_in == public[0]
//! C3: running_out == p(alpha)  [Lagrange interpolation]
//! C4: running_out == next.running_in (except last row)
//! C5: is_last -> running_out == public[1]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::{Field, PrimeCharacteristicRing};

pub const COL_EVALS0: usize = 0;
pub const COL_EVALS1: usize = 1;
pub const COL_EVALS2: usize = 2;
pub const COL_EVALS3: usize = 3;
pub const COL_RUNNING_IN: usize = 4;
pub const COL_RUNNING_OUT: usize = 5;
pub const COL_CHALLENGE: usize = 6;
pub const COL_IS_FIRST: usize = 7;
pub const COL_IS_LAST: usize = 8;
pub const WIDTH: usize = 9;
pub const NUM_PUBLIC: usize = 2;

/// Domain points: {0, 1, 2, 3, 4} as field elements.
const DOMAIN_LEN: usize = 5;

type F = BinaryField128;

fn domain_point(j: u128) -> F {
    F::from_le_bytes(j.to_le_bytes())
}

/// Precomputed Lagrange coefficients: L_i(x) = sum_k coeffs[i][k] * x^k
///
/// Computed once natively at AIR construction.
pub struct CompressedSumcheckAir {
    lagrange: [[F; DOMAIN_LEN]; DOMAIN_LEN],  // [i][k]: coeff of x^k in L_i
}

impl CompressedSumcheckAir {
    pub fn new() -> Self {
        let mut lagrange = [[F::ZERO; DOMAIN_LEN]; DOMAIN_LEN];

        for i in 0..DOMAIN_LEN {
            // Compute L_i(x) = prod_{j != i} (x + j) / prod_{j != i} (i + j)
            // in char 2: (x - j) = (x + j)
            let mut poly = [F::ZERO; DOMAIN_LEN];
            poly[0] = F::ONE;
            let mut deg = 0;
            let mut denom = F::ONE;

            for j in 0..DOMAIN_LEN {
                if i == j { continue; }
                let j_f = domain_point(j as u128);
                let i_plus_j = domain_point(i as u128) + j_f;
                denom = denom * i_plus_j;

                // Multiply poly by (x + j_f):
                // new[k] = poly[k-1] + j_f * poly[k]
                let mut new_poly = [F::ZERO; DOMAIN_LEN];
                for k in 0..=deg + 1 {
                    if k < DOMAIN_LEN {
                        let mut v = F::ZERO;
                        if k >= 1 { v = v + poly[k - 1]; }
                        if k <= deg { v = v + j_f * poly[k]; }
                        new_poly[k] = v;
                    }
                }
                poly = new_poly;
                deg += 1;
            }

            let denom_inv = denom.try_inverse().expect("domain points distinct");
            for k in 0..DOMAIN_LEN {
                lagrange[i][k] = poly[k] * denom_inv;
            }
        }

        Self { lagrange }
    }
}

impl<Fb> BaseAir<Fb> for CompressedSumcheckAir {
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

        let e0: AB::Expr = cur[COL_EVALS0].into();  // h(0)
        let e1: AB::Expr = cur[COL_EVALS1].into();  // h(2)
        let e2: AB::Expr = cur[COL_EVALS2].into();  // h(3)
        let e3: AB::Expr = cur[COL_EVALS3].into();  // h(4)
        let running_in: AB::Expr = cur[COL_RUNNING_IN].into();
        let running_out: AB::Expr = cur[COL_RUNNING_OUT].into();
        let alpha: AB::Expr = cur[COL_CHALLENGE].into();
        let is_first: AB::Expr = cur[COL_IS_FIRST].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();
        let next_running_in: AB::Expr = next[COL_RUNNING_IN].into();

        // C0: booleanity
        b.assert_eq(is_first.clone() * is_first.clone() + is_first.clone(), zero);
        b.assert_eq(is_last.clone() * is_last.clone() + is_last.clone(), zero);

        // C1: first row -- running_in == public[0]
        let init: AB::Expr = b.public_values()[0].into();
        b.assert_eq(is_first.clone() * (running_in.clone() + init), zero);

        // Build h(0)..h(4) expressions
        let h: [AB::Expr; 5] = [
            e0.clone(),                              // h(0)
            running_in.clone() + e0.clone(),         // h(1) = running_in + h(0)
            e1,                                       // h(2)
            e2,                                       // h(3)
            e3,                                       // h(4)
        ];

        // C3: running_out = p(alpha) = sum_k alpha^k * (sum_i h_i * coeffs[i][k])
        let mut p_alpha: AB::Expr = zero.into();
        let mut alpha_pow: AB::Expr = one.into();  // alpha^0 = 1
        for k in 0..DOMAIN_LEN {
            let mut ck: AB::Expr = zero.into();
            for i in 0..DOMAIN_LEN {
                let coeff_bytes = self.lagrange[i][k].to_le_bytes_or_repr();
                let coeff_f = BinaryField128::from_le_bytes(coeff_bytes);
                let coeff: AB::Expr = coeff_f.into();
                ck = ck + h[i].clone() * coeff;
            }
            p_alpha = p_alpha + ck * alpha_pow.clone();
            alpha_pow = alpha_pow * alpha.clone();
        }
        b.assert_eq(running_out.clone() + p_alpha, zero);

        // C4: transition -- running_out == next.running_in (except last row)
        let not_last = is_last.clone() + one;
        b.assert_eq(not_last * (running_out.clone() + next_running_in), zero);

        // C5: last row -- running_out == public[1]
        let fin: AB::Expr = b.public_values()[1].into();
        b.assert_eq(is_last.clone() * (running_out.clone() + fin), zero);
    }
}

/// Helper trait to convert BinaryField128 to bytes (via unsafe transmute as u128).
trait ToBytes {
    fn to_le_bytes_or_repr(&self) -> [u8; 16];
}

impl ToBytes for BinaryField128 {
    fn to_le_bytes_or_repr(&self) -> [u8; 16] {
        let v: u128 = unsafe { core::mem::transmute_copy(self) };
        v.to_le_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_matrix::dense::RowMajorMatrix;

    fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

    /// Native Lagrange interpolation for test data generation.
    fn lagrange_eval(h: [F; 5], alpha: F) -> F {
        let mut result = F::ZERO;
        for i in 0..5 {
            let mut num = F::ONE;
            let mut den = F::ONE;
            for j in 0..5 {
                if i == j { continue; }
                let aj = domain_point(j as u128);
                let ai = domain_point(i as u128);
                num = num * (alpha + aj);
                den = den * (ai + aj);
            }
            let li = num * den.try_inverse().expect("nonzero denom");
            result = result + h[i] * li;
        }
        result
    }

    fn build_valid_trace() -> (RowMajorMatrix<F>, Vec<F>) {
        let air = CompressedSumcheckAir::new();
        let _ = air;  // Just for consistency

        let mut values = vec![F::ZERO; 2 * WIDTH];

        // Row 0
        let e0_r0 = blk(1);   // h(0)
        let e1_r0 = blk(3);   // h(2)
        let e2_r0 = blk(4);   // h(3)
        let e3_r0 = blk(5);   // h(4)
        let r0_in = blk(10);
        let alpha_r0 = blk(100);

        // Native p(alpha) for row 0
        let h_r0: [F; 5] = [e0_r0, r0_in + e0_r0, e1_r0, e2_r0, e3_r0];
        let r0_out = lagrange_eval(h_r0, alpha_r0);

        values[COL_EVALS0] = e0_r0;
        values[COL_EVALS1] = e1_r0;
        values[COL_EVALS2] = e2_r0;
        values[COL_EVALS3] = e3_r0;
        values[COL_RUNNING_IN] = r0_in;
        values[COL_RUNNING_OUT] = r0_out;
        values[COL_CHALLENGE] = alpha_r0;
        values[COL_IS_FIRST] = F::ONE;

        // Row 1: running_in = r0_out (chained)
        let e0_r1 = blk(11);
        let e1_r1 = blk(13);
        let e2_r1 = blk(14);
        let e3_r1 = blk(15);
        let r1_in = r0_out;  // C4 satisfied
        let alpha_r1 = blk(200);

        let h_r1: [F; 5] = [e0_r1, r1_in + e0_r1, e1_r1, e2_r1, e3_r1];
        let r1_out = lagrange_eval(h_r1, alpha_r1);

        values[WIDTH + COL_EVALS0] = e0_r1;
        values[WIDTH + COL_EVALS1] = e1_r1;
        values[WIDTH + COL_EVALS2] = e2_r1;
        values[WIDTH + COL_EVALS3] = e3_r1;
        values[WIDTH + COL_RUNNING_IN] = r1_in;
        values[WIDTH + COL_RUNNING_OUT] = r1_out;
        values[WIDTH + COL_CHALLENGE] = alpha_r1;
        values[WIDTH + COL_IS_LAST] = F::ONE;

        let public = vec![r0_in, r1_out];  // [initial, final]
        (RowMajorMatrix::new(values, WIDTH), public)
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn lagrange_basis_is_valid() {
        // Sanity: L_i(j) == delta_ij
        let air = CompressedSumcheckAir::new();
        for i in 0..DOMAIN_LEN {
            for j in 0..DOMAIN_LEN {
                let mut v = F::ZERO;
                let mut pow = F::ONE;
                let x = domain_point(j as u128);
                for k in 0..DOMAIN_LEN {
                    v = v + air.lagrange[i][k] * pow;
                    pow = pow * x;
                }
                let expected = if i == j { F::ONE } else { F::ZERO };
                assert_eq!(v, expected, "L_{}({}) != delta", i, j);
            }
        }
    }

    #[test]
    fn layout_constants() {
        assert_eq!(WIDTH, 9);
        assert_eq!(NUM_PUBLIC, 2);
        assert_eq!(COL_EVALS0, 0);
        assert_eq!(COL_IS_LAST, 8);
    }

    #[test]
    fn valid_trace_passes() {
        let air = CompressedSumcheckAir::new();
        let (trace, public) = build_valid_trace();
        check_constraints(&air, &trace, &public);
    }

    #[test]
    fn tampered_initial_rejected() {
        let air = CompressedSumcheckAir::new();
        let (trace, mut public) = build_valid_trace();
        public[0] = public[0] + F::ONE;
        expect_reject(
            || check_constraints(&air, &trace, &public),
            "tampered initial must fail C1",
        );
    }

    #[test]
    fn tampered_final_rejected() {
        let air = CompressedSumcheckAir::new();
        let (trace, mut public) = build_valid_trace();
        public[1] = public[1] + F::ONE;
        expect_reject(
            || check_constraints(&air, &trace, &public),
            "tampered final must fail C5",
        );
    }

    #[test]
    fn tampered_running_out_rejected() {
        let air = CompressedSumcheckAir::new();
        let (mut trace, public) = build_valid_trace();
        // Flip running_out on row 0 -- breaks C3 (interpolation) and C4 (chain)
        trace.values[COL_RUNNING_OUT] = trace.values[COL_RUNNING_OUT] + F::ONE;
        expect_reject(
            || check_constraints(&air, &trace, &public),
            "tampered running_out must fail C3/C4",
        );
    }

    #[test]
    fn tampered_transition_rejected() {
        let air = CompressedSumcheckAir::new();
        let (mut trace, public) = build_valid_trace();
        // Break chain: row 1's running_in != row 0's running_out
        trace.values[WIDTH + COL_RUNNING_IN] = blk(999);
        expect_reject(
            || check_constraints(&air, &trace, &public),
            "broken chain must fail C4",
        );
    }
}
