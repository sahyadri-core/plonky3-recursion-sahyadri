//! BitDecompAir -- Phase T1.5d-BitGadget (scaffold).
//!
//! Given a BinaryField128 value, decompose it into 128 bits via tower
//! structure.
//!
//! # Why (bit gadget need)
//! For Fiat-Shamir byte binding:
//! - h0 (BF128) -> 16 bytes -> Blake3 block
//! - Blake3 output (16 bytes) -> alpha (BF128)
//! Both need bit-level access to BF128.
//!
//! # Tower structure (Plonky3)
//! GF(2^128) is a tower extension:
//!   GF(2^128) over GF(2^64): b = b_lo + b_hi * X
//!   GF(2^64) over GF(2^32):  b_lo = b_lo_lo + b_lo_hi * Y
//!   ... 7 levels down to GF(2)
//!
//! Bit decomposition requires exposing this tower. But each level's
//! multiplication is field-specific, so reconstruction constraints must
//! mirror the tower's `mul` operation.
//!
//! # Row layout (WIDTH = 129)
//! - 0..128: 128 bits (bit_i in {0,1})
//! - 128: is_real (bool, marks which rows are real vs padding)
//!
//! # Public
//! - public[0]: the BF128 value being decomposed (in "reconstructed" form)
//!
//! # Constraints
//! C0: each bit_i is boolean
//! C1: is_real is boolean
//! C2: reconstruct_from_bits(bits) == public[0]  [TBD next session]
//!
//! # TODO (next session, after `blk_to_le_bytes` discovery)
//! - C2: tower multiplication to reconstruct BF128 from 128 bits
//! - The exact tower formula (which polynomial, which level ordering)
//!   depends on Plonky3's `BinaryField128` implementation
//! - Once `blk_to_le_bytes` semantics are known, C2 is straightforward
//!
//! # Status: SCAFFOLD
//! Layout + booleanity implemented. C2 reconstruction TBD.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

pub const BITS: usize = 128;
pub const COL_IS_REAL: usize = 128;
pub const WIDTH: usize = 129;
pub const NUM_PUBLIC: usize = 1;

pub struct BitDecompAir;

impl<F> BaseAir<F> for BitDecompAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for BitDecompAir {
    fn eval(&self, b: &mut AB) {
        let zero = AB::F::ZERO;

        let main = b.main();
        let cur = main.current_slice();

        // C0: booleanity on all 128 bits (only on is_real rows)
        let is_real: AB::Expr = cur[COL_IS_REAL].into();
        b.assert_eq(is_real.clone() * is_real.clone() + is_real.clone(), zero);

        for i in 0..BITS {
            let bit: AB::Expr = cur[i].into();
            let bit_sq = bit.clone() * bit.clone();
            // is_real * (bit^2 + bit) = 0  --> bit in {0,1} when is_real
            b.assert_eq(is_real.clone() * (bit_sq + bit), zero);
        }

        // C2: TODO -- reconstruct_from_bits(bits) == public[0]
        // Needs tower decomposition formula from `blk_to_le_bytes` internals.
        // Currently unconstrained: the bits are boolean but not yet bound to
        // any specific field value.
        let _ = b.public_values();
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
        // Single row, bits are boolean (C0 satisfied), is_real=1
        let mut values = vec![F::ZERO; WIDTH];
        // Set bits arbitrarily (booleanity satisfied; C2 TBD)
        for i in 0..BITS {
            values[i] = if i % 2 == 0 { F::ONE } else { F::ZERO };
        }
        values[COL_IS_REAL] = F::ONE;
        (RowMajorMatrix::new(values, WIDTH), vec![blk(0xAAAA)])
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants() {
        assert_eq!(WIDTH, 129);
        assert_eq!(NUM_PUBLIC, 1);
        assert_eq!(COL_IS_REAL, 128);
    }

    #[test]
    fn valid_trace_passes() {
        let (trace, public) = build_valid_trace();
        check_constraints(&BitDecompAir, &trace, &public);
    }

    #[test]
    fn non_boolean_bit_rejected() {
        let (mut trace, public) = build_valid_trace();
        trace.values[5] = blk(99);  // bit 5 not boolean
        expect_reject(
            || check_constraints(&BitDecompAir, &trace, &public),
            "non-boolean bit must fail C0",
        );
    }

    #[test]
    fn non_boolean_flag_rejected() {
        let (mut trace, public) = build_valid_trace();
        trace.values[COL_IS_REAL] = blk(99);
        expect_reject(
            || check_constraints(&BitDecompAir, &trace, &public),
            "non-boolean is_real must fail booleanity",
        );
    }
}
