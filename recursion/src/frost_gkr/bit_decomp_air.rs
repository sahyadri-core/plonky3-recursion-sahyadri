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
//! # C2 IMPLEMENTED (byte-level reconstruction)
//! Since BF128 addition = XOR of bit patterns, reconstructing from bits is
//! just XOR-accumulating `bit_i * from_le_bytes(2^i)`. This matches the bit
//! pattern of the field element, no tower decomposition needed.
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

        // Extract bits + is_real from main in one borrow scope
        let (bits, is_real): (Vec<AB::Expr>, AB::Expr) = {
            let main = b.main();
            let cur = main.current_slice();
            let bits: Vec<AB::Expr> = (0..BITS).map(|i| cur[i].into()).collect();
            let is_real: AB::Expr = cur[COL_IS_REAL].into();
            (bits, is_real)
        };

        // C0: is_real booleanity
        b.assert_eq(is_real.clone() * is_real.clone() + is_real.clone(), zero);

        // C1: bit booleanity (gated by is_real)
        for i in 0..BITS {
            let bit = &bits[i];
            let bit_sq = bit.clone() * bit.clone();
            b.assert_eq(is_real.clone() * (bit_sq + bit.clone()), zero);
        }

        // C2a: is_first_row → is_real = 1
        // Forces at least one real decomposition row.
        let is_first: AB::Expr = b.is_first_row().into();
        let one_expr: AB::Expr = AB::F::ONE.into();
        b.assert_eq(is_first * (is_real.clone() + one_expr), zero);

        // C2b: is_real → sum_i(bit_i * X_i) = public[0]
        // where X_i = from_le_bytes(1u128 << i) as a field element.
        // Field addition = XOR of bit patterns, so summing single-bit
        // contributions reproduces the original u128 bit pattern.
        let mut reconstructed: AB::Expr = zero.into();
        for i in 0..BITS {
            let bit = &bits[i];
            let x_i_f: AB::F = AB::F::from_le_bytes((1u128 << i).to_le_bytes());
            let x_i_expr: AB::Expr = x_i_f.into();
            reconstructed = reconstructed + bit.clone() * x_i_expr;
        }
        let pub_val: AB::Expr = b.public_values()[0].into();
        b.assert_eq(is_real * (reconstructed + pub_val), zero);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;

    type F = BinaryField128;

    fn build_trace(value: u128) -> (RowMajorMatrix<F>, Vec<F>) {
        // Row 0: real decomposition (is_real=1)
        // Row 1: padding (is_real=0)
        let mut values = vec![F::ZERO; 2 * WIDTH];
        for i in 0..128 {
            if (value >> i) & 1 == 1 {
                values[i] = F::ONE;
            }
        }
        values[COL_IS_REAL] = F::ONE;

        let public = vec![F::from_le_bytes(value.to_le_bytes())];
        (RowMajorMatrix::new(values, WIDTH), public)
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants_c2() {
        assert_eq!(BITS, 128);
        assert_eq!(COL_IS_REAL, 128);
        assert_eq!(WIDTH, 129);
        assert_eq!(NUM_PUBLIC, 1);
    }

    #[test]
    fn valid_decomposition_passes() {
        let v: u128 = 0x123456789ABCDEF0123456789ABCDEF0;
        let (trace, public) = build_trace(v);
        check_constraints(&BitDecompAir, &trace, &public);
    }

    #[test]
    fn zero_value_passes() {
        let (trace, public) = build_trace(0);
        check_constraints(&BitDecompAir, &trace, &public);
    }

    #[test]
    fn max_value_passes() {
        let (trace, public) = build_trace(u128::MAX);
        check_constraints(&BitDecompAir, &trace, &public);
    }

    #[test]
    fn single_bit_passes() {
        let (trace, public) = build_trace(1);
        check_constraints(&BitDecompAir, &trace, &public);
    }

    #[test]
    fn high_bit_passes() {
        let (trace, public) = build_trace(1u128 << 127);
        check_constraints(&BitDecompAir, &trace, &public);
    }

    #[test]
    fn tampered_bit_rejected() {
        let v: u128 = 0x123456789ABCDEF0123456789ABCDEF0;
        let (mut trace, public) = build_trace(v);
        trace.values[0] = if trace.values[0] == F::ONE { F::ZERO } else { F::ONE };
        expect_reject(
            || check_constraints(&BitDecompAir, &trace, &public),
            "tampered bit must fail C2b",
        );
    }

    #[test]
    fn no_is_real_on_first_row_rejected() {
        let v: u128 = 0xABCD;
        let (mut trace, public) = build_trace(v);
        trace.values[COL_IS_REAL] = F::ZERO;
        expect_reject(
            || check_constraints(&BitDecompAir, &trace, &public),
            "is_real=0 on first row must fail C2a",
        );
    }

    #[test]
    fn tampered_public_rejected() {
        let v: u128 = 0xABCD;
        let (trace, mut public) = build_trace(v);
        public[0] = public[0] + F::ONE;
        expect_reject(
            || check_constraints(&BitDecompAir, &trace, &public),
            "tampered public must fail C2b",
        );
    }

    #[test]
    fn non_boolean_bit_rejected() {
        let v: u128 = 0;
        let (mut trace, public) = build_trace(v);
        // Set a bit to 2 (not boolean)
        trace.values[5] = F::from_le_bytes(2u128.to_le_bytes());
        expect_reject(
            || check_constraints(&BitDecompAir, &trace, &public),
            "non-boolean bit must fail C1",
        );
    }
}
