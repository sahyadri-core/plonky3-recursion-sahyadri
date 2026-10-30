//! Blake3TranscriptAir - Phase T1.4b.2b.2b.2 (boundary binding).
//!
//! # Scope (this file)
//! - Delegate Blake3BinaryAir::default().eval(b) [T1.4b.2b.2b.1]
//! - Row 0 binding (is_first_row constrained):
//!   - chaining_value = Blake3 IV (8 u32 = 256 bits)
//!   - counter_low = 0, counter_high = 0 (64 bits)
//!   - block_len = 42 (ROUND_POLY || h0 || h_inf)
//!   - flags = 0x0B (CHUNK_START | CHUNK_END | ROOT)
//!   - block bytes 0..10 = ROUND_POLY constant
//!   - block bytes 42..64 = zero padding
//! - is_last booleanity
//! - Bus Pull (h0, h_inf, alpha) on SC_ROUND last row
//!
//! # Deferred (T1.4b.2b.2b.2b/c, next sessions)
//! - Block bytes 10..42 = h0_bytes || h_inf_bytes (needs byte decomposition
//!   of h0/h_inf field elements into 16-bit constraint each)
//! - Alpha extraction from Blake3 output = IV XOR final_state[8..16]
//! - Assert alpha == COL_ALPHA
//!
//! # Soundness
//! Blake3 compression IS structurally verified on correct IV + ROUND_POLY.
//! Alpha is still unconstrained witness — Fiat-Shamir binding completes
//! when byte decomposition + output extraction are added.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_blake3_air::Blake3BinaryAir;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder};
use p3_field::PrimeCharacteristicRing;

use super::sumcheck_verifier_air::SC_ROUND;

// ============================================================================
// Blake3 trace layout (bit-sliced: 32 bits per u32 word)
// ============================================================================

pub const BLAKE3_TRACE_COLS: usize = 11536;

pub const B3_CHAINING_VALUE_OFFSET: usize = 0;    // 8 words * 32 bits
pub const B3_BLOCK_OFFSET: usize = 256;           // 16 words * 32 bits
pub const B3_COUNTER_LOW_OFFSET: usize = 768;     // 32 bits
pub const B3_COUNTER_HIGH_OFFSET: usize = 800;    // 32 bits
pub const B3_BLOCK_LEN_OFFSET: usize = 832;       // 32 bits
pub const B3_FLAGS_OFFSET: usize = 864;           // 32 bits

pub const COL_H0: usize = BLAKE3_TRACE_COLS;
pub const COL_H_INF: usize = BLAKE3_TRACE_COLS + 1;
pub const COL_ALPHA: usize = BLAKE3_TRACE_COLS + 2;
pub const COL_IS_LAST: usize = BLAKE3_TRACE_COLS + 3;
pub const WIDTH: usize = BLAKE3_TRACE_COLS + 4;
pub const NUM_PUBLIC: usize = 0;

// ============================================================================
// Blake3 spec constants (public, compile-time known)
// ============================================================================

const IV_U32: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

const BLOCK_LEN_CONST: u32 = 42;          // 10 (ROUND_POLY) + 16 (h0) + 16 (h_inf)
const FLAGS_CONST: u32 = 0x0B;            // CHUNK_START | CHUNK_END | ROOT
const ROUND_POLY_CONST: &[u8; 10] = b"round_poly";
const PADDING_START: usize = 42;          // first byte of zero padding
const BLOCK_BYTES: usize = 64;

pub struct Blake3TranscriptAir;

impl<F> BaseAir<F> for Blake3TranscriptAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

/// Assert `is_first * (cur + c) == 0` for a constant bit `c` (0 or 1).
/// Forces row 0 (first row) to have value `c` at that column.
#[inline]
fn assert_first_row_bit<AB: AirBuilder<F = BinaryField128>>(
    b: &mut AB,
    is_first: AB::Expr,
    col: usize,
    bit: bool,
) {
    let c = if bit { AB::F::ONE } else { AB::F::ZERO };
    let cur: AB::Expr = b.main().current_slice()[col].into();
    b.assert_eq(is_first * (cur + c), AB::F::ZERO);
}

/// Assert `is_first * cur == 0` — forces row-0 cell to 0.
#[inline]
fn assert_first_row_zero<AB: AirBuilder<F = BinaryField128>>(
    b: &mut AB,
    is_first: AB::Expr,
    col: usize,
) {
    let cur: AB::Expr = b.main().current_slice()[col].into();
    b.assert_eq(is_first * cur, AB::F::ZERO);
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for Blake3TranscriptAir {
    fn eval(&self, b: &mut AB) {
        Blake3BinaryAir::default().eval(b);

        let is_first: AB::Expr = b.is_first_row().into();

        // 1. Chaining value = Blake3 IV (256 bits)
        for i in 0..8 {
            for j in 0..32 {
                let bit = (IV_U32[i] >> j) & 1 == 1;
                assert_first_row_bit(b, is_first.clone(), B3_CHAINING_VALUE_OFFSET + i * 32 + j, bit);
            }
        }

        // 2. Counter = 0 (64 bits)
        for j in 0..32 {
            assert_first_row_zero(b, is_first.clone(), B3_COUNTER_LOW_OFFSET + j);
            assert_first_row_zero(b, is_first.clone(), B3_COUNTER_HIGH_OFFSET + j);
        }

        // 3. Block_len = 42 (32 bits)
        for j in 0..32 {
            let bit = (BLOCK_LEN_CONST >> j) & 1 == 1;
            assert_first_row_bit(b, is_first.clone(), B3_BLOCK_LEN_OFFSET + j, bit);
        }

        // 4. Flags = 0x0B (32 bits)
        for j in 0..32 {
            let bit = (FLAGS_CONST >> j) & 1 == 1;
            assert_first_row_bit(b, is_first.clone(), B3_FLAGS_OFFSET + j, bit);
        }

        // 5. Block bytes 0..10 = ROUND_POLY (80 bits, constant)
        for byte_idx in 0..10 {
            let byte = ROUND_POLY_CONST[byte_idx];
            for bit_in_byte in 0..8 {
                let block_bit = byte_idx * 8 + bit_in_byte;
                let word_idx = block_bit / 32;
                let bit_in_word = block_bit % 32;
                let bit = (byte >> bit_in_byte) & 1 == 1;
                assert_first_row_bit(
                    b,
                    is_first.clone(),
                    B3_BLOCK_OFFSET + word_idx * 32 + bit_in_word,
                    bit,
                );
            }
        }

        // 6. Block bytes 42..64 = zero padding (176 bits, constant 0)
        for byte_idx in PADDING_START..BLOCK_BYTES {
            for bit_in_byte in 0..8 {
                let block_bit = byte_idx * 8 + bit_in_byte;
                let word_idx = block_bit / 32;
                let bit_in_word = block_bit % 32;
                assert_first_row_zero(
                    b,
                    is_first.clone(),
                    B3_BLOCK_OFFSET + word_idx * 32 + bit_in_word,
                );
            }
        }

        // 7. is_last booleanity
        let is_last: AB::Expr = b.main().current_slice()[COL_IS_LAST].into();
        b.assert_eq(is_last.clone() * is_last.clone() + is_last, AB::F::ZERO);

        // TODO(2b.2b.2b.2b, next session):
        // - Block bytes 10..26 = h0 bytes (16 witness bytes; decompose h0 field)
        // - Block bytes 26..42 = h_inf bytes (16 witness bytes; decompose h_inf)
        // - alpha = Blake3 output bytes 0..16 = (IV XOR final_state[8..16]) bytes 0..16
        // - assert alpha == COL_ALPHA
    }
}

pub struct Blake3TranscriptBusAir;

impl<F> BaseAir<F> for Blake3TranscriptBusAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB>
    for Blake3TranscriptBusAir
{
    fn eval(&self, b: &mut AB) {
        Blake3TranscriptAir.eval(b);

        let (h0, h_inf, alpha): (AB::Expr, AB::Expr, AB::Expr) = {
            let main = b.main();
            let cur = main.current_slice();
            (
                AB::Expr::from(cur[COL_H0]),
                AB::Expr::from(cur[COL_H_INF]),
                AB::Expr::from(cur[COL_ALPHA]),
            )
        };

        let active = b.is_last_row();
        b.push_bus_interaction(
            SC_ROUND,
            BusDirection::Pull,
            [h0, h_inf, alpha],
            BusActivation::Boolean(active),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_blake3_air::{Blake3CompressionInput, generate_binary_trace_rows};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::Matrix;

    type F = BinaryField128;

    const CHUNK_START: u32 = 1;
    const CHUNK_END: u32 = 2;
    const ROOT_FLAG: u32 = 8;

    fn build_valid_compression_input() -> Blake3CompressionInput {
        let mut block = [0u32; 16];
        // ROUND_POLY bytes 0..10
        for i in 0..10 {
            let word_idx = i / 4;
            let byte_in_word = i % 4;
            block[word_idx] |= (ROUND_POLY_CONST[i] as u32) << (byte_in_word * 8);
        }
        // Bytes 10..42: h0/h_inf slots — set to 0 for now (T1.4b.2b.2b.2b will bind)
        // Bytes 42..64: padding zeros (already 0)

        Blake3CompressionInput {
            chaining_value: IV_U32,
            block,
            counter: 0,
            block_len: BLOCK_LEN_CONST,
            flags: CHUNK_START | CHUNK_END | ROOT_FLAG,
        }
    }

    fn build_trace_with_extras() -> RowMajorMatrix<F> {
        let input = build_valid_compression_input();
        let blake3 = generate_binary_trace_rows::<F>(vec![input], 0);
        let num_rows = blake3.height();
        let blake3_width = blake3.width();
        assert_eq!(blake3_width, BLAKE3_TRACE_COLS,
            "Blake3 trace width must be exactly BLAKE3_TRACE_COLS");

        let mut values = vec![F::ZERO; num_rows * WIDTH];
        for r in 0..num_rows {
            for c in 0..blake3_width {
                values[r * WIDTH + c] = blake3.values[r * blake3_width + c];
            }
            if r == num_rows - 1 {
                values[r * WIDTH + COL_IS_LAST] = F::ONE;
            }
        }
        RowMajorMatrix::new(values, WIDTH)
    }

    fn expect_reject<F2: FnOnce()>(f: F2, msg: &str) {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        assert!(r.is_err(), "{}", msg);
    }

    #[test]
    fn layout_constants() {
        assert_eq!(BLAKE3_TRACE_COLS, 11536);
        assert_eq!(B3_CHAINING_VALUE_OFFSET, 0);
        assert_eq!(B3_BLOCK_OFFSET, 256);
        assert_eq!(B3_COUNTER_LOW_OFFSET, 768);
        assert_eq!(B3_COUNTER_HIGH_OFFSET, 800);
        assert_eq!(B3_BLOCK_LEN_OFFSET, 832);
        assert_eq!(B3_FLAGS_OFFSET, 864);
        assert_eq!(COL_H0, 11536);
        assert_eq!(COL_IS_LAST, 11539);
        assert_eq!(WIDTH, 11540);
    }

    #[test]
    fn spec_constants() {
        assert_eq!(ROUND_POLY_CONST.len(), 10);
        assert_eq!(BLOCK_LEN_CONST, 42);
        assert_eq!(FLAGS_CONST, 0x0B);
        assert_eq!(PADDING_START, 42);
        // Sanity: ROUND_POLY = "round_poly"
        assert_eq!(ROUND_POLY_CONST[0], b'r');
        assert_eq!(ROUND_POLY_CONST[9], b'y');
    }

    #[test]
    fn valid_compression_with_binding_passes() {
        let trace = build_trace_with_extras();
        check_constraints(&Blake3TranscriptAir, &trace, &vec![]);
    }

    #[test]
    fn tampered_iv_bit_rejected() {
        let mut trace = build_trace_with_extras();
        // IV_U32[0] bit 0: 0x6A09E667 & 1 = 1. Flip to 0.
        trace.values[0 * WIDTH + B3_CHAINING_VALUE_OFFSET + 0] = F::ZERO;
        expect_reject(
            || check_constraints(&Blake3TranscriptAir, &trace, &vec![]),
            "tampered IV bit must be rejected",
        );
    }

    #[test]
    fn tampered_padding_rejected() {
        let mut trace = build_trace_with_extras();
        // Padding starts at byte 42. Set bit 0 of byte 42 to 1.
        let block_bit = 42 * 8;
        let word_idx = block_bit / 32;
        let bit_in_word = block_bit % 32;
        trace.values[0 * WIDTH + B3_BLOCK_OFFSET + word_idx * 32 + bit_in_word] = F::ONE;
        expect_reject(
            || check_constraints(&Blake3TranscriptAir, &trace, &vec![]),
            "tampered padding must be rejected",
        );
    }

    #[test]
    fn tampered_flags_rejected() {
        let mut trace = build_trace_with_extras();
        // FLAGS = 0x0B. Bit 0 should be 1. Flip to 0.
        trace.values[0 * WIDTH + B3_FLAGS_OFFSET + 0] = F::ZERO;
        expect_reject(
            || check_constraints(&Blake3TranscriptAir, &trace, &vec![]),
            "tampered flags bit must be rejected",
        );
    }

    #[test]
    fn air_type_checks() {
        let air = Blake3TranscriptAir;
        assert_eq!(BaseAir::<F>::width(&air), WIDTH);
        assert_eq!(BaseAir::<F>::num_public_values(&air), 0);
    }

    #[test]
    fn bus_wrapper_constructible() {
        let _ = Blake3TranscriptBusAir;
    }
}
