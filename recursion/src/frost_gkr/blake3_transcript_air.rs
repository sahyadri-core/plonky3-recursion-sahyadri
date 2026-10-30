//! Blake3TranscriptAir - Phase T1.4b.2b.2b.1 (delegate + offsets).
//!
//! # Scope (this file)
//! - Delegate Blake3BinaryAir::default().eval(b) for compression constraints
//! - Blake3 column offset constants (informational for 2b.2b.2)
//! - is_last booleanity
//! - Integration test: real Blake3 compression trace + extras passes
//!
//! # TODO (2b.2b.2, next session)
//! - Bind chaining_value to Blake3 IV
//! - Bind block to ROUND_POLY || h0_bytes || h_inf_bytes || 0-padding
//! - Bind block_len = 42, flags = CHUNK_START|CHUNK_END|ROOT
//! - Extract alpha from output (final_chaining XOR IV) bytes 0..16
//! - Assert COL_ALPHA == alpha
//!
//! # Width choice
//! WIDTH = 11536 (Blake3 trace) + 4 (h0, h_inf, alpha, is_last) = 11540.
//! Blake3 trace is exactly BLAKE3_TRACE_COLS = 11536, matching
//! Blake3BinaryAir's column structure layout.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_blake3_air::Blake3BinaryAir;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder};
use p3_field::PrimeCharacteristicRing;

use super::sumcheck_verifier_air::SC_ROUND;

// ============================================================================
// Blake3 trace layout (bit-sliced: 32 bits per u32 word)
// ============================================================================

/// Blake3 binary AIR column count.
pub const BLAKE3_TRACE_COLS: usize = 11536;

/// Blake3 padding width from BaseAir::width() impl (next_power_of_two).
pub const BLAKE3_PADDED_WIDTH: usize = 16384;

// Blake3 internal column offsets (32 bits per u32 word, contiguous in struct):
// - chaining_value: 8 words * 32 bits = 256 cols
// - block: 16 words * 32 bits = 512 cols
// - counter_low: 32 cols
// - counter_high: 32 cols
// - block_len: 32 cols
// - flags: 32 cols
// - rounds: 10640 cols (remaining)
pub const B3_CHAINING_VALUE_OFFSET: usize = 0;
pub const B3_BLOCK_OFFSET: usize = 256;
pub const B3_COUNTER_LOW_OFFSET: usize = 768;
pub const B3_COUNTER_HIGH_OFFSET: usize = 800;
pub const B3_BLOCK_LEN_OFFSET: usize = 832;
pub const B3_FLAGS_OFFSET: usize = 864;

// ============================================================================
// Our extras
// ============================================================================

pub const COL_H0: usize = BLAKE3_TRACE_COLS;
pub const COL_H_INF: usize = BLAKE3_TRACE_COLS + 1;
pub const COL_ALPHA: usize = BLAKE3_TRACE_COLS + 2;
pub const COL_IS_LAST: usize = BLAKE3_TRACE_COLS + 3;
pub const WIDTH: usize = BLAKE3_TRACE_COLS + 4;
pub const NUM_PUBLIC: usize = 0;

pub struct Blake3TranscriptAir;

impl<F> BaseAir<F> for Blake3TranscriptAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for Blake3TranscriptAir {
    fn eval(&self, b: &mut AB) {
        // Delegate Blake3BinaryAir compression constraints (cols 0..11536).
        //
        // If this fails with width mismatch, the delegate needs the trace to
        // be exactly BLAKE3_TRACE_COLS wide, meaning our WIDTH=11540 isn't
        // compatible. Fallback: pad WIDTH to 16388 with prefix cols.
        Blake3BinaryAir::default().eval(b);

        // is_last booleanity
        let is_last: AB::Expr = b.main().current_slice()[COL_IS_LAST].into();
        b.assert_eq(is_last.clone() * is_last.clone() + is_last, AB::F::ZERO);

        // TODO(2b.2b.2):
        // 1. Bind chaining_value to IV (row 0, cols 0..256)
        // 2. Bind block to ROUND_POLY||h0||h_inf||padding (row 0, cols 256..768)
        // 3. Bind block_len to 42 (row 0, cols 832..864)
        // 4. Bind flags to 0x0B (row 0, cols 864..896)
        // 5. Extract alpha from output = final_chaining XOR IV, bytes 0..16
        // 6. Assert alpha == COL_ALPHA
    }
}

/// Bus wrapper: Blake3TranscriptAir + Pull (h0, h_inf, alpha) on SC_ROUND.
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
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::Matrix;

    type F = BinaryField128;

    const IV: [u32; 8] = [
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
        0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
    ];
    const CHUNK_START: u32 = 1;
    const CHUNK_END: u32 = 2;
    const ROOT: u32 = 8;

    fn build_valid_compression_input() -> Blake3CompressionInput {
        Blake3CompressionInput {
            chaining_value: IV,
            block: [0u32; 16],
            counter: 0,
            block_len: 64,
            flags: CHUNK_START | CHUNK_END | ROOT,
        }
    }

    fn build_blake3_trace_with_extras() -> RowMajorMatrix<F> {
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

    #[test]
    fn layout_constants() {
        assert_eq!(BLAKE3_TRACE_COLS, 11536);
        assert_eq!(BLAKE3_PADDED_WIDTH, 16384);
        assert_eq!(COL_H0, 11536);
        assert_eq!(COL_H_INF, 11537);
        assert_eq!(COL_ALPHA, 11538);
        assert_eq!(COL_IS_LAST, 11539);
        assert_eq!(WIDTH, 11540);
    }

    #[test]
    fn blake3_internal_offsets() {
        // Bit-sliced layout: 32 bits per u32 word, contiguous in Blake3BinaryCols
        assert_eq!(B3_CHAINING_VALUE_OFFSET, 0);
        assert_eq!(B3_BLOCK_OFFSET, 256);        // 8 words * 32 bits
        assert_eq!(B3_COUNTER_LOW_OFFSET, 768);  // + 16 words * 32 bits
        assert_eq!(B3_COUNTER_HIGH_OFFSET, 800);
        assert_eq!(B3_BLOCK_LEN_OFFSET, 832);
        assert_eq!(B3_FLAGS_OFFSET, 864);
        // Total input bits: 864 + 32 = 896, then rounds: 11536 - 896 = 10640
    }

    #[test]
    fn valid_blake3_compression_with_extras_passes() {
        let trace = build_blake3_trace_with_extras();
        let public = vec![];
        check_constraints(&Blake3TranscriptAir, &trace, &public);
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
