//! Blake3TranscriptAir - Phase T1.4b.2b.2a (skeleton).
//!
//! Verifies that `alpha = Blake3(ROUND_POLY || h0_bytes || h_inf_bytes)[0..16]`
//! in-circuit, binding Fiat-Shamir derivation to Blake3 compression.
//!
//! # Layout (WIDTH = 11540)
//! - 0..11536:  Blake3 compression trace (delegated to Blake3BinaryAir.eval, T1.4b.2b.2b)
//! - 11536:     h0     (BF128)
//! - 11537:     h_inf  (BF128)
//! - 11538:     alpha  (BF128, expected = Blake3 output[0..16])
//! - 11539:     is_last (boolean, only last row pulls)
//!
//! # Bus
//! `SC_ROUND` Pull (h0, h_inf, alpha) on last row.
//! Matches `SumcheckVerifierBusAir` Push.
//!
//! # Scope (T1.4b.2b.2a - this file)
//! - Layout constants
//! - Booleanity of is_last
//! - Bus Pull (h0, h_inf, alpha) on SC_ROUND, last row
//! - Compression input builder helper (for test data)
//!
//! # TODO (T1.4b.2b.2b, next session)
//! - Delegate `Blake3BinaryAir::default().eval(b)` on cols 0..11536
//! - Bind Blake3 input block bytes to (ROUND_POLY, h0_bytes, h_inf_bytes)
//! - Extract alpha from Blake3 output bytes 0..16
//! - Real integration test with SumcheckData
//!
//! # Soundness
//! Skeleton: alpha is unconstrained witness (same as T1.4b.1 status).
//! After T1.4b.2b.2b: alpha bound to actual Blake3 computation.
//!
//! # Why Blake3 (not Keccak, not Poseidon2b sponge)
//! BinaryPcs transcript uses `HashChallenger<u8, ByteHash, 32>`. Default
//! ByteHash is Keccak256Hash, but no Keccak AIR exists. Blake3BinaryAir
//! (milestone 3, 816B proof) is working. Swapping transcript to Blake3
//! avoids building Keccak AIR (1-2 weeks saved).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder};
use p3_field::PrimeCharacteristicRing;

use super::sumcheck_verifier_air::SC_ROUND;

/// Blake3 binary AIR trace column count.
///
/// From milestone 3: 1 compression = 1 row x 11536 cols.
pub const BLAKE3_TRACE_COLS: usize = 11536;

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
        // C0: is_last booleanity (only constraint wired in skeleton)
        let (is_last,): (AB::Expr,) = {
            let main = b.main();
            let cur = main.current_slice();
            let v: AB::Expr = cur[COL_IS_LAST].into();
            (v,)
        };
        b.assert_eq(is_last.clone() * is_last.clone() + is_last, AB::F::ZERO);

        // TODO(T1.4b.2b.2b): 
        // 1. Blake3BinaryAir::default().eval(b)  [delegate cols 0..11536]
        // 2. Bind input block bytes to (ROUND_POLY || h0_bytes || h_inf_bytes)
        // 3. Extract alpha from Blake3 output bytes 0..16
        // 4. Assert alpha == COL_ALPHA
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

/// Build a `Blake3CompressionInput` for test data.
///
/// Mirrors Fiat-Shamir: `Blake3(ROUND_POLY || h0_bytes || h_inf_bytes)`.
///
/// ROUND_POLY = b"round_poly" (10 bytes)
/// h0 as 16 bytes little-endian (BF128)
/// h_inf as 16 bytes little-endian
/// Padding to 64-byte Blake3 block with zeros.
/// block_len = 42, flags = CHUNK_START | CHUNK_END | ROOT, counter = 0.
pub fn build_compression_input(
    h0: BinaryField128,
    h_inf: BinaryField128,
) -> Blake3CompressionInputFake {
    // Filled in next session (T1.4b.2b.2b) - needs actual Blake3CompressionInput
    // from p3_blake3_air. For now, return marker.
    let _ = (h0, h_inf);
    Blake3CompressionInputFake { h0, h_inf }
}

/// Placeholder for T1.4b.2b.2b - actual Blake3CompressionInput conversion.
pub struct Blake3CompressionInputFake {
    pub h0: BinaryField128,
    pub h_inf: BinaryField128,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_constants() {
        assert_eq!(BLAKE3_TRACE_COLS, 11536);
        assert_eq!(COL_H0, 11536);
        assert_eq!(COL_H_INF, 11537);
        assert_eq!(COL_ALPHA, 11538);
        assert_eq!(COL_IS_LAST, 11539);
        assert_eq!(WIDTH, 11540);
        assert_eq!(NUM_PUBLIC, 0);
    }

    #[test]
    fn bus_name_reused_from_sumcheck() {
        // Same channel as SumcheckVerifierBusAir
        let _ = SC_ROUND;
    }

    #[test]
    fn air_type_checks() {
        let air = Blake3TranscriptAir;
        assert_eq!(BaseAir::<BinaryField128>::width(&air), WIDTH);
        assert_eq!(BaseAir::<BinaryField128>::num_public_values(&air), 0);
    }

    #[test]
    fn bus_wrapper_constructible() {
        let _ = Blake3TranscriptBusAir;
    }
}
