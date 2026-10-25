//! A2.2 — Blake3 binary compression → MultiStarkProof<BinaryPcs>.
//!
//! Iteratively wired: this version constructs Blake3CompressionInput and
//! builds the binary trace; the MultiStarkProof pipeline is added once
//! the exact BinaryPcs types from `binary_grouped_prepared_layer.rs` are
//! reused here.
//!
//! Types referenced (from recursion/tests/binary_grouped_prepared_layer.rs):
//!   - p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs}
//!   - p3_multi_stark::{prove, setup, ProverInstance, ProverInstances}
//!   - p3_test_utils::binary_field_params::blake3 (test-only)

use alloc::vec::Vec;

use p3_binary_field::BinaryField128;
use p3_blake3_air::{
    Blake3BinaryAir, Blake3CompressionInput, generate_binary_trace_rows,
};
use p3_matrix::dense::RowMajorMatrix;

/// Blake3 compression parameters, in the exact shape Blake3CompressionInput
/// requires (u32 limbs, see vendor/p3-blake3-air/src/binary/generation.rs).
pub struct Blake3Params {
    /// 8 u32 limbs = 32-byte chaining value.
    pub chaining_value: [u32; 8],
    /// 16 u32 limbs = 64-byte message block.
    pub block: [u32; 16],
    pub counter: u64,
    pub block_len: u32,
    pub flags: u32,
}

impl Blake3Params {
    /// Convert from raw byte representation used by Sahyadri.
    pub fn from_bytes(
        cv_in: &[u8; 32],
        block: &[u8; 64],
        counter: u64,
        block_len: u32,
        flags: u32,
    ) -> Self {
        Self {
            chaining_value: core::array::from_fn(|i| {
                u32::from_le_bytes(cv_in[4 * i..4 * i + 4].try_into().unwrap())
            }),
            block: core::array::from_fn(|i| {
                u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap())
            }),
            counter,
            block_len,
            flags,
        }
    }

    pub fn to_input(&self) -> Blake3CompressionInput {
        Blake3CompressionInput {
            chaining_value: self.chaining_value,
            block: self.block,
            counter: self.counter,
            block_len: self.block_len,
            flags: self.flags,
        }
    }
}

#[derive(Debug)]
pub enum Blake3MultiStarkError {
    EmptyBatch,
}

/// Build the Blake3 binary trace for a single compression.
///
/// Returns `(trace, num_inputs)` where `trace` is a `RowMajorMatrix<BinaryField128>`
/// with one row per compression. `num_inputs` allows downstream code to
/// size the MultiStarkProof instance layout.
pub fn build_blake3_trace(
    inputs: Vec<Blake3Params>,
) -> Result<(RowMajorMatrix<BinaryField128>, usize), Blake3MultiStarkError> {
    if inputs.is_empty() {
        return Err(Blake3MultiStarkError::EmptyBatch);
    }
    let n = inputs.len();
    let compression_inputs: Vec<Blake3CompressionInput> =
        inputs.into_iter().map(|p| p.to_input()).collect();
    let trace: RowMajorMatrix<BinaryField128> =
        generate_binary_trace_rows(compression_inputs, 0);
    Ok((trace, n))
}

/// Verify the trace dimensions and the AIR's expected width / public counts.
///
/// Sanity check for A2.2 — returns `(height, width, num_public_values)`.
pub fn blake3_trace_shape() -> (usize, usize, usize) {
    let air = Blake3BinaryAir::default();
    let width = <Blake3BinaryAir as p3_air::BaseAir<BinaryField128>>::width(&air);
    let num_public =
        <Blake3BinaryAir as p3_air::BaseAir<BinaryField128>>::num_public_values(&air);
    // height unknown until trace generated; 0 placeholder
    (0, width, num_public)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_matrix::Matrix;

    #[test]
    fn blake3_input_round_trip() {
        let cv = [0x42u8; 32];
        let block = [0x7Fu8; 64];
        let params = Blake3Params::from_bytes(&cv, &block, 0, 64, 0);
        let input = params.to_input();
        assert_eq!(input.block_len, 64);
        assert_eq!(input.counter, 0);
        assert_eq!(input.flags, 0);
    }

    #[test]
    fn blake3_trace_builds() {
        let params = vec![Blake3Params::from_bytes(&[0u8; 32], &[0u8; 64], 0, 64, 0)];
        let (trace, n) = build_blake3_trace(params).unwrap();
        assert_eq!(n, 1);
        assert!(trace.height() >= 1);
        assert!(trace.width() > 0);
        println!(
            "Blake3 binary trace: {} rows x {} cols (width padded for MultiStark)",
            trace.height(),
            trace.width()
        );
    }

    #[test]
    fn air_shape() {
        let (_, width, num_public) = blake3_trace_shape();
        println!("Blake3BinaryAir: width={}, public={}", width, num_public);
        assert!(width > 0);
    }
}
