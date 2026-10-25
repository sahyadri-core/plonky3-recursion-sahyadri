//! A2.3 — Blake3 binary → MultiStarkProof → recursive proof bridge.
//!
//! Discovery summary (A2.3 prep):
//!   - Blake3BinaryAir::width() = 16384 (padded)
//!   - generate_binary_trace_rows() = 11536 (raw)
//!   - MUST pad trace to 16384 before MultiStark prove
//!   - pad_trace_width helper exists in blake3_binary_whir.rs example
//!
//! Pipeline (fill in A2.3c onward):
//!   [Blake3 trace 11536] --pad--> [16384] --MultiStark--> [MultiStarkProof]
//!     --import_native--> [NativeBinaryMultiStarkInput]
//!     --layer.prove--> [RecursionOutput<SC>] ← O(1)


use p3_binary_field::BinaryField128;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

use super::blake3_multi_stark::{build_blake3_trace, Blake3MultiStarkError, Blake3Params};

/// Raw Blake3 binary trace width (vendor constant).
pub const RAW_WIDTH: usize = 11_536;
/// Padded width required by MultiStark (next power of two).
pub const PADDED_WIDTH: usize = 16_384;

#[derive(Debug)]
pub enum Blake3BridgeError {
    NotYetWired(&'static str),
    Trace(Blake3MultiStarkError),
    WidthMismatch { expected: usize, actual: usize },
    Prover(String),
    Verifier(String),
}

/// Pad a Blake3 binary trace from 11,536 to 16,384 columns.
///
/// Extra columns are unconstrained zero padding; the AIR only reads the
/// first `RAW_WIDTH` columns (see blake3_binary_whir.rs PaddedBlake3Air).
pub fn pad_trace_width(
    trace: RowMajorMatrix<BinaryField128>,
    padded_width: usize,
) -> RowMajorMatrix<BinaryField128> {
    let height = trace.height();
    let width = trace.width();
    if width == padded_width {
        return trace;
    }
    assert!(
        padded_width >= width,
        "padded_width ({}) must be >= trace width ({})",
        padded_width,
        width
    );
    let zero = BinaryField128::from_le_bytes([0u8; 16]);
    let mut padded = vec![zero; height * padded_width];
    for r in 0..height {
        for c in 0..width {
            padded[r * padded_width + c] = trace.get(r, c).expect("in bounds");
        }
    }
    RowMajorMatrix::new(padded, padded_width)
}

/// Build, pad, and validate a single Blake3 compression trace.
///
/// Returns the padded trace (16384 columns). A2.3c will feed this into
/// MultiStarkProof::prove once Blake3BinaryConfig types are settled.
pub fn build_padded_blake3_trace(
    cv_in: [u8; 32],
    block: [u8; 64],
) -> Result<RowMajorMatrix<BinaryField128>, Blake3BridgeError> {
    let params = Blake3Params::from_bytes(&cv_in, &block, 0, 64, 0);
    let (trace, n) = build_blake3_trace(vec![params]).map_err(Blake3BridgeError::Trace)?;

    // Validate raw shape before padding.
    if trace.width() != RAW_WIDTH {
        return Err(Blake3BridgeError::WidthMismatch {
            expected: RAW_WIDTH,
            actual: trace.width(),
        });
    }
    if n != 1 {
        return Err(Blake3BridgeError::Prover(format!(
            "expected 1 compression, got {}",
            n
        )));
    }

    Ok(pad_trace_width(trace, PADDED_WIDTH))
}

/// Top-level prove — bridge implementation lands in A2.3c.
pub fn prove_blake3_compression(
    cv_in: [u8; 32],
    block: [u8; 64],
) -> Result<(), Blake3BridgeError> {
    let _padded = build_padded_blake3_trace(cv_in, block)?;
    Err(Blake3BridgeError::NotYetWired(
        "A2.3c: MultiStarkProof::prove with concrete Blake3BinaryConfig",
    ))
}

/// Bridge to recursive config SC — bridge body lands in A2.3d.
pub fn bridge_to_recursive<SC>(
    _proof_bytes: &[u8],
) -> Result<(), Blake3BridgeError>
where
    SC: p3_uni_stark::StarkGenericConfig + Send + Sync + Clone + 'static,
{
    Err(Blake3BridgeError::NotYetWired(
        "A2.3d: import_native + PreparedBinaryGroupedMultiStarkLayer::prove",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pad_trace_11536_to_16384() {
        let params = Blake3Params::from_bytes(&[0u8; 32], &[0u8; 64], 0, 64, 0);
        let (trace, _) = build_blake3_trace(vec![params]).unwrap();
        assert_eq!(trace.width(), RAW_WIDTH);
        assert_eq!(trace.height(), 1);
        let padded = pad_trace_width(trace, PADDED_WIDTH);
        assert_eq!(padded.width(), PADDED_WIDTH);
        assert_eq!(padded.height(), 1);
    }

    #[test]
    fn build_padded_trace_ok() {
        let padded = build_padded_blake3_trace([1u8; 32], [2u8; 64]).unwrap();
        assert_eq!(padded.width(), PADDED_WIDTH);
        assert_eq!(padded.height(), 1);
    }

    #[test]
    fn prove_still_not_yet_wired() {
        let err = prove_blake3_compression([0u8; 32], [0u8; 64]);
        assert!(matches!(err, Err(Blake3BridgeError::NotYetWired(_))));
    }
}
