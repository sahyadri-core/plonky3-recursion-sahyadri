//! SahyadriX PoW AIR — hybrid Poseidon2b final hash + Blake3 memory fill.
//!
//! Paper PoW: Poseidon2(ML_16MB(Blake3(h||n))) < T
//!
//! This module provides the Poseidon2b final-hash sub-proof. The Blake3
//! memory-fill sub-proof is aggregated at the chain-proof layer.

use alloc::vec;
use alloc::vec::Vec;

use p3_binary_field::BinaryField128;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_poseidon2b::generate_poseidon2b_trace;
use p3_poseidon2b::trace::{N_STATES, STATE_OFFSET};

type F = BinaryField128;

pub struct Poseidon2bFinalHash {
    pub public: Vec<F>,    // input || output (8 elements)
    pub trace: RowMajorMatrix<F>,
}

pub fn build_poseidon2b_final_hash(input: [F; 4]) -> Poseidon2bFinalHash {
    let trace = generate_poseidon2b_trace(input);

    // Copy output values out before moving `trace` into the struct.
    let mut output = [F::from_le_bytes([0u8; 16]); 4];
    {
        let row = trace.row_slice(0).expect("trace has row 0");
        let off = STATE_OFFSET + (N_STATES - 1) * 4;
        for i in 0..4 {
            output[i] = row[off + i];
        }
    }

    let mut public = vec![F::from_le_bytes([0u8; 16]); 8];
    for i in 0..4 {
        public[i] = input[i];
        public[4 + i] = output[i];
    }

    Poseidon2bFinalHash { public, trace }
}
