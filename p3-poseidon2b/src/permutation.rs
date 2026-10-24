//! Standalone Poseidon2b permutation over GF(2^128).
//!
//! Parameters match Parano1d's production instance:
//!   t=4, x^7 S-box, RF=8 (4+4), RP=58, 66 total rounds.
//!
//! Reference: Poseidon-Hash/Poseidon2b (Apache-2.0), adapted to p3-binary-field.

use p3_binary_field::BinaryField128;
use crate::params::params128_t4::{RC, MDS_FULL, MDS_PARTIAL, STATE_SIZE, R_F, R_P};

const N_ROUNDS: usize = R_F + R_P;

/// Evaluate x^7 using Frobenius structure: x^7 = x * x^2 * x^4.
/// In GF(2^128), squaring is linear, so this is 3 multiplications total.
#[inline]
pub fn sbox_x7(x: BinaryField128) -> BinaryField128 {
    let x2 = x * x;
    let x4 = x2 * x2;
    x * x2 * x4
}

/// Apply a 4×4 MDS matrix to the state.
#[inline]
fn mds_mul(state: &[BinaryField128; STATE_SIZE], matrix: &[[u128; STATE_SIZE]; STATE_SIZE]) -> [BinaryField128; STATE_SIZE] {
    let mut out = [BinaryField128::from_le_bytes([0u8; 16]); STATE_SIZE];
    for i in 0..STATE_SIZE {
        let mut acc = BinaryField128::from_le_bytes([0u8; 16]);
        for j in 0..STATE_SIZE {
            let m = u128_to_field(matrix[i][j]);
            acc += m * state[j];
        }
        out[i] = acc;
    }
    out
}

#[inline]
fn u128_to_field(v: u128) -> BinaryField128 {
    BinaryField128::from_le_bytes(v.to_le_bytes())
}

/// Poseidon2b permutation: 4-element state, 66 rounds, x^7 S-box.
pub fn poseidon2b_permutation(state: &mut [BinaryField128; STATE_SIZE]) {
    // Initial MDS (full)
    *state = mds_mul(state, &MDS_FULL);

    for r in 0..N_ROUNDS {
        let is_full = r < R_F / 2 || r >= R_F / 2 + R_P;
        if is_full {
            // Full round: RC add + x^7 on all lanes + MDS_FULL
            for i in 0..STATE_SIZE {
                state[i] += u128_to_field(RC[i][r]);
                state[i] = sbox_x7(state[i]);
            }
            *state = mds_mul(state, &MDS_FULL);
        } else {
            // Partial round: RC on lane 0 + x^7 on lane 0 + MDS_PARTIAL
            state[0] += u128_to_field(RC[0][r]);
            state[0] = sbox_x7(state[0]);
            *state = mds_mul(state, &MDS_PARTIAL);
        }
    }
}
