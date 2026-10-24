//! Poseidon2b trace generation: single row, all 66 rounds expanded to columns.

use p3_binary_field::BinaryField128;
use p3_matrix::dense::RowMajorMatrix;

use crate::params::params128_t4::{MDS_FULL, MDS_PARTIAL, RC, R_F, R_P};

pub const N_ROUNDS: usize = R_F + R_P; // 66
pub const N_STATES: usize = N_ROUNDS + 2; // input + MDS + 66 rounds = 68

pub const STATE_OFFSET: usize = 0;
pub const SBOX_IN_OFFSET: usize = N_STATES * 4;             // 272
pub const SBOX_OUT_OFFSET: usize = SBOX_IN_OFFSET + N_ROUNDS * 4; // 536

pub const ACTIVE_WIDTH: usize = SBOX_OUT_OFFSET + N_ROUNDS * 4;   // 800
pub const WIDTH: usize = 1024; // padded to power-of-two

#[inline]
fn fe(v: u128) -> BinaryField128 {
    BinaryField128::from_le_bytes(v.to_le_bytes())
}

pub fn generate_poseidon2b_trace(input: [BinaryField128; 4]) -> RowMajorMatrix<BinaryField128> {
    let mut values = vec![BinaryField128::from_le_bytes([0u8; 16]); WIDTH];
    let mut state = input;

    // Row 0: input
    for i in 0..4 {
        values[STATE_OFFSET + i] = state[i];
    }

    // Initial MDS -> row 1
    let mut next = [BinaryField128::from_le_bytes([0u8; 16]); 4];
    for i in 0..4 {
        let mut acc = BinaryField128::from_le_bytes([0u8; 16]);
        for j in 0..4 {
            acc += fe(MDS_FULL[i][j]) * state[j];
        }
        next[i] = acc;
    }
    state = next;
    for i in 0..4 {
        values[STATE_OFFSET + 4 + i] = state[i];
    }

    // 66 rounds
    for r in 0..N_ROUNDS {
        let next_row = r + 2;
        let is_full = r < R_F / 2 || r >= R_F / 2 + R_P;

        for lane in 0..4 {
            let rc = if is_full {
                RC[lane][r]
            } else if lane == 0 {
                RC[0][r]
            } else {
                0
            };
            let s_in = state[lane] + fe(rc);
            values[SBOX_IN_OFFSET + r * 4 + lane] = s_in;

            let s_out = if is_full || lane == 0 {
                let x2 = s_in * s_in;
                let x4 = x2 * x2;
                x4 * x2 * s_in
            } else {
                state[lane]
            };
            values[SBOX_OUT_OFFSET + r * 4 + lane] = s_out;
        }

        let mds = if is_full { &MDS_FULL } else { &MDS_PARTIAL };
        let mut next = [BinaryField128::from_le_bytes([0u8; 16]); 4];
        for i in 0..4 {
            let mut acc = BinaryField128::from_le_bytes([0u8; 16]);
            for j in 0..4 {
                acc += fe(mds[i][j]) * values[SBOX_OUT_OFFSET + r * 4 + j];
            }
            next[i] = acc;
        }
        state = next;
        for i in 0..4 {
            values[STATE_OFFSET + next_row * 4 + i] = state[i];
        }
    }

    RowMajorMatrix::new(values, WIDTH)
}
