//! Poseidon2b sponge over GF(2^128) with rate=2, capacity=2.
//!
//! Absorbs arbitrary bytes (padded to rate boundary), squeezes 32 bytes (2 field elements).
//! Domain separation via a capacity tag.

use p3_binary_field::{BinaryField128, TowerLevel};
use crate::permutation::poseidon2b_permutation;

const RATE: usize = 2;
const CAPACITY: usize = 2;
const STATE_SIZE: usize = RATE + CAPACITY;

/// Hash arbitrary bytes to a 32-byte digest using Poseidon2b sponge.
pub fn poseidon2b_hash(input: &[u8]) -> [u8; 32] {
    let mut state = [BinaryField128::from_le_bytes([0u8; 16]); STATE_SIZE];
    // Domain tag in capacity
    state[RATE] = BinaryField128::from_le_bytes([1u8; 16]);

    // Absorb: process input in 32-byte chunks (2 × 16 bytes)
    let mut chunks = input.chunks_exact(32);
    for chunk in &mut chunks {
        for i in 0..RATE {
            state[i] += BinaryField128::from_le_bytes(chunk[i*16..(i+1)*16].try_into().unwrap());
        }
        poseidon2b_permutation(&mut state);
    }
    let rem = chunks.remainder();
    if !rem.is_empty() {
        for i in 0..RATE {
            let start = i * 16;
            if start < rem.len() {
                let end = (start + 16).min(rem.len());
                let mut buf = [0u8; 16];
                buf[..end-start].copy_from_slice(&rem[start..end]);
                state[i] += BinaryField128::from_le_bytes(buf);
            }
        }
        poseidon2b_permutation(&mut state);
    }

    // Squeeze 2 field elements = 32 bytes
    let mut out = [0u8; 32];
    for i in 0..RATE {
        out[i*16..(i+1)*16].copy_from_slice(&state[i].to_repr().to_le_bytes());
    }
    out
}
