#![allow(unused_imports)]
// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Ignotus Nemo.

//! Public benchmark statement: a sequence of 59 Poseidon2b permutations.
//!
//! The output state of each permutation is the input state of the next.  This
//! deliberately application-neutral relation is sufficient to compare the
//! product-chain baseline with FROST-GKR without publishing any surrounding
//! protocol.

use alloc::vec::Vec;
use crate::frost_gkr::core::tower::Block128;
use crate::frost_gkr::core::native::permutation::{Poseidon2bPermutation, STATE_SIZE};

/// Number of Poseidon2b permutations used by the paper benchmark.
pub const N_PERMUTATIONS: usize = 59;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SequenceInput {
    pub initial_state: [Block128; STATE_SIZE],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SequenceWitness {
    pub states: Vec<([Block128; STATE_SIZE], [Block128; STATE_SIZE])>,
    pub final_state: [Block128; STATE_SIZE],
}

/// Evaluate the public sequence natively.
pub fn evaluate_sequence(input: &SequenceInput) -> SequenceWitness {
    let permutation = Poseidon2bPermutation;
    let mut current = input.initial_state;
    let mut states = Vec::with_capacity(N_PERMUTATIONS);

    for _ in 0..N_PERMUTATIONS {
        let state_in = current;
        permutation.permute_mut(&mut current);
        states.push((state_in, current));
    }

    SequenceWitness {
        states,
        final_state: current,
    }
}

/// Two-lane public digest used to bind the sequence to the transcript.
pub fn sequence_digest(input: &SequenceInput) -> [Block128; 2] {
    let final_state = evaluate_sequence(input).final_state;
    [final_state[0], final_state[1]]
}

