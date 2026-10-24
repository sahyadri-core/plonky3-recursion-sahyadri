//! Merkle aggregation over FROST-GKR batch chain commitments.
//!
//! Combines N chain commitments into one Poseidon2b Merkle root.
//! Tree levels are parallelised under the "parallel" feature.

use alloc::vec::Vec;

use crate::frost_gkr::core::field::TowerField;
use crate::frost_gkr::core::native::permutation::{Poseidon2bPermutation, STATE_SIZE};
use crate::frost_gkr::core::tower::Block128;
use crate::frost_gkr::e3_scale::ChainProof;

pub struct AggregatedProof {
    pub leaves: Vec<Block128>,
    pub root: Block128,
    pub n_batches: usize,
}

impl AggregatedProof {
    pub fn build(chain: &ChainProof) -> Self {
        let leaves = chain.batch_commitments.clone();
        let root = merkle_root(&leaves);
        Self { leaves, root, n_batches: chain.n_batches }
    }

    pub fn verify(&self) -> bool {
        if self.leaves.len() != self.n_batches {
            return false;
        }
        merkle_root(&self.leaves) == self.root
    }

    pub fn proof_size_bytes(&self) -> usize {
        self.leaves.len() * 16 + 16
    }
}

#[cfg(feature = "parallel")]
fn compress_level(level: &[Block128]) -> Vec<Block128> {
    use p3_maybe_rayon::prelude::*;
    level
        .par_chunks(2)
        .map(|pair| {
            if pair.len() == 2 {
                compress(pair[0], pair[1])
            } else {
                pair[0]
            }
        })
        .collect()
}

#[cfg(not(feature = "parallel"))]
fn compress_level(level: &[Block128]) -> Vec<Block128> {
    level
        .chunks(2)
        .map(|pair| {
            if pair.len() == 2 {
                compress(pair[0], pair[1])
            } else {
                pair[0]
            }
        })
        .collect()
}

pub fn merkle_root(leaves: &[Block128]) -> Block128 {
    if leaves.is_empty() {
        return Block128::ZERO;
    }
    let mut level: Vec<Block128> = leaves.to_vec();
    while level.len() > 1 {
        level = compress_level(&level);
    }
    level[0]
}

fn compress(a: Block128, b: Block128) -> Block128 {
    let mut state: [Block128; STATE_SIZE] = [a, b, Block128::ZERO, Block128::ZERO];
    Poseidon2bPermutation.permute_mut(&mut state);
    Block128(state[0].0 ^ a.0 ^ b.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frost_gkr::e3_scale::prove_batch_chain;

    #[test]
    fn empty_chain_has_zero_root() {
        assert_eq!(merkle_root(&[]), Block128::ZERO);
    }

    #[test]
    fn single_leaf_root_is_leaf() {
        let leaf = Block128(0x42);
        assert_eq!(merkle_root(&[leaf]), leaf);
    }

    #[test]
    fn two_leaf_root_matches_compress() {
        let a = Block128(1);
        let b = Block128(2);
        assert_eq!(merkle_root(&[a, b]), compress(a, b));
    }

    #[test]
    fn aggregate_and_verify_small_chain() {
        let chain = prove_batch_chain(1, 5);
        let proof = AggregatedProof::build(&chain);
        assert_eq!(proof.n_batches, 5);
        assert_eq!(proof.leaves.len(), 5);
        assert!(proof.verify());
    }

    #[test]
    fn tamper_detection() {
        let chain = prove_batch_chain(1, 5);
        let mut proof = AggregatedProof::build(&chain);
        proof.leaves[2] = proof.leaves[2] + Block128(1);
        assert!(!proof.verify());
    }

    #[test]
    fn batch_count_mismatch_rejected() {
        let chain = prove_batch_chain(1, 3);
        let mut proof = AggregatedProof::build(&chain);
        proof.n_batches = 4;
        assert!(!proof.verify());
    }
}
