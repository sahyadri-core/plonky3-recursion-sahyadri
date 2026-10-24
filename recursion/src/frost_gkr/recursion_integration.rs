//! p3-recursion integration for FROST-GKR verifier proofs.
//!
//! Currently a type-shape stub for Day 4. Actual prove/verify wiring
//! happens once we confirm p3-recursion's API accepts our sub-proof
//! shapes (Day 4-6 work).

use alloc::vec::Vec;
use p3_uni_stark::{Proof, StarkGenericConfig, Val};

pub struct FrostGkrSubProofs<SC: StarkGenericConfig> {
    pub extraction: Proof<SC>,
    pub pcs_open: Proof<SC>,
    pub sumcheck: Proof<SC>,
}

pub struct SubProofInputs<SC: StarkGenericConfig> {
    pub extraction_public: Vec<Val<SC>>,
    pub pcs_open_public: Vec<Val<SC>>,
    pub sumcheck_public: Vec<Val<SC>>,
}
