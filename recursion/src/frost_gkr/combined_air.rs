//! CombinedAir — enum wrapper for heterogeneous AIRs in MultiStark.
//!
//! Plonky3's MultiStark takes `&[&A]` with a single A type, so we wrap
//! Poseidon2bBusAir (width 1024) and MerklePathBusAir (width 4) in one enum.
//!
//! # Width padding
//!
//! Both variants report `width() = 1024`. The MerklePath trace is padded
//! with 1020 zero columns. `MerklePathAir::eval` only reads cols 0..3, so
//! the padding columns are unreferenced and unconstrained — valid.
//!
//! # Public input padding
//!
//! Both variants report `num_public_values() = 8`. The MerklePath public
//! is `[root, 0, 0, 0, 0, 0, 0, 0]` — root in [0], padding in [1..8].
//! `MerklePathAir::eval` reads `public[0]` only.
//!
//! # Why not split into two MultiStarks
//!
//! Bus multiset equality is enforced within a *single* MultiStark proof.
//! Two separate proofs cannot share a bus channel. So both AIR types must
//! live in one MultiStark, which forces the enum wrapper.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_bus::BusInteractionBuilder;

use sahyadri_fri_binius::merkle_path_bus_air::MerklePathBusAir;
use super::poseidon2b_bus_air::Poseidon2bBusAir;

/// Combined width = Poseidon2bAir's width (1024).
/// MerklePath traces are padded to this width.
pub const COMBINED_WIDTH: usize = 1024;

/// Combined public input count = Poseidon2bAir's (8).
/// MerklePath public arrays are padded to this count.
pub const COMBINED_PUBLIC: usize = 8;

/// Depth of the Merkle tree the path AIR handles.
pub const MERKLE_DEPTH: usize = 4;

#[derive(Clone, Copy)]
pub enum CombinedAir {
    Poseidon2b,
    MerklePath,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize {
        COMBINED_WIDTH
    }
    fn num_public_values(&self) -> usize {
        COMBINED_PUBLIC
    }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::Poseidon2b => Poseidon2bBusAir.eval(b),
            Self::MerklePath => MerklePathBusAir { depth: MERKLE_DEPTH }.eval(b),
        }
    }
}
