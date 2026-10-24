//! Poseidon2b over GF(2^128): permutation + sponge + AIR + trace.
//! Parameters: t=4, x^7, RF=8, RP=58, rate=2, capacity=2.

pub mod params;
pub mod permutation;
pub mod sponge;
pub mod trace;
pub mod air;

pub use air::Poseidon2bAir;
pub use permutation::poseidon2b_permutation;
pub use sponge::poseidon2b_hash;
pub use trace::generate_poseidon2b_trace;

