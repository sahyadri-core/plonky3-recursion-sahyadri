//! Poseidon2bBusAir — Phase 3D part 2b (scaffold).
//!
//! Wraps `Poseidon2bAir` with bus send/receive so Merkle-path AIRs can call
//! compression via a permutation argument.
//!
//! DESIGN
//!
//! The existing `Poseidon2bAir` (in `p3-poseidon2b`) is a full permutation
//! witness AIR: it declares ~330 columns, most of which carry intermediate
//! round state. Wrapping it directly means a Merkle path of depth 5 emits
//! 5 × 330 = 1650 trace cells per query.
//!
//! Alternative design (this file): a **compression-only AIR** that carries
//! exactly `(a, b, c)` where `c = poseidon2b_compress(a, b)`. Width = 3.
//! The prover is trusted to compute `c` correctly; soundness comes from
//! the bus linking to the full `Poseidon2bAir` which proves every accepted
//! `(a, b) → c` triple.
//!
//! The two AIRs are bus-connected:
//!
//!   Poseidon2bCompressAir  -- send (a, b, c)
//!   Poseidon2bAir (+wrapper) -- receive (a, b) and send c = compress(a, b)
//!
//! Bus balance ensures every Merkle-level compression is validated.
//!
//! STATUS
//!
//! The MerklePathAir side already exists in `sahyadri-fri-binius`
//! (`MerklePathAir` with `curr, sib, next, sel`). This file stubs the
//! compression side because `Poseidon2bAir` is not bus-aware out of the box.
//! Two options to complete:
//!
//!   Option A: wrap `Poseidon2bAir` with a bus decorator (pure Rust, no
//!             p3-poseidon2b fork needed) — 2-3 days
//!   Option B: extend `p3-poseidon2b/src/air.rs` to add
//!             `impl<AB: AirBuilder + BusInteractionBuilder> Air<AB>` — 1-2 days
//!
//! Until either lands, the current FriVerifierAirV2 is structurally sound
//! (fold math, root pin, final_poly binding) but does not authenticate
//! the Merkle path in-circuit. The MitM-relevant difference is: a prover
//! could fabricate `pair0, pair1` freely as long as the fold equation holds.
//! For a real FRI proof this requires computing a valid codeword, which is
//! cryptographically expensive even without the commitment binding — so the
//! practical risk is bounded by the FRI code's own hardness.

#![allow(dead_code)]

/// A compression row: `c == poseidon2b_compress(a, b)`.
///
/// This AIR is intentionally not implemented here — see STATUS above. The
/// types and column layout are stabilised so downstream code (bus wiring,
/// trace builders, tests) can be written against them.
pub const COL_A: usize = 0;
pub const COL_B: usize = 1;
pub const COL_C: usize = 2;
pub const WIDTH: usize = 3;

pub struct Poseidon2bCompressAir;

impl<F> p3_air::BaseAir<F> for Poseidon2bCompressAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 0 }
}

// Air impl pending Option A or B (see STATUS). When ready:
//
//   impl<AB: AirBuilder + BusInteractionBuilder> Air<AB> for Poseidon2bCompressAir {
//       fn eval(&self, b: &mut AB) {
//           let cur = ...;
//           // bus receive (a, b) from MerklePathAir
//           b.push_bus_interaction(BusDirection::Receive, bus, ...);
//           // bus send c to MerklePathAir's "next" cell
//           b.push_bus_interaction(BusDirection::Send, bus, ...);
//           // the c value must equal what Poseidon2bAir produces;
//           // Poseidon2bAir's own rows satisfy this via permutation argument.
//       }
//   }
