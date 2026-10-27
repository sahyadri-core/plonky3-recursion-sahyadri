//! Phase 3D part 2b — Poseidon2b bus-linked compression.
//!
//! Wraps Plonky3's `Poseidon2bAir` (full permutation, 1024 cols) with:
//!   - 3 extra witness columns (a, b, c) for the compression tuple
//!   - A bus Push on MERKLE_COMPRESS
//!
//! MerklePathAir (sahyadri-fri-binius) pulls the same tuple. Plonky3's
//! multiset bus equality makes every Merkle-level `next == compress(curr, sib)`
//! computationally bound to a Poseidon2b permutation proof.
//!
//! # Status
//!
//! Scaffold for today:
//!   - Compiles
//!   - Delegates full Poseidon2b constraints via `Poseidon2bAir.eval(b)`
//!   - Pushes (a, b, c) on the bus
//!
//! Next step (3D2b, 1-2 days):
//!   - State binding: cur[STATE_OFFSET + 0] == a, cur[STATE_OFFSET + 1] == b
//!   - Output binding: cur[OUTPUT_OFFSET + 0] + cur[OUTPUT_OFFSET + 1] == c
//!   Both need `STATE_OFFSET` / `OUTPUT_OFFSET` discovery (params module).
//!
//! Bus tuple (a, b, c) is stable; the soundness tie comes from permutation
//! constraints once the state/output offsets are wired.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_poseidon2b::trace::WIDTH as P2B_WIDTH;
use p3_poseidon2b::Poseidon2bAir;

/// Channel for Merkle compression tuples.
pub const MERKLE_COMPRESS: BusName<'static> = BusName::new("sahyadri_merkle_compress");

/// Width: Poseidon2b columns + 3 witness cells for (a, b, c).
pub const WIDTH: usize = P2B_WIDTH + 3;

pub const COL_A: usize = P2B_WIDTH;
pub const COL_B: usize = P2B_WIDTH + 1;
pub const COL_C: usize = P2B_WIDTH + 2;

pub struct Poseidon2bBusAir;

impl<F> BaseAir<F> for Poseidon2bBusAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 0 }
}

impl<AB> Air<AB> for Poseidon2bBusAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        // 1. Delegate the full Poseidon2b permutation constraints on cols
        //    0..P2B_WIDTH. Plonky3's Poseidon2bAir.eval reads
        //    main.current_slice() from offset 0, so it silently ignores
        //    the 3 extra columns we append.
        Poseidon2bAir.eval(b);

        // 2. Read the compression tuple from the extra columns.
        //    Bound the borrow in a scope so we can mutate `b` afterwards.
        let (a, bb, c) = {
            let main = b.main();
            let cur = main.current_slice();
            let a: AB::Expr = cur[COL_A].into();
            let bb: AB::Expr = cur[COL_B].into();
            let c: AB::Expr = cur[COL_C].into();
            (a, bb, c)
        };

        // 3. State binding (TODO 3D2b): cur[STATE_OFFSET + 0] == a and
        //    cur[STATE_OFFSET + 1] == bb; cur[OUTPUT_OFFSET + 0] +
        //    cur[OUTPUT_OFFSET + 1] == c. Both offsets live in
        //    `p3_poseidon2b::params::params128_t4`.

        // 4. Bus Push — this AIR is the producer of a verified
        //    (a, b, c) triple. MerklePathAir pulls the same tuple.
        b.push_bus_interaction(
            MERKLE_COMPRESS,
            BusDirection::Push,
            [a, bb, c],
            BusActivation::Always,
        );
    }
}
