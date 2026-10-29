//! SpongePermuteBusAir - Phase T1.4b.2b.1 (producer side).
//!
//! Proves a FULL 4-limb Poseidon2b permutation, then Pushes
//! `(s[0..4], ns[0..4])` on the `SC_SPONGE_PERMUTE` bus.
//!
//! Producer for `TranscriptAIR` (T1.4b.2b.2 consumer): links consecutive
//! sponge states during absorb/sample, binding Fiat-Shamir alpha to
//! actual Poseidon2b sponge outputs.
//!
//! # Design (vs 3D2b `Poseidon2bBusAir`)
//!
//! - 3D2b: Pushes `(a, b, a+b_out)` for Merkle compression (3-tuple)
//! - This: Pushes `(s[0..4], ns[0..4])` for full permutation (8-tuple)
//! - Both delegate to `Poseidon2bAir.eval` for 1024-col permutation
//! - Different bus channel, same underlying AIR
//!
//! # Layout (WIDTH = 1032)
//!
//! - 0..1024:   Poseidon2b full trace (delegated)
//! - 1024..1028: input state s[0..4]  (bound to trace row 0, cols 0..4)
//! - 1028..1032: output state ns[0..4] (bound to trace at P2B_OUTPUT_OFFSET)
//!
//! # Trace rows
//!
//! Same 68-row Poseidon2b trace as 3D2b. Extra 8 cols hold input on row 0
//! and output on last row. Only last row Pushes (is_last_row activation).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_field::PrimeCharacteristicRing;
use p3_poseidon2b::air::Poseidon2bAir;
use p3_poseidon2b::trace::WIDTH as P2B_WIDTH;

/// Bus channel: SpongePermuteBusAir Push -> TranscriptAIR Pull.
/// Tuple: (s0, s1, s2, s3, ns0, ns1, ns2, ns3) - 8 limbs.
pub const SC_SPONGE_PERMUTE: BusName<'static> = BusName::new("sahyadri_sponge_permute");

pub const EXTRA_COLS: usize = 8;
pub const WIDTH: usize = P2B_WIDTH + EXTRA_COLS;

/// Poseidon2b input state offset (confirmed STATE_OFFSET=0 from discovery).
pub const P2B_INPUT_OFFSET: usize = 0;

/// Poseidon2b output state offset.
///
/// ADJUST after discovery: check 3D2b `Poseidon2bBusAir` for how it reads
/// output state, or `generate_poseidon2b_trace` last-write pattern.
/// Likely candidates:
///   - `(N_STATES - 1) * 4` = 67 * 4 = 268  (last row, final state)
///   - `N_ROUNDS * 4` = 66 * 4 = 264 (if last row has metadata)
///   - custom OUTPUT_OFFSET if declared
pub const P2B_OUTPUT_OFFSET: usize = 268; // PLACEHOLDER - adjust post-discovery

pub const COL_INPUT_BASE: usize = P2B_WIDTH;
pub const COL_OUTPUT_BASE: usize = P2B_WIDTH + 4;

pub struct SpongePermuteBusAir;

impl<F> BaseAir<F> for SpongePermuteBusAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 0 }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB>
    for SpongePermuteBusAir
{
    fn eval(&self, b: &mut AB) {
        Poseidon2bAir.eval(b);

        // Bind input state (row 0, cols 0..4) to extra cols 1024..1028.
        let is_first = b.is_first_row();
        for i in 0..4 {
            let (extra_col, trace_col): (AB::Expr, AB::Expr) = {
                let main = b.main();
                let cur = main.current_slice();
                (
                    cur[COL_INPUT_BASE + i].into(),
                    cur[P2B_INPUT_OFFSET + i].into(),
                )
            };
            b.assert_eq(is_first.clone() * (extra_col + trace_col), AB::F::ZERO);
        }

        // Bind output state (last row, cols P2B_OUTPUT_OFFSET..+4) to extra cols 1028..1032.
        let is_last = b.is_last_row();
        for i in 0..4 {
            let (extra_col, trace_col): (AB::Expr, AB::Expr) = {
                let main = b.main();
                let cur = main.current_slice();
                (
                    cur[COL_OUTPUT_BASE + i].into(),
                    cur[P2B_OUTPUT_OFFSET + i].into(),
                )
            };
            b.assert_eq(is_last.clone() * (extra_col + trace_col), AB::F::ZERO);
        }

        // Push (s[0..4], ns[0..4]) on last row only.
        let (s, ns): ([AB::Expr; 4], [AB::Expr; 4]) = {
            let main = b.main();
            let cur = main.current_slice();
            let s: [AB::Expr; 4] = [
                cur[COL_INPUT_BASE + 0].into(),
                cur[COL_INPUT_BASE + 1].into(),
                cur[COL_INPUT_BASE + 2].into(),
                cur[COL_INPUT_BASE + 3].into(),
            ];
            let ns: [AB::Expr; 4] = [
                cur[COL_OUTPUT_BASE + 0].into(),
                cur[COL_OUTPUT_BASE + 1].into(),
                cur[COL_OUTPUT_BASE + 2].into(),
                cur[COL_OUTPUT_BASE + 3].into(),
            ];
            (s, ns)
        };

        let active = b.is_last_row();
        b.push_bus_interaction(
            SC_SPONGE_PERMUTE,
            BusDirection::Push,
            [
                s[0].clone(), s[1].clone(), s[2].clone(), s[3].clone(),
                ns[0].clone(), ns[1].clone(), ns[2].clone(), ns[3].clone(),
            ],
            BusActivation::Boolean(active),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_constants() {
        assert_eq!(EXTRA_COLS, 8);
        assert_eq!(COL_INPUT_BASE, P2B_WIDTH);
        assert_eq!(COL_OUTPUT_BASE, P2B_WIDTH + 4);
        assert_eq!(WIDTH, P2B_WIDTH + 8);
    }

    #[test]
    fn bus_name_constructible() {
        let _ = SC_SPONGE_PERMUTE;
    }

    #[test]
    fn offsets_are_reasonable() {
        assert!(P2B_INPUT_OFFSET < P2B_OUTPUT_OFFSET);
        assert!(P2B_OUTPUT_OFFSET + 4 <= P2B_WIDTH);
    }

    #[test]
    fn air_type_checks() {
        let air = SpongePermuteBusAir;
        assert_eq!(BaseAir::<BinaryField128>::width(&air), WIDTH);
        assert_eq!(BaseAir::<BinaryField128>::num_public_values(&air), 0);
    }
}
