//! BinaryAggregationAir — Phase T1.1 (2-to-1 FRI aggregation, honest scope).
//!
//! Verifies TWO FRI proofs (via `eval_fri_half` twice) in one AIR, with
//! explicit commitment binding per half.
//!
//! # Layout
//! - cols 0..18   : FRI verifier for proof A
//! - cols 18..36  : FRI verifier for proof B
//!
//! # Public (10)
//! - public[0..4]:  fp_A[0..4]
//! - public[4..8]:  fp_B[0..4]
//! - public[8]:     root_A (Merkle root of proof A's FRI commitment)
//! - public[9]:     root_B
//!
//! # Soundness scope (HONEST — read carefully)
//! - Verifies: FRI fold, final_poly binding, Merkle path, root binding
//!   for BOTH input proofs.
//! - Does NOT verify: inner MultiStark sumcheck or bus balance.
//!   For full adversarial soundness, sumcheck verifier AIR (T1.4) and
//!   bus verifier AIR (T1.5) must be added — ~4-6 weeks extra.
//! - Suitable for: honest-prover testnet, paper-stage demo.
//! - Not suitable for: mainnet production without T1.4+T1.5.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};

use super::binary_verifier_air::{
    eval_fri_half,
    COL_PAIR0, COL_MERKLE_SIB_BASE, COL_MERKLE_PARENT_BASE, MERKLE_DEPTH,
    WIDTH as FRI_HALF_WIDTH,
};

pub const MERKLE_COMPRESS: BusName<'static> = BusName::new("sahyadri_merkle_compress");

pub const AGG_HALF_WIDTH: usize = FRI_HALF_WIDTH; // 18
pub const AGG_WIDTH: usize = AGG_HALF_WIDTH * 2; // 36
pub const AGG_PUBLIC: usize = 10;
pub const ROOT_A_IDX: usize = 8;
pub const ROOT_B_IDX: usize = 9;

pub struct BinaryAggregationAir;

impl<F> BaseAir<F> for BinaryAggregationAir {
    fn width(&self) -> usize { AGG_WIDTH }
    fn num_public_values(&self) -> usize { AGG_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for BinaryAggregationAir {
    fn eval(&self, b: &mut AB) {
        eval_fri_half(b, 0, 0);
        eval_fri_half(b, AGG_HALF_WIDTH, 4);

        // Root binding: each half's merkle_parent[3] == public root
        let (root_a, root_b): (AB::Expr, AB::Expr) = {
            let main = b.main();
            let cur = main.current_slice();
            let ra: AB::Expr = cur[COL_MERKLE_PARENT_BASE + (MERKLE_DEPTH - 1)].into();
            let rb: AB::Expr =
                cur[AGG_HALF_WIDTH + COL_MERKLE_PARENT_BASE + (MERKLE_DEPTH - 1)].into();
            (ra, rb)
        };
        let (exp_a, exp_b): (AB::Expr, AB::Expr) = {
            let public = b.public_values();
            (public[ROOT_A_IDX].into(), public[ROOT_B_IDX].into())
        };
        b.assert_eq(root_a, exp_a);
        b.assert_eq(root_b, exp_b);
    }
}

/// Bus version — 8 Pulls total (4 per half), pairs with 8 Poseidon2b producers.
pub struct BinaryAggregationBusAir;

impl<F> BaseAir<F> for BinaryAggregationBusAir {
    fn width(&self) -> usize { AGG_WIDTH }
    fn num_public_values(&self) -> usize { AGG_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB>
    for BinaryAggregationBusAir
{
    fn eval(&self, b: &mut AB) {
        BinaryAggregationAir.eval(b);

        // 8 Pull tuples: 4 for half A, 4 for half B.
        // Collect first (immutable borrow), then push (mutable borrow).
        let tuples: Vec<(AB::Expr, AB::Expr, AB::Expr)> = {
            let main = b.main();
            let cur = main.current_slice();
            let mut out = Vec::with_capacity(2 * MERKLE_DEPTH);
            for half_off in [0usize, AGG_HALF_WIDTH] {
                for level in 0..MERKLE_DEPTH {
                    let curr: AB::Expr = if level == 0 {
                        cur[half_off + COL_PAIR0].into()
                    } else {
                        cur[half_off + COL_MERKLE_PARENT_BASE + level - 1].into()
                    };
                    let sib: AB::Expr = cur[half_off + COL_MERKLE_SIB_BASE + level].into();
                    let parent: AB::Expr = cur[half_off + COL_MERKLE_PARENT_BASE + level].into();
                    out.push((curr, sib, parent));
                }
            }
            out
        };
        for (curr, sib, parent) in tuples {
            let active = b.is_last_row();
            b.push_bus_interaction(
                MERKLE_COMPRESS,
                BusDirection::Pull,
                [curr, sib, parent],
                BusActivation::Boolean(active),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_constants() {
        assert_eq!(AGG_HALF_WIDTH, 18);
        assert_eq!(AGG_WIDTH, 36);
        assert_eq!(AGG_PUBLIC, 10);
        assert_eq!(ROOT_A_IDX, 8);
        assert_eq!(ROOT_B_IDX, 9);
    }
}
