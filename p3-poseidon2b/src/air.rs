//! Poseidon2b AIR: single-row permutation with full constraints.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;

use crate::params::params128_t4::{MDS_FULL, MDS_PARTIAL, RC, R_F, R_P};
use crate::trace::{
    N_ROUNDS, N_STATES, SBOX_IN_OFFSET, SBOX_OUT_OFFSET, STATE_OFFSET, WIDTH,
};

pub struct Poseidon2bAir;

impl<F> BaseAir<F> for Poseidon2bAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 8 }
}

#[inline]
fn fe(v: u128) -> BinaryField128 {
    // Must match trace.rs semantics — from_le_bytes, NOT from_u32.
    BinaryField128::from_le_bytes(v.to_le_bytes())
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for Poseidon2bAir {
    fn eval(&self, b: &mut AB) {
        let cur: Vec<AB::Expr> = {
            let main = b.main();
            main.current_slice().iter().map(|v| (*v).into()).collect()
        };
        let public: Vec<AB::Expr> =
            b.public_values().iter().map(|v| (*v).into()).collect();

        let state = |r: usize, lane: usize| -> AB::Expr {
            cur[STATE_OFFSET + r * 4 + lane].clone()
        };
        let sbox_in = |r: usize, lane: usize| -> AB::Expr {
            cur[SBOX_IN_OFFSET + r * 4 + lane].clone()
        };
        let sbox_out = |r: usize, lane: usize| -> AB::Expr {
            cur[SBOX_OUT_OFFSET + r * 4 + lane].clone()
        };
        let c = |v: u128| -> AB::Expr { fe(v).into() };

        // Input
        for lane in 0..4 {
            b.assert_eq(state(0, lane), public[lane].clone());
        }

        // Initial MDS
        for i in 0..4 {
            let mut acc: AB::Expr = c(0);
            for j in 0..4 {
                acc = acc + c(MDS_FULL[i][j]) * state(0, j);
            }
            b.assert_eq(state(1, i), acc);
        }

        // 66 rounds
        for r in 0..N_ROUNDS {
            let srow = r + 1;
            let nrow = r + 2;
            let is_full = r < R_F / 2 || r >= R_F / 2 + R_P;

            for lane in 0..4 {
                let rc = if is_full {
                    RC[lane][r]
                } else if lane == 0 {
                    RC[0][r]
                } else {
                    0
                };
                let expected = state(srow, lane) + c(rc);
                b.assert_eq(sbox_in(r, lane), expected);

                if is_full || lane == 0 {
                    let x = sbox_in(r, lane);
                    let x2 = x.clone() * x.clone();
                    let x4 = x2.clone() * x2.clone();
                    let x7 = x4 * x2 * x;
                    b.assert_eq(sbox_out(r, lane), x7);
                } else {
                    b.assert_eq(sbox_out(r, lane), state(srow, lane));
                }
            }

            let mds = if is_full { &MDS_FULL } else { &MDS_PARTIAL };
            for i in 0..4 {
                let mut acc: AB::Expr = c(0);
                for j in 0..4 {
                    acc = acc + c(mds[i][j]) * sbox_out(r, j);
                }
                b.assert_eq(state(nrow, i), acc);
            }
        }

        // Output
        for lane in 0..4 {
            b.assert_eq(state(N_STATES - 1, lane), public[4 + lane].clone());
        }
    }
}
