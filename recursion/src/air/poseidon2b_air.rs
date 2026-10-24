//! Poseidon2b AIR: single permutation over GF(2^128), t=4, x^7, RF=8 (4+4), RP=58.
//!
//! Single-row computation (all 66 rounds + initial MDS in one row).
//! Column layout:
//!   state[0..272]:  68 states (initial + 66 rounds + final) × 4 lanes
//!   sbox_in[0..264]: 66 rounds × 4 lanes
//!   sbox_out[0..264]: 66 rounds × 4 lanes
//!   padding[0..224]: zero
//! Total: 1024 columns, 1 row.
//!
//! AirBuilder gives us the "row" as the full column vector, so single-row works.
//! Prove with p3-uni-stark (FRI over binary field, "groundwork only" path).

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_poseidon2b::params::params128_t4::{MDS_FULL, MDS_PARTIAL, RC, R_F, R_P};

const N_ROUNDS: usize = R_F + R_P; // 66
const N_STATES: usize = N_ROUNDS + 2; // input + initial MDS + 66 rounds = 68

const STATE_OFFSET: usize = 0;
const SBOX_IN_OFFSET: usize = N_STATES * 4; // 272
const SBOX_OUT_OFFSET: usize = SBOX_IN_OFFSET + N_ROUNDS * 4; // 536

const WIDTH: usize = 1024;

pub struct Poseidon2bAir;

impl<F> BaseAir<F> for Poseidon2bAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 8 } // 4 input + 4 output
}

#[inline]
fn fe<AB: AirBuilder>(v: u128) -> AB::Expr {
    use p3_field::PrimeCharacteristicRing;
    let f = <AB::F as PrimeCharacteristicRing>::from_u128(v);
    f.into()
}

impl<AB: AirBuilder> Air<AB> for Poseidon2bAir {
    fn eval(&self, b: &mut AB) {
        let cur = b.main().current_slice();
        let public = b.public_values();

        let state = |r: usize, lane: usize| -> AB::Expr {
            cur[STATE_OFFSET + r * 4 + lane].into()
        };
        let sbox_in = |r: usize, lane: usize| -> AB::Expr {
            cur[SBOX_IN_OFFSET + r * 4 + lane].into()
        };
        let sbox_out = |r: usize, lane: usize| -> AB::Expr {
            cur[SBOX_OUT_OFFSET + r * 4 + lane].into()
        };

        // ---- Input constraint ----
        for lane in 0..4 {
            b.assert_eq(state(0, lane), public[lane].into());
        }

        // ---- Initial MDS ----
        for i in 0..4 {
            let mut acc = AB::Expr::ZERO;
            for j in 0..4 {
                acc = acc + fe::<AB>(MDS_FULL[i][j]) * state(0, j);
            }
            b.assert_eq(state(1, i), acc);
        }

        // ---- 66 rounds ----
        for r in 0..N_ROUNDS {
            let state_row = r + 1;
            let next_state_row = r + 2;
            let is_full = r < R_F / 2 || r >= R_F / 2 + R_P;

            for lane in 0..4 {
                let rc = if is_full {
                    RC[lane][r]
                } else if lane == 0 {
                    RC[0][r]
                } else {
                    0
                };

                let expected = state(state_row, lane) + fe::<AB>(rc);
                b.assert_eq(sbox_in(r, lane), expected);

                if is_full || lane == 0 {
                    let x = sbox_in(r, lane);
                    let x2 = x.clone() * x.clone();
                    let x4 = x2.clone() * x2.clone();
                    let x7 = x4 * x2 * x;
                    b.assert_eq(sbox_out(r, lane), x7);
                } else {
                    b.assert_eq(sbox_out(r, lane), state(state_row, lane));
                }
            }

            let mds = if is_full { &MDS_FULL } else { &MDS_PARTIAL };
            for i in 0..4 {
                let mut acc = AB::Expr::ZERO;
                for j in 0..4 {
                    acc = acc + fe::<AB>(mds[i][j]) * sbox_out(r, j);
                }
                b.assert_eq(state(next_state_row, i), acc);
            }
        }

        // ---- Output constraint ----
        for lane in 0..4 {
            b.assert_eq(state(N_STATES - 1, lane), public[4 + lane].into());
        }
    }
}
