// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Ignotus Nemo.

//! Unified 15-variable MLE layout for FROST-GKR.
//!
//! Instead of one 9-variable MLE per permutation (the product-chain
//! baseline), FROST-GKR represents all 59 permutations as four side-by-side
//! MLEs on a single hypercube of
//! `2^15 = 32 768` cells:
//!
//! | MLE       | Meaning per cell `(slot, round, elem)`                       |
//! |-----------|---------------------------------------------------------------|
//! | `s_in`    | S-box input  = `sin[round][elem]` from the witness            |
//! | `s_out`   | S-box output = `sout[round][elem]` from the witness           |
//! | `sigma`   | 1 if the S-box is active on this cell, else 0                 |
//! | `state`   | Round-entry state = `state[round][elem]` from the witness     |
//!
//! Bit layout (15 bits, low → high): `elem:2 | round:7 | slot:6`.
//! `(slot, round, elem)` lives at index
//! `(slot << (N_ROUND_VARS + N_LANE_VARS))
//!  | (round << N_LANE_VARS)
//!  | elem`.
//!
//! Topology (matches `frost_gkr_poseidon2b` natively):
//!   - Rounds 0..3 and 62..65 are **full** — every elem is active in `σ`.
//!   - Rounds 4..61 are **partial** — only `elem == 0` is active in `σ`.
//!   - `state[round]` exists for `round ∈ 0..=N_ROUNDS` (67 rows). Row
//!     `0` is the post-initial-MDS state; row `N_ROUNDS = 66` is the
//!     permutation output. The 7-bit round axis covers indices 0..127;
//!     rounds 67..127 are zero-padded.
//!   - `s_in` / `s_out` exist for `round ∈ 0..N_ROUNDS`; row `N_ROUNDS`
//!     and rounds 67..127 are zero by convention.
//!   - Slots `N_PERMUTATIONS..64` are zero-padded.
//!
//! Identities discharged by the degree-nine unified sumcheck after the change
//! of variable `y = inc_round(x)`:
//!
//! ```text
//!   C1 (deg 7 in s_in):
//!       σ(x)·(s_out(x) + s_in(x)^7) + (1+σ(x))·(s_out(x) + s_in(x)) = 0
//!
//!   C1' (deg 2, "RC tie"): for every active cell, the witness obeys
//!       σ(x)·(s_in(x) + state(x) + RC(x)) = 0
//!     where RC(x) is the round-constant table indexed at `x` itself.
//!
//!   C2 (deg 2, "MDS shift"): the next-round state is the MDS image
//!     of the previous row's S-box output (full rounds) or of a mixed
//!     row (partial rounds, lanes 1..3 pass `state` through):
//!         state(y)_e + Σ_j  M_{kind(dec(y))}[e][j] · π(dec(y) | e=j) = 0
//!     where π is the multilinear lookup
//!         π(x | e=j) = s_out(x | e=j) + (1 - σ(x | e=j)) · state(x | e=j).
//!     On full rounds σ ≡ 1 so π = s_out; on partial rounds σ(j=0)=1
//!     so π = s_out at lane 0 and π = state at lanes 1..3 (the witness
//!     pins `s_out=0` there).
//! ```
//!
//! Inactive cells (`σ = 0`) trivialise C1 (both branches collapse to
//! `s_out + s_in = 0` with both pinned to zero) and C1' (`σ = 0`
//! kills the constraint). Padded cells (slot ≥ N_PERMUTATIONS or
//! round ≥ N_ROUNDS) have every MLE zero so all three identities hold
//! trivially. C2 is masked at the sumcheck level by the public mask
//! `μ(dec(y)) = 1[slot(dec(y)) < N_PERMUTATIONS ∧ round(dec(y)) < N_ROUNDS]`.

use alloc::vec;
use alloc::vec::Vec;
use crate::frost_gkr::core::tower::Block128;
use crate::frost_gkr::core::TowerField;
use crate::frost_gkr::core::native::permutation::{F_ROUNDS, N_ROUNDS, P_ROUNDS, STATE_SIZE};

use crate::frost_gkr::layers::{evaluate_permutation, PermLayerWitness, RoundKind};
use crate::frost_gkr::sequence::N_PERMUTATIONS;

/// `log2(64) = 6` slot variables.
pub const N_SLOT_VARS: usize = 6;
/// `log2(128) = 7` round variables (covers `N_ROUNDS = 66` with padding).
pub const N_ROUND_VARS: usize = 7;
/// `log2(4) = 2` element-within-state variables.
pub const N_LANE_VARS: usize = 2;
/// Total variable count of the unified MLE.
pub const N_UNIFIED_VARS: usize = N_SLOT_VARS + N_ROUND_VARS + N_LANE_VARS;
/// `2^15 = 32 768` cells.
pub const N_UNIFIED_CELLS: usize = 1 << N_UNIFIED_VARS;

/// Padding helpers — compile-time assertions on topology.
const _: () = assert!(N_ROUNDS == 66);
const _: () = assert!(STATE_SIZE == 4);
const _: () = assert!(N_PERMUTATIONS <= (1 << N_SLOT_VARS));
const _: () = assert!(N_ROUNDS <= (1 << N_ROUND_VARS));
const _: () = assert!(STATE_SIZE <= (1 << N_LANE_VARS));

#[derive(Debug, Clone)]
pub struct UnifiedMle {
    pub s_in: Vec<Block128>,
    pub s_out: Vec<Block128>,
    pub sigma: Vec<Block128>,
    /// Round-entry state. `state[(slot, 0, elem)]` is the
    /// post-initial-MDS state lane; `state[(slot, N_ROUNDS, elem)]`
    /// is the permutation output lane. Rounds `> N_ROUNDS` and
    /// padded slots are zero.
    pub state: Vec<Block128>,
}

impl UnifiedMle {
    /// Empty (all-zero) MLE — useful as a starting buffer before
    /// `populate_slot`.
    pub fn zero() -> Self {
        Self {
            s_in: vec![Block128::ZERO; N_UNIFIED_CELLS],
            s_out: vec![Block128::ZERO; N_UNIFIED_CELLS],
            sigma: vec![Block128::ZERO; N_UNIFIED_CELLS],
            state: vec![Block128::ZERO; N_UNIFIED_CELLS],
        }
    }

    #[inline]
    pub fn index(slot: usize, round: usize, elem: usize) -> usize {
        debug_assert!(slot < 1 << N_SLOT_VARS);
        debug_assert!(round < 1 << N_ROUND_VARS);
        debug_assert!(elem < 1 << N_LANE_VARS);
        (slot << (N_ROUND_VARS + N_LANE_VARS)) | (round << N_LANE_VARS) | elem
    }

    /// Fill in one slot's cells from an instrumented `PermLayerWitness`.
    /// `slot` must satisfy `slot < N_PERMUTATIONS`.
    pub fn populate_slot(&mut self, slot: usize, witness: &PermLayerWitness) {
        assert!(slot < N_PERMUTATIONS, "slot out of range");
        // `s_in`, `s_out`, `σ` live for `r ∈ 0..N_ROUNDS`.
        for r in 0..N_ROUNDS {
            let active_mask = match witness.kind[r] {
                RoundKind::Full => [true; STATE_SIZE],
                RoundKind::Partial => {
                    let mut m = [false; STATE_SIZE];
                    m[0] = true;
                    m
                }
            };
            for elem in 0..STATE_SIZE {
                let idx = Self::index(slot, r, elem);
                // `sin`/`sout` already obey the partial-round zeroing
                // convention (lanes 1..3 are pinned to zero by
                // `evaluate_permutation`). Copy them straight in.
                self.s_in[idx] = witness.sin[r][elem];
                self.s_out[idx] = witness.sout[r][elem];
                self.sigma[idx] = if active_mask[elem] {
                    Block128::ONE
                } else {
                    Block128::ZERO
                };
            }
        }
        // `state` lives for `r ∈ 0..=N_ROUNDS` (rows 0..67 inclusive
        // of the witness). Row 0 is the post-initial-MDS state,
        // row N_ROUNDS is the permutation output.
        debug_assert_eq!(witness.state.len(), N_ROUNDS + 1);
        for r in 0..=N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = Self::index(slot, r, elem);
                self.state[idx] = witness.state[r][elem];
            }
        }
    }

    /// Local consistency check: every cell satisfies all three
    /// FROST-GKR identities (`C1`, `C1'`, `C2`). Used by debug paths
    /// and differential tests.
    pub fn debug_check_identity(&self) {
        use crate::frost_gkr::shift::{build_mu_table, build_rc_table, dec_round_index, mds_coeff, round_of};
        use crate::frost_gkr::core::packed::pow7::pow7_block128;

        let rc = build_rc_table();
        let mu = build_mu_table();

        for idx in 0..N_UNIFIED_CELLS {
            let sin = self.s_in[idx];
            let sout = self.s_out[idx];
            let sigma = self.sigma[idx];
            let state = self.state[idx];
            let rcv = rc[idx];

            // C1: σ·(sout + sin^7) + (1+σ)·(sout + sin) == 0.
            let active = sout + pow7_block128(sin);
            let identity = sout + sin;
            let c1 = sigma * active + (Block128::ONE + sigma) * identity;
            assert_eq!(c1, Block128::ZERO, "C1 violated at idx {idx}");

            // C1': σ · (sin + state + RC) == 0.
            let c1p = sigma * (sin + state + rcv);
            assert_eq!(c1p, Block128::ZERO, "C1' violated at idx {idx}");
        }

        // C2 (MDS shift): for every y where μ(dec(y)) == 1, we must
        // have state(y) + Σ_j M_{kind(dec(y))}[e][j] · π(dec(y) | e=j) = 0,
        // where π = s_out + (1-σ)·state.
        for idx_y in 0..N_UNIFIED_CELLS {
            let dec = dec_round_index(idx_y as u16) as usize;
            if mu[dec] == Block128::ZERO {
                continue;
            }
            let r = round_of(dec as u16);
            // Build π lookups for all four lanes at `dec` with that
            // lane substituted in.
            let pi: [Block128; STATE_SIZE] = core::array::from_fn(|j| {
                let dec_with_j = (dec & !0b11) | j;
                let sout_j = self.s_out[dec_with_j];
                let state_j = self.state[dec_with_j];
                let sigma_j = self.sigma[dec_with_j];
                // π = σ·s_out + (1+σ)·state — matches the symbolic
                // form the unified sumcheck will fold over.
                sigma_j * sout_j + (Block128::ONE + sigma_j) * state_j
            });
            let e = idx_y & 0b11;
            let mut acc = Block128::ZERO;
            for j in 0..STATE_SIZE {
                acc += mds_coeff(r, e, j) * pi[j];
            }
            let c2 = self.state[idx_y] + acc;
            assert_eq!(
                c2,
                Block128::ZERO,
                "C2 violated at idx_y {idx_y} (dec={dec})"
            );
        }
    }
}

/// Build the unified MLE from `N_PERMUTATIONS` input states.
pub fn build_unified_mle(
    slot_state_ins: &[[Block128; STATE_SIZE]],
) -> (UnifiedMle, Vec<PermLayerWitness>) {
    assert_eq!(
        slot_state_ins.len(),
        N_PERMUTATIONS,
        "expected exactly N_PERMUTATIONS slot inputs"
    );
    let mut mle = UnifiedMle::zero();
    let mut witnesses = Vec::with_capacity(N_PERMUTATIONS);
    for (slot, state_in) in slot_state_ins.iter().enumerate() {
        let w = evaluate_permutation(*state_in);
        mle.populate_slot(slot, &w);
        witnesses.push(w);
    }
    (mle, witnesses)
}

/// Compile-time sigma schedule: `sigma_template()[r][elem]` is the same
/// for every slot, so callers that want to verify the selector value at
/// a specific `(round, elem)` can do so without rebuilding the MLE.
pub fn sigma_at(round: usize, elem: usize) -> Block128 {
    if round >= N_ROUNDS || elem >= STATE_SIZE {
        return Block128::ZERO;
    }
    let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
    if !is_partial || elem == 0 {
        Block128::ONE
    } else {
        Block128::ZERO
    }
}

