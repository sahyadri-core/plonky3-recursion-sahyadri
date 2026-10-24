// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Ignotus Nemo.

//! Round-shift index helpers and public MLE evaluators for FROST-GKR.
//!
//! The unified sumcheck proves
//!
//! ```text
//!   Σ_y  U(y) · [ C1(dec(y)) + β · C2(y) ] = 0
//! ```
//!
//! by the change of variable `y = inc_round(x)`. The non-linearity of
//! the round-shift carry stays out of the MLEs and lives entirely in
//! these public schedules:
//!
//! * `U(y)             = eq(ρ, dec(y)) · μ(dec(y))`
//! * `μ(x) = 1` iff `round(x) < N_ROUNDS` and `slot(x) < N_PERMUTATIONS`.
//!   This live-cell mask is keyed at `dec(y)`, like C1, C1', and the C2
//!   source row whose MDS image is `state(y)`.
//! * `RC(y)` is the public 15-variable MLE of round constants indexed at
//!   the next round and evaluated directly at `y`.
//! * `σ(x)`            is the public S-box selector schedule.
//!
//! Index layout (low → high bit): `elem:2 | round:7 | slot:6`.
//! `dec_round_index(y)` decrements the round bits by 1 (mod 128) using
//! plain integer arithmetic on the 15-bit index — no symbolic
//! polynomial work.
//!
//! All `*_evaluate` functions take a 15-element point in `F^15` and
//! return the evaluation of the corresponding multilinear extension.
//! They are used by the verifier and by prover sanity tests.

use alloc::vec;
use alloc::vec::Vec;
use crate::frost_gkr::core::mle::eq::eq_ind_partial_eval;
use crate::frost_gkr::core::tower::Block128;
use crate::frost_gkr::core::TowerField;
use crate::frost_gkr::core::native::permutation::{
    F_ROUNDS, MDS_FULL, MDS_PARTIAL, N_ROUNDS, P_ROUNDS, ROUND_CONSTANTS, STATE_SIZE,
};

use crate::frost_gkr::sequence::N_PERMUTATIONS;
use crate::frost_gkr::unified_mle::{
    sigma_at, N_LANE_VARS, N_ROUND_VARS, N_SLOT_VARS, N_UNIFIED_CELLS, N_UNIFIED_VARS,
};

const ELEM_BITS: usize = N_LANE_VARS; // 2
const ROUND_BITS: usize = N_ROUND_VARS; // 7
const SLOT_BITS: usize = N_SLOT_VARS; // 6

const ROUND_SHIFT: usize = ELEM_BITS;
const SLOT_SHIFT: usize = ELEM_BITS + ROUND_BITS;

const ROUND_MASK: u16 = ((1 << ROUND_BITS) - 1) << ROUND_SHIFT;
const ELEM_MASK: u16 = (1 << ELEM_BITS) - 1;
const SLOT_MASK: u16 = ((1 << SLOT_BITS) - 1) << SLOT_SHIFT;

const ROUND_LIMIT: usize = 1 << ROUND_BITS; // 128
const ELEM_LIMIT: usize = 1 << ELEM_BITS; // 4

// Compile-time consistency with the unified MLE.
const _: () = assert!(ELEM_BITS + ROUND_BITS + SLOT_BITS == N_UNIFIED_VARS);

#[inline]
pub fn round_of(idx: u16) -> usize {
    ((idx & ROUND_MASK) >> ROUND_SHIFT) as usize
}

#[inline]
pub fn elem_of(idx: u16) -> usize {
    (idx & ELEM_MASK) as usize
}

#[inline]
pub fn slot_of(idx: u16) -> usize {
    ((idx & SLOT_MASK) >> SLOT_SHIFT) as usize
}

#[inline]
pub fn dec_round_index(idx: u16) -> u16 {
    let round = round_of(idx);
    let prev = (round + ROUND_LIMIT - 1) & (ROUND_LIMIT - 1);
    (idx & !ROUND_MASK) | ((prev as u16) << ROUND_SHIFT)
}

#[inline]
pub fn inc_round_index(idx: u16) -> u16 {
    let round = round_of(idx);
    let next = (round + 1) & (ROUND_LIMIT - 1);
    (idx & !ROUND_MASK) | ((next as u16) << ROUND_SHIFT)
}

// ---------------------------------------------------------------------------
// μ schedule
// ---------------------------------------------------------------------------

/// `μ_table[idx] == ONE` iff `slot(idx) < N_PERMUTATIONS` and
/// `round(idx) < N_ROUNDS` (the "live witness cell" mask). Otherwise
/// `ZERO`. Length `2^15`.
pub fn build_mu_table() -> Vec<Block128> {
    let mut tab = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for slot in 0..N_PERMUTATIONS {
        for round in 0..N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = pack_index(slot, round, elem);
                tab[idx as usize] = Block128::ONE;
            }
        }
    }
    tab
}

/// Evaluate the multilinear extension of μ at an arbitrary point.
pub fn mu_evaluate(point: &[Block128]) -> Block128 {
    debug_assert_eq!(point.len(), N_UNIFIED_VARS);
    inner_product_with_eq_tensor(&build_mu_table(), point)
}

// ---------------------------------------------------------------------------
// σ schedule
// ---------------------------------------------------------------------------

/// `σ_table[idx] == ONE` iff the cell goes through the x^7 S-box on the
/// active topology. Length `2^15`.
pub fn build_sigma_table() -> Vec<Block128> {
    let mut tab = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for slot in 0..N_PERMUTATIONS {
        for round in 0..N_ROUNDS {
            for elem in 0..STATE_SIZE {
                let idx = pack_index(slot, round, elem);
                tab[idx as usize] = sigma_at(round, elem);
            }
        }
    }
    tab
}

/// Evaluate the multilinear extension of σ at an arbitrary point.
pub fn sigma_evaluate(point: &[Block128]) -> Block128 {
    debug_assert_eq!(point.len(), N_UNIFIED_VARS);
    inner_product_with_eq_tensor(&build_sigma_table(), point)
}

// ---------------------------------------------------------------------------
// Round-constant MLE: RC(idx) = ROUND_CONSTANTS[elem][round] for live cells.
// Indexed at *the cell where the constant is consumed*, i.e. directly
// at `y` after the change of variable.
// ---------------------------------------------------------------------------

/// RC table indexed by `(slot, round, elem)`. Pads zero outside the
/// live topology. The constant for partial rounds is stored only at
/// `elem == 0` to mirror the native permutation semantics.
pub fn build_rc_table() -> Vec<Block128> {
    let mut tab = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for slot in 0..N_PERMUTATIONS {
        for round in 0..N_ROUNDS {
            let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
            for elem in 0..STATE_SIZE {
                if is_partial && elem != 0 {
                    continue;
                }
                let idx = pack_index(slot, round, elem);
                tab[idx as usize] = Block128::from(ROUND_CONSTANTS[elem][round]);
            }
        }
    }
    tab
}

/// Evaluate the public RC MLE at an arbitrary point.
pub fn rc_evaluate(point: &[Block128]) -> Block128 {
    debug_assert_eq!(point.len(), N_UNIFIED_VARS);
    inner_product_with_eq_tensor(&build_rc_table(), point)
}

// ---------------------------------------------------------------------------
// MDS row coefficient lookup, used by C2.
// ---------------------------------------------------------------------------

#[inline]
pub fn mds_coeff(round: usize, i: usize, j: usize) -> Block128 {
    debug_assert!(round < N_ROUNDS);
    debug_assert!(i < STATE_SIZE);
    debug_assert!(j < STATE_SIZE);
    let is_partial = (F_ROUNDS / 2..F_ROUNDS / 2 + P_ROUNDS).contains(&round);
    let raw = if is_partial {
        MDS_PARTIAL[i][j]
    } else {
        MDS_FULL[i][j]
    };
    Block128::from(raw)
}

// ---------------------------------------------------------------------------
// Round-shift table helpers.
//
// All "_dec" tables are pure permutations of their source by
// `dec_round_index`. They let the unified sumcheck treat all factors
// as plain multilinear MLEs in `y`, at the cost of running a small
// shift gadget afterwards to reduce a `T_dec_ml(r')` claim back to a
// claim on `T_ml` at a permuted point.
// ---------------------------------------------------------------------------

/// Return `out[y] = src[dec_round_index(y)]`. Used to align every
/// "indexed at `dec(y)`" factor of the unified constraint with the
/// natural `y`-fold direction of the sumcheck.
pub fn permute_by_dec(src: &[Block128]) -> Vec<Block128> {
    debug_assert_eq!(src.len(), N_UNIFIED_CELLS);
    let mut out = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for y in 0..N_UNIFIED_CELLS {
        out[y] = src[dec_round_index(y as u16) as usize];
    }
    out
}

/// Build the unified mask `U[y] = eq(ρ, dec(y)) · μ(dec(y))` for the
/// main sumcheck. `ρ` has length `N_UNIFIED_VARS`. This is the
/// only `dec`-twisted public schedule the verifier rebuilds natively
/// at the start of the protocol.
pub fn build_u_table(rho: &[Block128]) -> Vec<Block128> {
    debug_assert_eq!(rho.len(), N_UNIFIED_VARS);
    let eq_tab = eq_ind_partial_eval::<Block128>(rho); // eq(ρ, ·) at the point as full hypercube
    let mu_tab = build_mu_table();
    let mut out = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for y in 0..N_UNIFIED_CELLS {
        let x = dec_round_index(y as u16) as usize;
        out[y] = eq_tab[x] * mu_tab[x];
    }
    out
}

/// Build `lane[y] = src[ (slot(y), round(y), e=lane) ]`. Independent of
/// the `elem` bits of `y` — those are projected out and replaced by a
/// fixed lane index. Used by the C2 contribution where the four MDS
/// inputs come from the four lanes of the same `(slot, round)` row.
pub fn project_lane(src: &[Block128], lane: usize) -> Vec<Block128> {
    debug_assert!(lane < STATE_SIZE);
    debug_assert_eq!(src.len(), N_UNIFIED_CELLS);
    let mut out = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for y in 0..N_UNIFIED_CELLS {
        let row_base = (y as u16) & !ELEM_MASK; // zero the elem bits
        out[y] = src[(row_base | lane as u16) as usize];
    }
    out
}

/// `M_kind_lane_table[y] = M_{kind(dec(y))}[elem(y)][lane]` — the four
/// per-lane MDS coefficient schedules used by C2. `lane` ranges over
/// `0..STATE_SIZE`. Padded cells (slot ≥ N_PERMUTATIONS or
/// round(dec(y)) outside `0..N_ROUNDS`) get coefficient `ZERO` so the
/// C2 contribution there vanishes.
pub fn build_mds_lane_table(lane: usize) -> Vec<Block128> {
    debug_assert!(lane < STATE_SIZE);
    let mut out = vec![Block128::ZERO; N_UNIFIED_CELLS];
    for y in 0..N_UNIFIED_CELLS {
        let yb = y as u16;
        let slot = slot_of(yb);
        if slot >= N_PERMUTATIONS {
            continue;
        }
        let dec_round = round_of(dec_round_index(yb));
        if dec_round >= N_ROUNDS {
            continue;
        }
        let elem = elem_of(yb);
        out[y] = mds_coeff(dec_round, elem, lane);
    }
    out
}

// ---------------------------------------------------------------------------
// Internals.
// ---------------------------------------------------------------------------

#[inline]
pub fn pack_index(slot: usize, round: usize, elem: usize) -> u16 {
    debug_assert!(slot < (1 << SLOT_BITS));
    debug_assert!(round < ROUND_LIMIT);
    debug_assert!(elem < ELEM_LIMIT);
    ((slot << SLOT_SHIFT) | (round << ROUND_SHIFT) | elem) as u16
}

/// Inner product of a length-`2^15` table with the eq-tensor of
/// `point`, evaluating the multilinear extension of `tab` at `point`.
fn inner_product_with_eq_tensor(tab: &[Block128], point: &[Block128]) -> Block128 {
    let eq_tab = eq_ind_partial_eval::<Block128>(point);
    debug_assert_eq!(eq_tab.len(), tab.len());
    let mut acc = Block128::ZERO;
    for (a, b) in tab.iter().zip(eq_tab.iter()) {
        acc += *a * *b;
    }
    acc
}

