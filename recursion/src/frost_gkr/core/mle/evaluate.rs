// SPDX-License-Identifier: Apache-2.0
// Portions adapted from binius64.
// Copyright (c) 2025 The Binius Developers.
// Copyright (c) 2025 Irreducible, Inc.
// Modifications Copyright (C) 2026 Ignotus Nemo.

//! Multilinear polynomial evaluation over the boolean hypercube.

use alloc::vec::Vec;
use super::fold::fold_highest_var_inplace;
use crate::frost_gkr::core::packed::PACKED_LANES;
use crate::frost_gkr::core::tower::{Block128};
use crate::frost_gkr::core::{TowerField};

/// Evaluate a multilinear polynomial at a point using in-place folding.
pub fn evaluate_inplace_scalars<F: TowerField>(mut evals: Vec<F>, point: &[F]) -> F {
    let n = point.len();
    assert_eq!(
        evals.len(),
        1 << n,
        "eval length {} must equal 2^{}",
        evals.len(),
        n
    );

    for &coord in point.iter().rev() {
        fold_highest_var_inplace(&mut evals, coord);
    }

    assert_eq!(evals.len(), 1);
    evals[0]
}

/// Convenience function: evaluate without consuming the input.
pub fn evaluate_slice<F: TowerField>(evals: &[F], point: &[F]) -> F {
    evaluate_inplace_scalars(evals.to_vec(), point)
}

/// Evaluate an MLE using packed fold operations.
pub fn evaluate_packed(poly: &[Block128], point: &[Block128]) -> Block128 {
    use crate::frost_gkr::core::packed::{pack_slice, PackedBlock128};

    // Too small for packed path to be worthwhile — fall back to scalar.
    if poly.len() < PACKED_LANES * 2 || !poly.len().is_multiple_of(PACKED_LANES) {
        return evaluate_slice(poly, point);
    }

    let mut evals: Vec<PackedBlock128> = pack_slice(poly).to_vec();
    let mut point_iter = point.iter().rev();

    while evals.len() > 1 {
        let Some(&r) = point_iter.next() else {
            break;
        };
        let half = evals.len() / 2;
        for i in 0..half {
            let lo = evals[i];
            let hi = evals[i + half];
            let diff = hi.xor(lo);
            let scaled = diff.scalar_mul(r);
            evals[i] = lo.xor(scaled);
        }
        evals.truncate(half);
    }

    // Unpack final element and fold any remaining variables scalar-style.
    let mut scalars: Vec<Block128> = evals.into_iter().flat_map(|p| p.to_array()).collect();
    for &r in point_iter {
        fold_highest_var_inplace(&mut scalars, r);
    }

    scalars[0]
}
