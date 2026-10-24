// SPDX-License-Identifier: Apache-2.0
// Portions adapted from binius64.
// Copyright (c) 2025 The Binius Developers.
// Copyright (c) 2025 Irreducible, Inc.
// Modifications Copyright (C) 2026 Ignotus Nemo.

//! Equality indicator polynomial for multilinear extensions.
//! Computes tensor products of (1 - r_i, r_i) over the boolean hypercube.
use alloc::vec;
use alloc::vec::Vec;
use crate::frost_gkr::core::tower::{Block128};
use crate::frost_gkr::core::{TowerField};

#[inline(always)]
pub fn eq_one_var<F: TowerField>(x: F, y: F) -> F {
    let one = F::ONE;
    x * y + (one - x) * (one - y)
}

/// Evaluate the full equality indicator polynomial at two length-n slices.
/// eq(x_0..x_{n-1}, y_0..y_{n-1}) = ∏_{i=0}^{n-1} eq_one_var(x_i, y_i)
pub fn eq_ind<F: TowerField>(x: &[F], y: &[F]) -> F {
    assert_eq!(x.len(), y.len());
    x.iter()
        .zip(y.iter())
        .map(|(xi, yi)| eq_one_var(*xi, *yi))
        .fold(F::ONE, |acc, val| acc * val)
}

/// Compute the partial evaluation of the equality indicator polynomial.
///
/// Returns the tensor product (1 - r_0, r_0) ⊗ ... ⊗ (1 - r_{n-1}, r_{n-1})
/// as a Vec<F> of length 2^n.
pub fn eq_ind_partial_eval<F: TowerField>(point: &[F]) -> Vec<F> {
    if point.is_empty() {
        return vec![F::ONE];
    }

    let mut result = vec![F::ONE];

    for &r_i in point {
        let len = result.len();
        result.reserve(len);
        for j in 0..len {
            // val * r_i computed once
            let prod = result[j] * r_i;
            // lo = val * (1 - r_i) = val - val*r_i
            result[j] -= prod;
            // hi = val * r_i
            result.push(prod);
        }
    }

    result
}

/// Compute the tensor product (1 - r_{k-1}, r_{k-1}) ⊗ ... ⊗ (1 - r_0, r_0) ⊗ v.
/// This is the left-tensor variant.
pub fn tensor_prod_eq_ind_prepend<F: TowerField>(values: &mut Vec<F>, extra_coords: &[F]) {
    for &r_i in extra_coords.iter().rev() {
        let len = values.len();
        values.reserve(len);
        for j in (0..len).rev() {
            let eval = values[j];
            // values[2*j] = eval * (1 - r_i)
            values[2 * j] = eval * (F::ONE - r_i);
            // values[2*j + 1] = eval * r_i
            values.push(eval * r_i);
        }
    }
}

/// Truncate the equality indicator expansion to fewer variables by summing halves.
pub fn eq_ind_truncate_low_inplace<F: TowerField>(values: &mut Vec<F>, truncated_log_len: usize) {
    let current_log_len = values.len().trailing_zeros() as usize;
    assert!(truncated_log_len <= current_log_len);

    for _log_len in (truncated_log_len..current_log_len).rev() {
        let half = values.len() / 2;
        for j in 0..half {
            values[j] = values[j] + values[j + half];
        }
        values.truncate(half);
    }
}

// ---------------------------------------------------------------------------
// Packed variant for Block128
// ---------------------------------------------------------------------------

/// Compute the equality indicator tensor using packed operations.
pub fn eq_ind_packed(point: &[Block128], num_vars: usize) -> Vec<Block128> {
    let size = 1usize << num_vars;
    let mut result = vec![Block128::ZERO; size];
    result[0] = Block128::ONE;

    let mut current_size = 1;

    for &r in point.iter() {
        let one_plus_r = Block128::ONE + r;

        for i in 0..current_size {
            result[i + current_size] = result[i] * r;
            result[i] *= one_plus_r;
        }
        current_size *= 2;
    }

    result
}
