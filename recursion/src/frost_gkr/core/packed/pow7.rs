// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Ignotus Nemo. All rights reserved.

//! Fast `x ↦ x^7` on `Block128` for the Poseidon2b S-box.
//!
//! In GF(2^128) squaring is the Frobenius endomorphism — a *linear*
//! operation `(a+b)^2 = a^2 + b^2`. So `x^7` decomposes as
//!
//! ```text
//!   s  = x
//!   s2 = s.square()           // free (linear)
//!   s3 = s2 * s                // 1 CLMUL
//!   s4 = s2.square()           // free (linear)
//!   s7 = s4 * s3               // 1 CLMUL
//! ```
//!
//! Total: **2 multiplications + 2 Frobenius squarings**. The previous
//! naive `x.pow(7)` performs 4 multiplications (or 6 in a generic
//! square-and-multiply), so this saves ~50% of the per-element work
//! inside the degree-nine FROST-GKR main sumcheck.

use super::PackedBlock128;
use crate::frost_gkr::core::hardware::{clmul_gcm, square_flat_u128};
use crate::frost_gkr::core::tower::Block128;

#[inline(always)]
pub fn pow7_block128(x: Block128) -> Block128 {
    let s2 = x.square();
    let s3 = s2 * x;
    let s4 = s2.square();
    s4 * s3
}

#[inline(always)]
pub fn pow7_flat_block128(x: u128) -> u128 {
    let s2 = square_flat_u128(x);
    let s3 = clmul_gcm(s2, x);
    let s4 = square_flat_u128(s2);
    clmul_gcm(s4, s3)
}

#[inline(always)]
pub fn pow7_packed(x: PackedBlock128) -> PackedBlock128 {
    let arr = x.to_array();
    let out = arr.map(pow7_block128);
    PackedBlock128::from_array(out)
}

