// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Ignotus Nemo. All rights reserved.

//! Fast Karatsuba multiplication for binary tower fields.
//!
//! The tower type hierarchy already implements Karatsuba recursively:
//!   Block128 → Block64 → Block32 → Block16 → Block8
//!
//! The base case `Block8::mul` uses a precomputed 256×256 lookup table,
//! so the full multiplication is already optimal.  This module simply
//! re-exports the scalar fast path for use in packed lanes.

use crate::frost_gkr::core::tower::Block128;

#[inline(always)]
pub fn mul_block128_fast(a: Block128, b: Block128) -> Block128 {
    a * b
}
