// SPDX-License-Identifier: Apache-2.0
// Copyright (C) 2026 Ignotus Nemo. All rights reserved.

//! Packed arithmetic operations for PackedBlock128.

use super::PackedBlock128;
use crate::frost_gkr::core::hardware::{
    clmul_gcm, flat_to_tower_u128, square_flat_u128, tower_to_flat_u128, Flat, HardwareField,
};
use crate::frost_gkr::core::tower::Block128;

impl PackedBlock128 {
    #[inline(always)]
    pub fn packed_mul(self, other: Self) -> Self {
        Self {
            lanes: core::array::from_fn(|i| {
                let a_tower = Block128::from(self.lanes[i]);
                let b_tower = Block128::from(other.lanes[i]);

                // Convert tower -> flat
                let a_flat = Flat(a_tower).to_flat();
                let b_flat = Flat(b_tower).to_flat();

                // Multiply in flat basis using CLMUL
                let c_flat = a_flat * b_flat;

                // Convert flat -> tower
                c_flat.to_tower().inner().0
            }),
        }
    }

    #[inline(always)]
    pub fn square(self) -> Self {
        Self {
            lanes: core::array::from_fn(|i| {
                super::square::square_block128(Block128::from(self.lanes[i])).to_u128()
            }),
        }
    }

    #[inline(always)]
    pub fn scalar_mul(self, scalar: Block128) -> Self {
        // Convert the scalar to flat basis ONCE, instead of per-lane
        let scalar_flat = Flat(scalar).to_flat();

        Self {
            lanes: core::array::from_fn(|i| {
                let a_tower = Block128::from(self.lanes[i]);
                let a_flat = Flat(a_tower).to_flat();

                let c_flat = a_flat * scalar_flat;

                c_flat.to_tower().inner().0
            }),
        }
    }

    // ------------------------------------------------------------------
    // Flat-basis fast path
    //
    // For pipelines that perform several multiplications in a row (e.g.
    // Poseidon2b's S-box), converting to flat basis once, doing all work
    // in flat, then converting back amortises the expensive basis
    // transform over many arithmetic ops.
    // ------------------------------------------------------------------

    #[inline(always)]
    pub fn to_flat(self) -> Self {
        Self {
            lanes: self.lanes.map(tower_to_flat_u128),
        }
    }

    #[inline(always)]
    pub fn to_tower(self) -> Self {
        Self {
            lanes: self.lanes.map(flat_to_tower_u128),
        }
    }

    #[inline(always)]
    pub fn flat_mul(self, other: Self) -> Self {
        Self {
            lanes: core::array::from_fn(|i| clmul_gcm(self.lanes[i], other.lanes[i])),
        }
    }

    #[inline(always)]
    pub fn flat_square(self) -> Self {
        #[cfg(all(
            target_arch = "x86_64",
            target_feature = "avx2",
            not(target_feature = "avx512f"),
        ))]
        {
            return unsafe { super::simd_square_avx2::packed_square_flat_avx2(self) };
        }
        #[allow(unreachable_code)]
        Self {
            lanes: self.lanes.map(square_flat_u128),
        }
    }

    #[inline(always)]
    pub fn flat_scalar_mul(self, scalar_flat: u128) -> Self {
        Self {
            lanes: core::array::from_fn(|i| clmul_gcm(self.lanes[i], scalar_flat)),
        }
    }

    #[inline(always)]
    pub fn select(mask: Self, a: Self, b: Self) -> Self {
        let and_a = Self {
            lanes: core::array::from_fn(|i| mask.lanes[i] & a.lanes[i]),
        };
        let not_mask = Self {
            lanes: core::array::from_fn(|i| !mask.lanes[i]),
        };
        let and_b = Self {
            lanes: core::array::from_fn(|i| not_mask.lanes[i] & b.lanes[i]),
        };
        and_a.xor(and_b)
    }
}

