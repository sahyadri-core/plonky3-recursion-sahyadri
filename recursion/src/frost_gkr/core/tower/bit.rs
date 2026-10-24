// SPDX-License-Identifier: Apache-2.0
// Portions derived from hekate-math.
// Copyright (C) 2026 Andrei Kochergin and Oumuamua Labs.
// Modifications Copyright (C) 2026 Ignotus Nemo.

use crate::frost_gkr::core::{CanonicalDeserialize, CanonicalSerialize, SerializationError, TowerField};
use serde::{Deserialize, Serialize};
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Serialize, Deserialize)]
#[repr(transparent)]
pub struct Bit(pub u8);

impl Bit {
    pub const fn new(val: u8) -> Self {
        Self(val & 1)
    }
}

impl TowerField for Bit {
    const BITS: usize = 1;
    const ZERO: Self = Bit(0);
    const ONE: Self = Bit(1);

    /// For the extension GF(2) → GF(2^2), the irreducible polynomial
    /// is x^2 + x + 1 = 0, so TAU = 1.
    const EXTENSION_TAU: Self = Bit(1);

    fn invert(&self) -> Self {
        // In GF(2), inverse of 1 is 1; inverse of 0 is 0 (by convention).
        *self
    }

    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        Self(bytes[0] & 1)
    }
}

// ---- Arithmetic: Add = XOR ----

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Bit {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl Sub for Bit {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Mul for Bit {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl AddAssign for Bit {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl SubAssign for Bit {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl MulAssign for Bit {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---- Canonical Serialization ----

impl CanonicalSerialize for Bit {
    fn serialized_size(&self) -> usize {
        1
    }
    fn serialize(&self, writer: &mut [u8]) -> Result<(), SerializationError> {
        if writer.is_empty() {
            return Err(SerializationError);
        }
        writer[0] = self.0;
        Ok(())
    }
}

impl CanonicalDeserialize for Bit {
    fn deserialize(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.is_empty() {
            return Err(SerializationError);
        }
        if bytes[0] > 1 {
            return Err(SerializationError);
        }
        Ok(Self(bytes[0]))
    }
}

// ---- From conversions ----

impl From<u8> for Bit {
    fn from(val: u8) -> Self {
        Self(val & 1)
    }
}

impl From<u32> for Bit {
    fn from(val: u32) -> Self {
        Self((val & 1) as u8)
    }
}

impl From<u64> for Bit {
    fn from(val: u64) -> Self {
        Self((val & 1) as u8)
    }
}

impl From<u128> for Bit {
    fn from(val: u128) -> Self {
        Self((val & 1) as u8)
    }
}

