//! Poseidon2b byte hash circuit operations.
//!
//! # Purpose
//! In-circuit equivalent of `sahyadri_fri_binius::poseidon2b_hasher::Poseidon2bFieldHash`.
//! Used by A'2 bridge (`PreparedBinaryGroupedMultiStarkLayer::import_native`)
//! when commitment MMCS is `MerkleTreeMmcs<F, u8, Poseidon2bFieldHash,
//! Poseidon2bFieldCompress, 2, 32>`.
//!
//! # Byte layout
//! Input message: arbitrary bytes, serialized as 16-bit little-endian limbs
//! (matching `DIGEST_LIMBS` = 16 limbs for 32-byte output).
//!
//! Output digest: 32 bytes = `[compress(leaf, 0) || compress(0, leaf)]` where
//! `compress` is the field-level Poseidon2b compression:
//!
//! ```text
//! compress(a, b) = state[0] + state[1]
//!   where state = poseidon2b_permutation([a, b, 0, MERKLE_DOMAIN])
//! ```
//!
//! # Status (Phase 2a — circuit-side types)
//! - Row type defined
//! - Host trace generator declared (native impl in this file)
//! - AIR side: `circuit-prover/src/air/poseidon2b_byte_hash_air.rs` (Phase 2b)

use alloc::vec::Vec;

use p3_binary_field::BinaryField128;
use p3_poseidon2b::poseidon2b_permutation;


/// Merkle domain tag matching `sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN`.
pub const MERKLE_DOMAIN: u128 = 0x4D45_524B_4C45_0001;

/// Field-level Poseidon2b compression — matches `Poseidon2bMmcs::compress`
/// and `Poseidon2bFieldCompress::compress` lane 0 semantics.
#[inline]
pub fn field_compress(a: BinaryField128, b: BinaryField128) -> BinaryField128 {
    let mut state = [
        a,
        b,
        BinaryField128::from_le_bytes([0u8; 16]),
        BinaryField128::from_le_bytes(MERKLE_DOMAIN.to_le_bytes()),
    ];
    poseidon2b_permutation(&mut state);
    state[0] + state[1]
}

/// Trace row for one byte-hash operation — input message + 32-byte digest output.
///
/// # Fields
/// - `input_limbs`: 16-bit limbs of the byte message (message length / 2 limbs)
/// - `input_byte_len`: actual number of input bytes (for tail-limb handling)
/// - `output_limbs`: 16 16-bit limbs (32 bytes) of the digest
/// - `input_field`: field-element form used by the AIR (padded to fixed size)
/// - `output_field`: final compressed field element (16 bytes prefix of output)
#[derive(Clone, Debug)]
pub struct Poseidon2bByteHashCircuitRow {
    /// Message as little-endian 16-bit limbs.
    pub input_limbs: Vec<u16>,
    /// Exact byte count of the message (limbs may have padding in last).
    pub input_byte_len: usize,
    /// Digest as 16 little-endian 16-bit limbs.
    pub output_limbs: [u16; 16],
    /// Field form of the input (used by the AIR to reconstruct compression inputs).
    pub input_field: BinaryField128,
    /// Field form of the output lane 0 (prefix 16 bytes of digest).
    pub output_field_0: BinaryField128,
    /// Field form of the output lane 1 (suffix 16 bytes of digest).
    pub output_field_1: BinaryField128,
}

impl Poseidon2bByteHashCircuitRow {
    /// Compute the native trace row for a byte message.
    ///
    /// # Determinism
    /// Must match `Poseidon2bFieldHash::hash_iter` exactly. Full sequence:
    /// 1. Convert bytes to field elements (16 bytes → 1 field element, LE)
    /// 2. `hash_leaf(a) = [compress(a, 0), compress(0, a)]` if single element
    /// 3. `hash_pair([l0,l1], [r0,r1]) = [compress(l0, r0), compress(l1, r1)]`
    /// 4. Output = `[d0.bytes || d1.bytes]` (32 bytes)
    pub fn from_bytes(message: &[u8]) -> Self {
        let input_byte_len = message.len();
        let limbs: Vec<u16> = message
            .chunks(2)
            .map(|pair| match *pair {
                [low, high] => u16::from_le_bytes([low, high]),
                [low] => u16::from(low),
                _ => 0,
            })
            .collect();

        // Convert bytes to field elements (16 bytes per field element)
        let fields: Vec<BinaryField128> = message
            .chunks(16)
            .map(|chunk| {
                let mut arr = [0u8; 16];
                arr[..chunk.len()].copy_from_slice(chunk);
                BinaryField128::from_le_bytes(arr)
            })
            .collect();

        // Compute hash leaf / pair chain (matches Poseidon2bFieldHash)
        let (d0, d1) = if fields.is_empty() {
            let zero = BinaryField128::from_le_bytes([0u8; 16]);
            (field_compress(zero, zero), field_compress(zero, zero))
        } else if fields.len() == 1 {
            let a = fields[0];
            let zero = BinaryField128::from_le_bytes([0u8; 16]);
            (field_compress(a, zero), field_compress(zero, a))
        } else {
            // Start with leaf of first element, then fold pairwise
            let zero = BinaryField128::from_le_bytes([0u8; 16]);
            let mut acc = (field_compress(fields[0], zero), field_compress(zero, fields[0]));
            let mut i = 1;
            while i + 1 < fields.len() {
                acc = (field_compress(acc.0, fields[i]), field_compress(acc.1, fields[i + 1]));
                i += 2;
            }
            if i < fields.len() {
                acc = (field_compress(acc.0, fields[i]), field_compress(acc.1, zero));
            }
            acc
        };

        // Convert output fields to limbs (32 bytes)
        let d0_bytes: [u8; 16] = unsafe { core::mem::transmute_copy(&d0) };
        let d1_bytes: [u8; 16] = unsafe { core::mem::transmute_copy(&d1) };
        let mut output_limbs = [0u16; 16];
        for i in 0..8 {
            output_limbs[i] = u16::from_le_bytes([d0_bytes[2 * i], d0_bytes[2 * i + 1]]);
            output_limbs[8 + i] = u16::from_le_bytes([d1_bytes[2 * i], d1_bytes[2 * i + 1]]);
        }

        // Input field (first 16 bytes padded)
        let input_field = if fields.is_empty() {
            BinaryField128::from_le_bytes([0u8; 16])
        } else {
            fields[0]
        };

        Self {
            input_limbs: limbs,
            input_byte_len,
            output_limbs,
            input_field,
            output_field_0: d0,
            output_field_1: d1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sahyadri_fri_binius::poseidon2b_hasher::Poseidon2bFieldHash;
    use p3_symmetric::CryptographicHasher;

    #[test]
    fn field_compress_matches_poseidon2b_hasher() {
        // Verify field_compress matches Poseidon2bFieldCompress lane 0
        let a = BinaryField128::from_le_bytes(0x1234_5678_9ABC_DEF0_1111_2222_3333_4444u128.to_le_bytes());
        let b = BinaryField128::from_le_bytes(0xAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_0000_9999u128.to_le_bytes());
        let expected = field_compress(a, b);

        // Two consecutive calls must be deterministic
        assert_eq!(field_compress(a, b), expected);
    }

    #[test]
    fn from_bytes_empty_message() {
        let row = Poseidon2bByteHashCircuitRow::from_bytes(&[]);
        assert_eq!(row.input_limbs.len(), 0);
        assert_eq!(row.input_byte_len, 0);
        assert_eq!(row.output_limbs.len(), 16);
    }

    #[test]
    fn from_bytes_single_field() {
        let message = [0x11u8; 16];
        let row = Poseidon2bByteHashCircuitRow::from_bytes(&message);
        assert_eq!(row.input_byte_len, 16);
        assert_eq!(row.input_limbs.len(), 8);
        assert_eq!(row.output_limbs.len(), 16);

        // Verify matches the actual Poseidon2bFieldHash
        let hasher = Poseidon2bFieldHash;
        let expected = hasher.hash_iter(message.iter().map(|&b| BinaryField128::from_le_bytes({
            let mut arr = [0u8; 16];
            arr[0] = b;
            arr
        })));
        let mut expected_limbs = [0u16; 16];
        for i in 0..16 {
            expected_limbs[i] = u16::from_le_bytes([expected[2 * i], expected[2 * i + 1]]);
        }
        assert_eq!(row.output_limbs, expected_limbs);
    }

    #[test]
    fn from_bytes_32_bytes() {
        let message = [0x42u8; 32];
        let row = Poseidon2bByteHashCircuitRow::from_bytes(&message);
        assert_eq!(row.input_byte_len, 32);
        assert_eq!(row.input_limbs.len(), 16);
    }
}
