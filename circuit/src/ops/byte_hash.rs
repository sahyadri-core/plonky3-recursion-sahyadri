//! Gadgets shared by the byte-oriented hashes (Keccak-256 and BLAKE3): canonical field-element
//! serialization and Merkle path verification.
//!
//! Byte strings travel as little-endian 16-bit limbs, two bytes per limb; a 32-byte digest is
//! [`DIGEST_LIMBS`] limbs.

use alloc::format;
use alloc::vec::Vec;

use p3_field::{ExtensionField, Field, PrimeField64};
use p3_util::log2_ceil_usize;

use super::binary_host::BinaryCircuitHost;
use crate::builder::CircuitBuilderError;
use crate::types::ExprId;

/// Bits per limb.
const LIMB_BITS: usize = 16;
/// 16-bit limbs in a 32-byte digest.
pub const DIGEST_LIMBS: usize = 16;

/// A 32-byte hash available as a circuit gadget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteHash {
    /// Keccak-256 (`p3_keccak::Keccak256Hash`), over the Keccak-f\[1600\] operation.
    Keccak256,
    /// BLAKE3 (`p3_blake3::Blake3`), over the BLAKE3 compression operation.
    Blake3,
    /// Poseidon2b byte hash, matching `MerkleTreeMmcs<F, u8, Poseidon2bFieldHash,
    /// Poseidon2bFieldCompress, 2, 32>` semantics.
    ///
    /// # Status (Phase 1, WIP)
    /// Enum variant added for A'2 bridge. In-circuit implementation lands Phase 2.
    /// Currently returns `CircuitBuilderError::UnsupportedNonPrimitiveOp` for all
    /// operations. Used by `import_native` on Poseidon2b MMCS proofs.
    Poseidon2b,
}

impl<F> crate::CircuitBuilder<F>
where
    F: Field + Eq + core::hash::Hash,
{
    /// Each element's serialized little-endian bytes, as 16-bit limbs: the byte stream a
    /// `SerializingHasher` feeds its byte hash.
    ///
    /// Plonky3 serializes an element as a unique integer below `p`, which is not always its
    /// canonical value: Montgomery fields (BabyBear, KoalaBear) serialize `x·2^32 mod p`. Both
    /// forms are `x·u(1)` for the serialization `u(1)` of one, so each element is scaled by that
    /// constant and then decomposed into canonical bits (`value < p`), which stops a prover from
    /// substituting the encoding of `y + p` for `y`.
    ///
    /// # Errors
    ///
    /// As [`Self::decompose_to_bits`].
    ///
    /// # Panics
    ///
    /// If `BF`'s serialization is not linear in the element, which no Plonky3 prime field is.
    pub fn serialize_field_elements_to_limbs<BF>(
        &mut self,
        elements: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        let limbs_per_element = BF::NUM_BYTES / 2;
        let serialized = |x: BF| -> u64 {
            BF::into_byte_stream([x])
                .into_iter()
                .enumerate()
                .fold(0, |acc, (i, byte)| acc | (u64::from(byte) << (8 * i)))
        };
        let scale = BF::from_u64(serialized(BF::ONE));
        assert_eq!(
            serialized(BF::GENERATOR),
            (BF::GENERATOR * scale).as_canonical_u64(),
            "field serialization must be x -> x * u(1)"
        );
        let scale = self.define_const(F::from(scale));

        let mut limbs = Vec::with_capacity(elements.len() * limbs_per_element);
        for &element in elements {
            let serialized_value = self.mul(element, scale);
            let bits = self.decompose_to_bits::<BF>(serialized_value, BF::bits())?;
            for chunk in 0..limbs_per_element {
                let mut limb = self.define_const(F::ZERO);
                for (i, &bit) in bits
                    .iter()
                    .skip(chunk * LIMB_BITS)
                    .take(LIMB_BITS)
                    .enumerate()
                {
                    let weight = self.define_const(F::from_u32(1 << i));
                    limb = self.mul_add(bit, weight, limb);
                }
                limbs.push(limb);
            }
        }
        Ok(limbs)
    }

    /// `hash` of a message given as little-endian 16-bit limbs; returns the 32-byte digest as
    /// [`DIGEST_LIMBS`] limbs.
    ///
    /// # Errors
    ///
    /// As [`Self::keccak256_limbs`] or [`Self::blake3_limbs`].
    pub fn byte_hash_limbs<BF>(
        &mut self,
        hash: ByteHash,
        message: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        match hash {
            ByteHash::Keccak256 => self.keccak256_limbs::<BF>(message),
            ByteHash::Blake3 => self.blake3_limbs::<BF>(message),
            ByteHash::Poseidon2b => self.poseidon2b_limbs::<BF>(message),
        }
    }

    /// `hash` of an exact byte string, including an odd number of bytes.
    /// Returns the 32-byte digest as [`DIGEST_LIMBS`] little-endian limbs.
    /// Each input is constrained to a base-field integer in `0..=255`.
    ///
    /// # Errors
    ///
    /// As [`Self::decompose_to_bits`] and the selected hash gadget.
    pub fn byte_hash_bytes<BF>(
        &mut self,
        hash: ByteHash,
        message: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        for &byte in message {
            self.decompose_to_bits::<BF>(byte, 8)?;
        }
        let scale = self.define_const(F::from_u16(256));
        let limbs: Vec<_> = message
            .chunks(2)
            .map(|pair| match *pair {
                [low, high] => self.mul_add(high, scale, low),
                [low] => low,
                _ => unreachable!("nonempty byte pairs"),
            })
            .collect();
        match hash {
            ByteHash::Keccak256 => self.keccak256_packed_bytes::<BF>(&limbs, message.len()),
            ByteHash::Blake3 => self.blake3_packed_bytes(&limbs, message.len()),
            ByteHash::Poseidon2b => self.poseidon2b_packed_bytes::<BF>(&limbs, message.len()),
        }
    }

    /// `SerializingHasher<hash>` of base-field elements, the leaf hash of a `hash` Merkle tree.
    ///
    /// # Errors
    ///
    /// As [`Self::serialize_field_elements_to_limbs`] and [`Self::byte_hash_limbs`].
    pub fn byte_hash_field_elements<BF>(
        &mut self,
        hash: ByteHash,
        elements: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        let limbs = self.serialize_field_elements_to_limbs::<BF>(elements)?;
        self.byte_hash_limbs::<BF>(hash, &limbs)
    }

    /// `CompressionFunctionFromHasher<hash, 2, 32>`: `hash` of the 64-byte concatenation of two
    /// digests, the node compression of a `hash` Merkle tree.
    ///
    /// # Errors
    ///
    /// [`CircuitBuilderError::NonPrimitiveOpArity`] for a digest of the wrong width, or as the
    /// hash's own gadget.
    pub fn byte_hash_compress<BF>(
        &mut self,
        hash: ByteHash,
        left: &[ExprId],
        right: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        match hash {
            ByteHash::Keccak256 => self.keccak256_compress(left, right),
            ByteHash::Blake3 => self.blake3_compress_digests::<BF>(left, right),
            ByteHash::Poseidon2b => self.poseidon2b_compress_digests::<BF>(left, right),
        }
    }

    /// Constrains an opening of a `hash` `MerkleTreeMmcs` batch commitment at one index.
    ///
    /// This mirrors the native binary-arity `verify_batch`:
    ///
    /// - `rows[m]` is matrix `m`'s opened row (base-field elements), in commitment order, and
    ///   `heights[m]` its height. Heights need not be powers of two, but as natively, each must be
    ///   `ceil(max_height / 2^k)` for some `k`; the tree has `index_bits.len() =
    ///   ceil(log2(max_height))` levels, and a matrix of height `h` sits `ceil(log2(h))` levels
    ///   above the root.
    /// - The index, whose little-endian bits are `index_bits`, is constrained below `max_height`.
    /// - The leaf digest hashes the concatenated rows of every tallest matrix
    ///   (`SerializingHasher<hash>`).
    /// - Level `i` compresses the pair ordered by `index_bits[i]` (set: the current node is the
    ///   right child) with `siblings[i]`; then, if some matrices sit at the level just reached,
    ///   the digest becomes `compress(digest, hash(their rows))`.
    /// - After `index_bits.len() - log2(cap.len())` levels, the remaining index bits select the
    ///   cap root the digest must equal.
    ///
    /// Digests are [`DIGEST_LIMBS`] limbs. Every index bit is constrained to be boolean.
    ///
    /// # Errors
    ///
    /// - [`CircuitBuilderError::NonPrimitiveOpArity`] if the rows and heights, the path and the
    ///   index, or a digest's width disagree; if a height is not reachable from the tallest; if
    ///   the cap is not a power-of-two root count at most `2^index_bits.len()`; or if some matrix
    ///   sits below the cap layer.
    /// - As [`Self::byte_hash_field_elements`] and [`Self::byte_hash_compress`].
    #[allow(clippy::too_many_arguments)]
    pub fn verify_byte_hash_mmcs_opening<BF>(
        &mut self,
        hash: ByteHash,
        rows: &[Vec<ExprId>],
        heights: &[usize],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        cap: &[Vec<ExprId>],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        self.verify_byte_hash_mmcs_opening_with(
            rows,
            heights,
            index_bits,
            siblings,
            cap,
            |builder, row| builder.byte_hash_field_elements::<BF>(hash, row),
            |builder, left, right| builder.byte_hash_compress::<BF>(hash, left, right),
        )
    }

    /// Constrains a byte-hash MMCS opening whose rows are already serialized as
    /// little-endian 16-bit limbs.
    ///
    /// Each row's limbs are concatenated directly, without host-field serialization.
    /// This is the leaf encoding for represented binary tower elements: a
    /// `BinaryField128` contributes eight limbs in raw coordinate order. Every
    /// supplied row limb is constrained to a base-field integer in `0..=65535`.
    /// Heights, index bits, siblings and caps follow [`Self::verify_byte_hash_mmcs_opening`].
    /// The caller must check each row's serialized width against its native matrix.
    ///
    /// # Errors
    ///
    /// As [`Self::verify_byte_hash_mmcs_opening`], [`Self::decompose_to_bits`] and
    /// [`Self::byte_hash_limbs`].
    #[allow(clippy::too_many_arguments)]
    pub fn verify_byte_hash_mmcs_opening_limbs<BF>(
        &mut self,
        hash: ByteHash,
        rows: &[Vec<ExprId>],
        heights: &[usize],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        cap: &[Vec<ExprId>],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        self.verify_byte_hash_mmcs_opening_with(
            rows,
            heights,
            index_bits,
            siblings,
            cap,
            |builder, row| {
                for &limb in row {
                    builder.decompose_to_bits::<BF>(limb, LIMB_BITS)?;
                }
                builder.byte_hash_limbs::<BF>(hash, row)
            },
            |builder, left, right| builder.byte_hash_compress::<BF>(hash, left, right),
        )
    }

    /// Constrains a byte-hash MMCS opening whose rows are serialized as exact
    /// byte strings. Each row byte is constrained to `0..=255`, and the rows
    /// at one height are concatenated in commitment order before hashing.
    /// This supports odd-width rows, including `BinaryField8` commitments.
    /// The caller must check each row's byte width against its native matrix.
    /// Heights and digests follow [`Self::verify_byte_hash_mmcs_opening`].
    ///
    /// # Errors
    ///
    /// As [`Self::verify_byte_hash_mmcs_opening`] and [`Self::byte_hash_bytes`].
    #[allow(clippy::too_many_arguments)]
    pub fn verify_byte_hash_mmcs_opening_bytes<BF>(
        &mut self,
        hash: ByteHash,
        rows: &[Vec<ExprId>],
        heights: &[usize],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        cap: &[Vec<ExprId>],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        self.verify_byte_hash_mmcs_opening_with(
            rows,
            heights,
            index_bits,
            siblings,
            cap,
            |builder, row| builder.byte_hash_bytes::<BF>(hash, row),
            |builder, left, right| builder.byte_hash_compress::<BF>(hash, left, right),
        )
    }

    /// Authenticates exact serialized byte rows using an explicit circuit host.
    ///
    /// Row widths and native serialization belong to the caller's trusted
    /// matrix geometry. Each byte is checked by the host encoding. Digests
    /// retain sixteen low-first words; all mixed-height injection, index and
    /// cap checks are shared with the prime-field API above.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_byte_hash_mmcs_opening_bytes_with_host<H>(
        &mut self,
        hash: ByteHash,
        rows: &[Vec<ExprId>],
        heights: &[usize],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        cap: &[Vec<ExprId>],
    ) -> Result<(), CircuitBuilderError>
    where
        H: BinaryCircuitHost<F>,
    {
        H::check_hash(hash)?;
        self.verify_byte_hash_mmcs_opening_with(
            rows,
            heights,
            index_bits,
            siblings,
            cap,
            |builder, row| {
                let digest = H::hash_bytes(builder, hash, row)?;
                H::words_from_bytes(builder, &digest)
            },
            |builder, left, right| H::compress(builder, hash, left, right),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_byte_hash_mmcs_opening_with(
        &mut self,
        rows: &[Vec<ExprId>],
        heights: &[usize],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        cap: &[Vec<ExprId>],
        mut hash_rows: impl FnMut(&mut Self, &[ExprId]) -> Result<Vec<ExprId>, CircuitBuilderError>,
        mut compress: impl FnMut(
            &mut Self,
            &[ExprId],
            &[ExprId],
        ) -> Result<Vec<ExprId>, CircuitBuilderError>,
    ) -> Result<(), CircuitBuilderError> {
        let shape_error = |expected: alloc::string::String, got: usize| {
            CircuitBuilderError::NonPrimitiveOpArity {
                op: "MmcsOpening",
                expected,
                got,
            }
        };
        let log_max = index_bits.len();
        if log_max >= usize::BITS as usize {
            return Err(shape_error(
                format!("fewer than {} index bits", usize::BITS),
                log_max,
            ));
        }
        if rows.is_empty() || rows.len() != heights.len() {
            return Err(shape_error(
                format!("one height per opened row ({})", rows.len()),
                heights.len(),
            ));
        }
        let max_height = heights.iter().copied().max().unwrap_or(0);
        if max_height == 0 || log2_ceil_usize(max_height) != log_max {
            return Err(shape_error(
                format!("a tallest matrix of height needing {log_max} index bits"),
                max_height,
            ));
        }
        // As natively: a height `h` sits `k = log_max - ceil(log2(h))` levels up and must be
        // `ceil(max_height / 2^k)`, so each level holds at most one height.
        for &height in heights {
            let reduced = log_max - log2_ceil_usize(height.max(1));
            if height != ((max_height - 1) >> reduced) + 1 {
                return Err(shape_error(
                    format!("a height of ceil({max_height} / 2^k)"),
                    height,
                ));
            }
        }
        let log_heights: Vec<usize> = heights.iter().map(|&h| log2_ceil_usize(h)).collect();
        if !cap.len().is_power_of_two() || cap.len() > 1 << log_max {
            return Err(shape_error(
                format!("a power-of-two cap of at most 2^{log_max} roots"),
                cap.len(),
            ));
        }
        let cap_height = cap.len().trailing_zeros() as usize;
        let levels = log_max - cap_height;
        if siblings.len() != levels {
            return Err(shape_error(format!("{levels} siblings"), siblings.len()));
        }
        if let Some(&short) = log_heights.iter().find(|&&h| h < cap_height) {
            return Err(shape_error(
                format!("matrices at least as tall as the cap layer (log-height {cap_height})"),
                short,
            ));
        }
        for digest in siblings.iter().chain(cap) {
            if digest.len() != DIGEST_LIMBS {
                return Err(shape_error(
                    format!("{DIGEST_LIMBS} limbs per digest"),
                    digest.len(),
                ));
            }
        }

        // The concatenated rows of every matrix of one log-height, in commitment order.
        let rows_at = |log_height: usize| -> Vec<ExprId> {
            rows.iter()
                .zip(&log_heights)
                .filter(|&(_, &h)| h == log_height)
                .flat_map(|(row, _)| row.iter().copied())
                .collect()
        };

        for &bit in index_bits {
            self.assert_bool(bit);
        }
        if !max_height.is_power_of_two() {
            self.assert_bits_at_most(index_bits, max_height - 1);
        }

        let leaf = rows_at(log_max);
        let mut node = hash_rows(self, &leaf)?;
        for (level, (&bit, sibling)) in index_bits.iter().zip(siblings).enumerate() {
            let (left, right): (Vec<ExprId>, Vec<ExprId>) = node
                .iter()
                .zip(sibling)
                .map(|(&current, &other)| {
                    (
                        self.select(bit, other, current),
                        self.select(bit, current, other),
                    )
                })
                .unzip();
            node = compress(self, &left, &right)?;

            let reached = log_max - level - 1;
            if log_heights.contains(&reached) {
                let injected = rows_at(reached);
                let digest = hash_rows(self, &injected)?;
                node = compress(self, &node, &digest)?;
            }
        }

        // The remaining index bits pick the cap root, one multiplexer layer per bit.
        let mut candidates: Vec<Vec<ExprId>> = cap.to_vec();
        for &bit in &index_bits[levels..] {
            candidates = candidates
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| {
                    let digest = pair[0]
                        .iter()
                        .zip(&pair[1])
                        .map(|(&even, &odd)| self.select(bit, odd, even))
                        .collect();
                    self.check_construction_limits()?;
                    Ok(digest)
                })
                .collect::<Result<_, CircuitBuilderError>>()?;
        }
        for (&computed, &expected) in node.iter().zip(&candidates[0]) {
            self.connect(computed, expected);
        }
        self.check_construction_limits()?;
        Ok(())
    }

    /// Constrains the number whose little-endian (boolean) bits are `bits` to be at most `bound`.
    fn assert_bits_at_most(&mut self, bits: &[ExprId], bound: usize) {
        // `above` is whether the bits read so far, from the least significant, exceed `bound`'s
        // bits of the same positions: a set bit over a clear one exceeds it, a clear bit over a
        // set one does not, and equal bits leave the lower positions to decide.
        let mut above = self.define_const(F::ZERO);
        for (i, &bit) in bits.iter().enumerate() {
            let both = self.mul(bit, above);
            above = if bound >> i & 1 == 1 {
                both
            } else {
                let either = self.add(bit, above);
                self.sub(either, both)
            };
        }
        let zero = self.define_const(F::ZERO);
        self.connect(above, zero);
    }

    /// Constrains a single-matrix Merkle opening under `hash`: `leaf` sits at the position
    /// whose little-endian bits are `index_bits`, under a one-root cap `root`.
    ///
    /// [`Self::verify_byte_hash_mmcs_opening`] for one matrix and a one-root cap.
    ///
    /// # Errors
    ///
    /// As [`Self::verify_byte_hash_mmcs_opening`].
    pub fn verify_byte_hash_merkle_path<BF>(
        &mut self,
        hash: ByteHash,
        leaf: &[ExprId],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        root: &[ExprId],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        if index_bits.len() >= usize::BITS as usize {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "MmcsOpening",
                expected: format!("fewer than {} index bits", usize::BITS),
                got: index_bits.len(),
            });
        }
        self.verify_byte_hash_mmcs_opening::<BF>(
            hash,
            &[leaf.to_vec()],
            &[1 << index_bits.len()],
            index_bits,
            siblings,
            &[root.to_vec()],
        )
    }

    /// [`Self::verify_byte_hash_merkle_path`] under Keccak-256.
    ///
    /// # Errors
    ///
    /// As [`Self::verify_byte_hash_merkle_path`].
    pub fn verify_keccak_merkle_path<BF>(
        &mut self,
        leaf: &[ExprId],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        root: &[ExprId],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        self.verify_byte_hash_merkle_path::<BF>(
            ByteHash::Keccak256,
            leaf,
            index_bits,
            siblings,
            root,
        )
    }

    /// [`Self::verify_byte_hash_merkle_path`] under BLAKE3.
    ///
    /// # Errors
    ///
    /// As [`Self::verify_byte_hash_merkle_path`].
    pub fn verify_blake3_merkle_path<BF>(
        &mut self,
        leaf: &[ExprId],
        index_bits: &[ExprId],
        siblings: &[Vec<ExprId>],
        root: &[ExprId],
    ) -> Result<(), CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        self.verify_byte_hash_merkle_path::<BF>(ByteHash::Blake3, leaf, index_bits, siblings, root)
    }

    // ═══════════════════════════════════════════════════════════════════
    // Poseidon2b byte hash — Phase 1 stubs (Phase 2 implements in-circuit)
    // ═══════════════════════════════════════════════════════════════════
    //
    // The in-circuit Poseidon2b byte hash must replicate
    // `sahyadri_fri_binius::poseidon2b_hasher::Poseidon2bFieldHash::hash_iter`
    // and `Poseidon2bFieldCompress::compress` semantics exactly. Each byte-digest
    // requires multiple Poseidon2b permutations — Phase 2 is 3-5 days.

    fn poseidon2b_limbs<BF>(
        &mut self,
        message: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        self.poseidon2b_packed_bytes::<BF>(message, 2 * message.len())
    }

    fn poseidon2b_packed_bytes<BF>(
        &mut self,
        message: &[ExprId],
        _message_bytes: usize,
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        // 8 limbs = 1 field element (16 bytes)
        const LIMBS_PER_FIELD: usize = 8;
        let zero_limb = self.define_const(F::ZERO);
        let field_count = (message.len() + LIMBS_PER_FIELD - 1) / LIMBS_PER_FIELD;

        // Pad to multiple of LIMBS_PER_FIELD with zero limbs
        let padded: Vec<ExprId> = (0..field_count * LIMBS_PER_FIELD)
            .map(|i| message.get(i).copied().unwrap_or(zero_limb))
            .collect();

        // Split into fields (8 limbs each)
        let fields: Vec<&[ExprId]> = padded.chunks(LIMBS_PER_FIELD).collect();
        let zero_field: Vec<ExprId> = alloc::vec![zero_limb; LIMBS_PER_FIELD];

        let (mut acc_d0, mut acc_d1) = if fields.is_empty() {
            let d0 = self.add_poseidon2b_compress(&zero_field)?;
            let d1 = self.add_poseidon2b_compress(&zero_field)?;
            (d0, d1)
        } else if fields.len() == 1 {
            let f0 = fields[0];
            let mut in0 = f0.to_vec();
            in0.extend_from_slice(&zero_field);
            let d0 = self.add_poseidon2b_compress(&in0)?;
            let mut in1 = zero_field.clone();
            in1.extend_from_slice(f0);
            let d1 = self.add_poseidon2b_compress(&in1)?;
            (d0, d1)
        } else {
            let f0 = fields[0];
            let mut in0 = f0.to_vec();
            in0.extend_from_slice(&zero_field);
            let d0 = self.add_poseidon2b_compress(&in0)?;
            let mut in1 = zero_field.clone();
            in1.extend_from_slice(f0);
            let d1 = self.add_poseidon2b_compress(&in1)?;
            (d0, d1)
        };

        if fields.len() > 1 {
            let mut i = 1;
            while i + 1 < fields.len() {
                let mut in_d0 = acc_d0.clone();
                in_d0.extend_from_slice(fields[i]);
                acc_d0 = self.add_poseidon2b_compress(&in_d0)?;

                let mut in_d1 = acc_d1.clone();
                in_d1.extend_from_slice(fields[i + 1]);
                acc_d1 = self.add_poseidon2b_compress(&in_d1)?;
                i += 2;
            }
            if i < fields.len() {
                let mut in_d0 = acc_d0.clone();
                in_d0.extend_from_slice(fields[i]);
                acc_d0 = self.add_poseidon2b_compress(&in_d0)?;

                let mut in_d1 = acc_d1.clone();
                in_d1.extend_from_slice(&zero_field);
                acc_d1 = self.add_poseidon2b_compress(&in_d1)?;
            }
        }

        // Return 16 limbs (d0 8 limbs + d1 8 limbs)
        let mut result = acc_d0;
        result.extend_from_slice(&acc_d1);
        Ok(result)
    }

    fn poseidon2b_compress_digests<BF>(
        &mut self,
        left: &[ExprId],
        right: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError>
    where
        BF: PrimeField64,
        F: ExtensionField<BF>,
    {
        // Each digest is 16 limbs = 32 bytes = 2 fields (d0, d1)
        const LIMBS_PER_FIELD: usize = 8;
        const DIGEST_LIMBS: usize = 16;
        for digest in [left, right] {
            if digest.len() != DIGEST_LIMBS {
                return Err(CircuitBuilderError::NonPrimitiveOpArity {
                    op: "Poseidon2bCompress",
                    expected: alloc::format!("{DIGEST_LIMBS} limbs per digest"),
                    got: digest.len(),
                });
            }
        }
        // c0 = compress(left[0..8], right[0..8])
        let mut in0 = left[..LIMBS_PER_FIELD].to_vec();
        in0.extend_from_slice(&right[..LIMBS_PER_FIELD]);
        let c0 = self.add_poseidon2b_compress(&in0)?;
        // c1 = compress(left[8..16], right[8..16])
        let mut in1 = left[LIMBS_PER_FIELD..].to_vec();
        in1.extend_from_slice(&right[LIMBS_PER_FIELD..]);
        let c1 = self.add_poseidon2b_compress(&in1)?;

        let mut result = c0;
        result.extend_from_slice(&c1);
        Ok(result)
    }
}


#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::CircuitBuilder;

    #[test]
    fn cap_selection_checks_each_digest_pair() {
        use p3_binary_field::Poly64;

        use crate::CircuitConstructionLimits;

        let mut b = CircuitBuilder::<Poly64>::with_construction_limits(CircuitConstructionLimits {
            max_expression_nodes: 600,
            max_pending_connects: 1024,
            max_non_primitive_calls: 1024,
            max_non_primitive_slots: 4096,
        })
        .unwrap();
        let bits = b.alloc_private_input_array::<5>("cap index");
        let cap: Vec<_> = (0..32)
            .map(|_| b.alloc_private_input_array::<16>("cap root").to_vec())
            .collect();
        let result = b.verify_byte_hash_mmcs_opening_with(
            &[vec![ExprId::ZERO]],
            &[32],
            &bits,
            &[],
            &cap,
            |_, _| Ok(vec![ExprId::ZERO; 16]),
            |_, _, _| unreachable!("leaf-layer cap has no sibling compression"),
        );
        assert!(matches!(
            result,
            Err(CircuitBuilderError::ConstructionLimitExceeded { .. })
        ));
        assert!(b.construction_usage().unwrap().expression_nodes <= 648);
        assert!(b.build().is_err());
    }

    #[test]
    fn the_index_bound_admits_exactly_the_indices_up_to_it() {
        for bound in 0..8usize {
            let mut builder = CircuitBuilder::<BabyBear>::new();
            let bits: Vec<ExprId> = (0..3).map(|_| builder.public_input()).collect();
            builder.assert_bits_at_most(&bits, bound);
            let circuit = builder.build().unwrap();
            for index in 0..8usize {
                let public: Vec<BabyBear> = (0..3)
                    .map(|i| BabyBear::from_bool(index >> i & 1 == 1))
                    .collect();
                let mut runner = circuit.runner();
                let runs = runner.set_public_inputs(&public).is_ok() && runner.run().is_ok();
                assert_eq!(runs, index <= bound, "index {index}, bound {bound}");
            }
        }
    }
}
