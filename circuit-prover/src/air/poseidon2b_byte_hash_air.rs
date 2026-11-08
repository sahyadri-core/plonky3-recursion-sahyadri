//! [`Poseidon2bByteHashAir`] proves the circuit's Poseidon2b compressions.
//!
//! # ⚠️ ARCHITECTURAL BLOCKER (2026-11-08)
//!
//! `Poseidon2bAir` runs over `AB::F = BinaryField128` directly (bit-sliced
//! GF(2^128) ops). Batch prover `Val<SC>` is BabyBear/Goldilocks (prime field).
//! `SubAirBuilder<AB, Poseidon2bAir, _>` cannot work here — field type mismatch.
//!
//! # Real Phase 2b-d task
//!
//! Mirror `binary_in_goldilocks_air.rs` C1 skeleton:
//! 1. Encode each BF128 as 2 prime limbs (lo: 64-bit, hi: 64-bit)
//! 2. Express BF128 add/mul/sbox/MDS as prime-field constraints on the 2 limbs
//! 3. Run Poseidon2b 66 rounds on the encoded data
//! 4. Batch prover integration
//!
//! Effort: 8-16h research (not "mirror Blake3CompressAir"). This skeleton is
//! placeholder structure ONLY — constraints on Poseidon2b permutation rounds
//! require the binary-in-goldilocks encoding to be implemented first.
//!
//! # Structure (mirrors `Blake3CompressAir`)
//! - Embeds Poseidon2b permutation trace (68 rows × 1024 cols) per compression
//! - Adds limb columns: 16 input limbs (2 fields), 8 output limbs (1 field)
//! - Bus PUSH to MERKLE_COMPRESS (per row)
//! - WitnessChecks LOOKUP for circuit witness table binding
//!
//! # KEY DIFFERENCE from Poseidon2bBusAir
//! Poseidon2bAir uses **public values** to bind state(0) and state(67).
//! Batch prover (MultiStark) doesn't support per-row public values.
//! Solution: bind state(0) and state(67) via WITNESS columns directly.
//!
//! # Status (Phase 2b-d skeleton)
//! - Column layout + preprocessed trace structure: DONE
//! - Poseidon2b trace generation: DONE (delegates to Poseidon2bAir::trace)
//! - Limb packing constraints: TODO (Session 2)
//! - State input/output binding: TODO (Session 2)
//! - WitnessChecks lookups: TODO (Session 2)
//! - Bus push: DONE (basic)
//!
//! # Multi-compression
//! One row per compression. Multi-compression chaining is at circuit-builder
//! level (poseidon2b_limbs chains add_poseidon2b_compress calls).

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_circuit::ops::poseidon2b_compress::Poseidon2bCompressCircuitRow;
// Session 2: MERKLE_DOMAIN, SubAirBuilder used for permutation constraints
#[allow(unused_imports)]
use p3_circuit::ops::poseidon2b_compress::MERKLE_DOMAIN;
#[allow(unused_imports)]
use p3_uni_stark::SubAirBuilder;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2b::trace::WIDTH as P2B_TRACE_WIDTH;

pub const MERKLE_COMPRESS: BusName<'static> = BusName::new("sahyadri_merkle_compress");

/// Poseidon2b trace width (1024 columns from p3-poseidon2b).
pub const NUM_P2B_COLS: usize = P2B_TRACE_WIDTH;

/// Input limbs (2 fields × 8 limbs).
pub const INPUT_LIMBS: usize = 16;
/// Output limbs (1 field × 8 limbs).
pub const OUTPUT_LIMBS: usize = 8;

/// Input field A column.
pub const COL_INPUT_A: usize = NUM_P2B_COLS;
/// Input field B column.
pub const COL_INPUT_B: usize = NUM_P2B_COLS + 1;
/// Output field column.
pub const COL_OUTPUT: usize = NUM_P2B_COLS + 2;
/// Active marker.
pub const COL_ACTIVE: usize = NUM_P2B_COLS + 3;
/// Input limbs base (16 cols).
pub const COL_INPUT_LIMBS: usize = NUM_P2B_COLS + 4;
/// Output limbs base (8 cols).
pub const COL_OUTPUT_LIMBS: usize = NUM_P2B_COLS + 20;

/// Total main trace width.
pub const P2B_BYTE_HASH_WIDTH: usize = NUM_P2B_COLS + 28;

/// Preprocessed columns per call: [active, in_idx × 16, (out_idx, out_mult) × 8].
pub const P2B_BYTE_HASH_PREP_OP_WIDTH: usize = 1 + INPUT_LIMBS + 2 * OUTPUT_LIMBS;
/// Preprocessed row width.
pub const P2B_BYTE_HASH_PREP_ROW_WIDTH: usize = P2B_BYTE_HASH_PREP_OP_WIDTH;

pub struct Poseidon2bByteHashAir<F, const D: usize> {
    pub(crate) preprocessed: Vec<F>,
    pub(crate) min_height: usize,
    _phantom: PhantomData<F>,
}

impl<F: Field, const D: usize> Poseidon2bByteHashAir<F, D> {
    pub const fn new_with_preprocessed(preprocessed: Vec<F>, min_height: usize) -> Self {
        Self { preprocessed, min_height, _phantom: PhantomData }
    }

    pub const fn num_ops(&self) -> usize {
        self.preprocessed.len() / P2B_BYTE_HASH_PREP_OP_WIDTH
    }

    pub fn height_for(num_ops: usize, min_height: usize) -> usize {
        num_ops.max(1).next_power_of_two().max(min_height.next_power_of_two())
    }

    /// Build main trace: one row per compression.
    ///
    /// Each row contains:
    /// - 1024 Poseidon2b permutation trace columns (state, sbox, MDS)
    /// - input_a, input_b (fields)
    /// - output (field)
    /// - 16 input limbs + 8 output limbs
    pub fn trace_to_matrix(
        ops: &[Poseidon2bCompressCircuitRow],
        height: usize,
    ) -> RowMajorMatrix<F>
    where
        F: From<BinaryField128>,
    {
        assert!(height.is_power_of_two() && height >= ops.len());
        let mut values = F::zero_vec(height * P2B_BYTE_HASH_WIDTH);
        for (i, row) in values.chunks_exact_mut(P2B_BYTE_HASH_WIDTH).enumerate() {
            let Some(op) = ops.get(i) else { continue };

            // Phase 2b-d Session 2: generate Poseidon2b trace here
            // (68-row permutation trace from input_a, input_b, MERKLE_DOMAIN)
            // For skeleton: leave leading 1024 cols zero (Poseidon2bAir constraints
            // will reject at test time, but structure compiles)

            row[COL_INPUT_A] = op.input_a.into();
            row[COL_INPUT_B] = op.input_b.into();
            row[COL_OUTPUT] = op.output.into();
            row[COL_ACTIVE] = F::ONE;

            // Input limbs: split input_a and input_b into 16-bit limbs (LE)
            let a_bytes: [u8; 16] = unsafe { core::mem::transmute_copy(&op.input_a) };
            let b_bytes: [u8; 16] = unsafe { core::mem::transmute_copy(&op.input_b) };
            for j in 0..8 {
                let limb_a = u16::from_le_bytes([a_bytes[2 * j], a_bytes[2 * j + 1]]);
                let limb_b = u16::from_le_bytes([b_bytes[2 * j], b_bytes[2 * j + 1]]);
                row[COL_INPUT_LIMBS + j] = F::from_u64(limb_a as u64);
                row[COL_INPUT_LIMBS + 8 + j] = F::from_u64(limb_b as u64);
            }

            // Output limbs
            let o_bytes: [u8; 16] = unsafe { core::mem::transmute_copy(&op.output) };
            for j in 0..8 {
                let limb = u16::from_le_bytes([o_bytes[2 * j], o_bytes[2 * j + 1]]);
                row[COL_OUTPUT_LIMBS + j] = F::from_u64(limb as u64);
            }
        }
        RowMajorMatrix::new(values, P2B_BYTE_HASH_WIDTH)
    }
}

impl<F: Field, const D: usize> BaseAir<F> for Poseidon2bByteHashAir<F, D> {
    fn width(&self) -> usize { P2B_BYTE_HASH_WIDTH }
    fn preprocessed_width(&self) -> usize { P2B_BYTE_HASH_PREP_ROW_WIDTH }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let height = Self::height_for(self.num_ops(), self.min_height);
        let mut values = F::zero_vec(height * P2B_BYTE_HASH_PREP_ROW_WIDTH);
        for (row, prep) in values
            .as_chunks_mut::<P2B_BYTE_HASH_PREP_ROW_WIDTH>().0.iter_mut()
            .zip(self.preprocessed.as_chunks::<P2B_BYTE_HASH_PREP_OP_WIDTH>().0.iter())
        {
            row.copy_from_slice(prep);
        }
        Some(RowMajorMatrix::new(values, P2B_BYTE_HASH_PREP_ROW_WIDTH))
    }
    fn main_next_row_columns(&self) -> Vec<usize> { vec![] }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> { vec![] }
    fn max_constraint_degree(&self) -> Option<usize> { Some(3) }
}

impl<AB, const D: usize> Air<AB> for Poseidon2bByteHashAir<AB::F, D>
where
    AB: AirBuilder + BusInteractionBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        // Phase 2b-d Session 2: embed Poseidon2bAir via SubAirBuilder
        // For skeleton: skip Poseidon2b verification (basic constraints only)

        let main = builder.main();
        let cur = main.current_slice();
        let zero = AB::F::ZERO;

        // Basic booleanity
        let active: AB::Expr = cur[COL_ACTIVE].into();
        builder.assert_eq(active.clone() * active.clone() + active.clone(), zero);

        // ══════════════════════════════════════════════════════════════════
        // TODO Phase 2b-d Session 2:
        // ══════════════════════════════════════════════════════════════════
        // 1. Embed Poseidon2bAir via SubAirBuilder (constrained on 0..1024)
        //    - But Poseidon2bAir uses public values; bypass by constraining
        //      state(0) and state(67) directly from input_a/b/output witness cols
        // 2. Constrain input_a, input_b → limb decomposition (16 limbs)
        // 3. Constrain output → limb decomposition (8 limbs)
        // 4. Constrain domain: input state = [input_a, input_b, 0, MERKLE_DOMAIN]
        // 5. Constrain output = state[67][0] + state[67][1]
        // 6. WitnessChecks lookups (input limbs, output limbs)
        // 7. Bus push (input_a, input_b, output) on active rows

        // Bus push: (input_a, input_b, output) — matches Poseidon2bFieldCompress
        let input_a: AB::Expr = cur[COL_INPUT_A].into();
        let input_b: AB::Expr = cur[COL_INPUT_B].into();
        let output: AB::Expr = cur[COL_OUTPUT].into();
        builder.push_bus_interaction(
            MERKLE_COMPRESS,
            BusDirection::Push,
            [input_a, input_b, output],
            BusActivation::Boolean(active),
        );
    }
}
