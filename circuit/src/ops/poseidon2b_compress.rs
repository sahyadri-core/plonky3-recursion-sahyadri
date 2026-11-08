//! Poseidon2b field compression — circuit NonPrimitiveOp.
//!
//! One NPO = one `field_compress(a, b) → c` where:
//!   `compress(a, b) = state[0] + state[1]` after
//!   `poseidon2b_permutation([a, b, 0, MERKLE_DOMAIN])`.
//!
//! Byte hash (`Poseidon2bFieldHash::hash_iter`) is chained at the
//! circuit-builder level via multiple `add_poseidon2b_compress` calls.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;

use p3_binary_field::BinaryField128;
use p3_field::Field;
use p3_poseidon2b::poseidon2b_permutation;

use crate::builder::{CircuitBuilderError, NonPrimitiveOperationData};
use crate::errors::CircuitError;
use crate::ops::keccak_perm::{limb_fn, LimbFn};
use crate::ops::{
    ExecutionContext, NpoConfig, NpoTypeId, NonPrimitiveExecutor, Op, OpStateMap,
    PreprocessedWriter,
};
use crate::tables::{NonPrimitiveTrace, TraceGeneratorFn};
use crate::types::{ExprId, WitnessId};
use crate::{NpoCircuitPlugin, NpoLoweringContext};

/// Input limbs: 2 fields × 8 limbs (16-bit each).
pub const P2B_INPUT_LIMBS: usize = 16;
/// Output limbs: 1 field × 8 limbs.
pub const P2B_OUTPUT_LIMBS: usize = 8;

/// Merkle domain tag matching `sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN`.
pub const MERKLE_DOMAIN: u128 = 0x4D45_524B_4C45_0001;

/// Native field-level Poseidon2b compression.
#[inline]
pub fn native_compress(a: BinaryField128, b: BinaryField128) -> BinaryField128 {
    let mut state = [
        a,
        b,
        BinaryField128::from_le_bytes([0u8; 16]),
        BinaryField128::from_le_bytes(MERKLE_DOMAIN.to_le_bytes()),
    ];
    poseidon2b_permutation(&mut state);
    state[0] + state[1]
}

/// One compression captured during execution.
#[derive(Debug, Clone)]
pub struct Poseidon2bCompressCircuitRow {
    pub input_wids: Vec<WitnessId>,
    pub output_wids: Vec<WitnessId>,
    pub input_a: BinaryField128,
    pub input_b: BinaryField128,
    pub output: BinaryField128,
}

/// Execution state collecting every compression.
#[derive(Debug, Default)]
pub struct Poseidon2bCompressExecutionState {
    pub rows: Vec<Poseidon2bCompressCircuitRow>,
}

// ─── Executor ───

pub struct Poseidon2bCompressExecutor<F> {
    op_type: NpoTypeId,
    limb_fn: LimbFn<F>,
}

impl<F> Clone for Poseidon2bCompressExecutor<F> {
    fn clone(&self) -> Self {
        Self {
            op_type: self.op_type.clone(),
            limb_fn: Arc::clone(&self.limb_fn),
        }
    }
}

impl<F: Field> core::fmt::Debug for Poseidon2bCompressExecutor<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Poseidon2bCompressExecutor")
            .field("op_type", &self.op_type)
            .finish()
    }
}

fn check_layout(
    op_type: &NpoTypeId,
    inputs: &[Vec<WitnessId>],
    outputs: &[Vec<WitnessId>],
) -> Result<(), CircuitError> {
    if inputs.len() != 1 || inputs[0].len() != P2B_INPUT_LIMBS {
        return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
            op: op_type.clone(),
            expected: alloc::format!("1 input group with {P2B_INPUT_LIMBS} limbs"),
            got: inputs.first().map_or(0, Vec::len),
        });
    }
    if outputs.len() != 1 || outputs[0].len() != P2B_OUTPUT_LIMBS {
        return Err(CircuitError::NonPrimitiveOpLayoutMismatch {
            op: op_type.clone(),
            expected: alloc::format!("1 output group with {P2B_OUTPUT_LIMBS} limbs"),
            got: outputs.first().map_or(0, Vec::len),
        });
    }
    Ok(())
}

impl<F: Field + Send + Sync + 'static> NonPrimitiveExecutor<F> for Poseidon2bCompressExecutor<F> {
    fn execute(
        &self,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        ctx: &mut ExecutionContext<'_, F>,
    ) -> Result<(), CircuitError> {
        check_layout(&self.op_type, inputs, outputs)?;

        let mut a_bytes = [0u8; 16];
        let mut b_bytes = [0u8; 16];
        for i in 0..8 {
            let va = ctx.get_witness(inputs[0][i])?;
            let vb = ctx.get_witness(inputs[0][8 + i])?;
            let la = (self.limb_fn)(&va).ok_or_else(|| {
                CircuitError::InvalidNonPrimitiveOpInput {
                    op: self.op_type.clone(),
                    witness_id: inputs[0][i],
                    expected: "a base-field integer below 2^16",
                    got: alloc::string::ToString::to_string(&va),
                }
            })?;
            let lb = (self.limb_fn)(&vb).ok_or_else(|| {
                CircuitError::InvalidNonPrimitiveOpInput {
                    op: self.op_type.clone(),
                    witness_id: inputs[0][8 + i],
                    expected: "a base-field integer below 2^16",
                    got: alloc::string::ToString::to_string(&vb),
                }
            })?;
            a_bytes[2 * i] = (la & 0xFF) as u8;
            a_bytes[2 * i + 1] = ((la >> 8) & 0xFF) as u8;
            b_bytes[2 * i] = (lb & 0xFF) as u8;
            b_bytes[2 * i + 1] = ((lb >> 8) & 0xFF) as u8;
        }
        let a = BinaryField128::from_le_bytes(a_bytes);
        let b = BinaryField128::from_le_bytes(b_bytes);
        let c = native_compress(a, b);
        let c_bytes: [u8; 16] = unsafe { core::mem::transmute_copy(&c) };

        for i in 0..8 {
            let limb = u16::from_le_bytes([c_bytes[2 * i], c_bytes[2 * i + 1]]);
            ctx.set_witness(outputs[0][i], F::from_u16(limb))?;
        }

        let state = ctx.get_op_state_mut::<Poseidon2bCompressExecutionState>(&self.op_type);
        state.rows.push(Poseidon2bCompressCircuitRow {
            input_wids: inputs[0].clone(),
            output_wids: outputs[0].clone(),
            input_a: a,
            input_b: b,
            output: c,
        });
        Ok(())
    }

    fn op_type(&self) -> &NpoTypeId {
        &self.op_type
    }

    fn preprocess(
        &self,
        inputs: &[Vec<WitnessId>],
        outputs: &[Vec<WitnessId>],
        preprocessed: &mut dyn PreprocessedWriter<F>,
    ) -> Result<(), CircuitError> {
        check_layout(&self.op_type, inputs, outputs)?;
        preprocessed.register_non_primitive_preprocessed_no_read(&self.op_type, &[F::ONE]);
        preprocessed.register_non_primitive_witness_reads(&self.op_type, &inputs[0])?;
        for &wid in &outputs[0] {
            preprocessed.register_non_primitive_output_index(&self.op_type, &[wid]);
            preprocessed.register_non_primitive_preprocessed_no_read(&self.op_type, &[F::ONE]);
        }
        Ok(())
    }

    fn num_exposed_outputs(&self) -> Option<usize> {
        Some(1)
    }

    fn boxed(&self) -> Box<dyn NonPrimitiveExecutor<F>> {
        Box::new(self.clone())
    }
}

// ─── Trace ───

#[derive(Debug, Clone)]
pub struct Poseidon2bCompressTrace {
    pub operations: Vec<Poseidon2bCompressCircuitRow>,
}

impl<CF> NonPrimitiveTrace<CF> for Poseidon2bCompressTrace {
    fn op_type(&self) -> NpoTypeId {
        NpoTypeId::poseidon2b_compress()
    }
    fn rows(&self) -> usize {
        self.operations.len()
    }
    fn as_any(&self) -> &dyn core::any::Any {
        self
    }
    fn boxed_clone(&self) -> Box<dyn NonPrimitiveTrace<CF>> {
        Box::new(self.clone())
    }
}

pub fn generate_poseidon2b_compress_trace<F>(
    op_states: &OpStateMap,
) -> Result<Option<Box<dyn NonPrimitiveTrace<F>>>, CircuitError> {
    let Some(state) = op_states
        .get(&NpoTypeId::poseidon2b_compress())
        .and_then(|s| s.downcast_ref::<Poseidon2bCompressExecutionState>())
    else {
        return Ok(None);
    };
    if state.rows.is_empty() {
        return Ok(None);
    }
    Ok(Some(Box::new(Poseidon2bCompressTrace {
        operations: state.rows.clone(),
    })))
}

// ─── Config + Plugin ───

#[derive(Debug, Clone)]
pub struct Poseidon2bCompressConfig;

pub(crate) struct Poseidon2bCompressCircuitPlugin<F: Field> {
    trace_gen: TraceGeneratorFn<F>,
    limb_fn: LimbFn<F>,
}

impl<F: Field> core::fmt::Debug for Poseidon2bCompressCircuitPlugin<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Poseidon2bCompressCircuitPlugin").finish()
    }
}

impl<F: Field> NpoCircuitPlugin<F> for Poseidon2bCompressCircuitPlugin<F> {
    fn type_id(&self) -> NpoTypeId {
        NpoTypeId::poseidon2b_compress()
    }

    fn lower(
        &self,
        data: &NonPrimitiveOperationData<F>,
        output_exprs: &[(u32, ExprId)],
        ctx: &mut NpoLoweringContext<'_, F>,
    ) -> Result<Op<F>, CircuitBuilderError> {
        if data.params.is_some() {
            return Err(CircuitBuilderError::InvalidNonPrimitiveOpConfiguration {
                op: data.op_type.clone(),
            });
        }
        if data.input_exprs.len() != P2B_INPUT_LIMBS
            || data.input_exprs.iter().any(|slot| slot.len() != 1)
        {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "Poseidon2bCompress",
                expected: alloc::format!("{P2B_INPUT_LIMBS} single-limb input slots"),
                got: data.input_exprs.len(),
            });
        }
        if output_exprs.len() != P2B_OUTPUT_LIMBS {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "Poseidon2bCompress",
                expected: alloc::format!("{P2B_OUTPUT_LIMBS} output limbs"),
                got: output_exprs.len(),
            });
        }

        for (_, expr) in output_exprs {
            ctx.ensure_witness_id(*expr);
        }
        let input_wids = data
            .input_exprs
            .iter()
            .enumerate()
            .map(|(i, slot)| {
                ctx.resolve_witness_id(slot[0], || {
                    alloc::format!("Poseidon2bCompress input limb {i}")
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut ordered: Vec<(u32, ExprId)> = output_exprs.to_vec();
        ordered.sort_unstable_by_key(|&(index, _)| index);
        if ordered
            .iter()
            .enumerate()
            .any(|(position, &(index, _))| index as usize != position)
        {
            return Err(CircuitBuilderError::MalformedNonPrimitiveOutputs {
                op_id: data.op_id,
                details: "Poseidon2b output limbs must be indexed 0..8 without gaps".into(),
            });
        }
        let output_wids = ordered
            .iter()
            .map(|&(index, expr)| {
                ctx.resolve_witness_id(expr, || {
                    alloc::format!("Poseidon2bCompress output limb {index}")
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Op::NonPrimitiveOpWithExecutor {
            inputs: alloc::vec![input_wids],
            outputs: alloc::vec![output_wids],
            executor: Box::new(Poseidon2bCompressExecutor {
                op_type: NpoTypeId::poseidon2b_compress(),
                limb_fn: Arc::clone(&self.limb_fn),
            }),
            op_id: data.op_id,
        })
    }

    fn trace_generator(&self) -> TraceGeneratorFn<F> {
        self.trace_gen
    }

    fn config(&self) -> NpoConfig {
        NpoConfig::new(Poseidon2bCompressConfig)
    }
}

unsafe impl<F: Field> Send for Poseidon2bCompressCircuitPlugin<F> {}
unsafe impl<F: Field> Sync for Poseidon2bCompressCircuitPlugin<F> {}

// ─── Builder API ───

impl<F> crate::CircuitBuilder<F>
where
    F: Field + Eq + core::hash::Hash,
{
    /// Enables Poseidon2b field compression in a circuit over `F ⊇ BF`.
    pub fn enable_poseidon2b_compress<BF>(&mut self)
    where
        BF: p3_field::PrimeField64,
        F: p3_field::ExtensionField<BF>,
    {
        assert!(
            BF::ORDER_U64 > 1 << 16,
            "Poseidon2b limbs need a base field with more than 2^16 elements"
        );
        self.register_npo(Poseidon2bCompressCircuitPlugin {
            trace_gen: generate_poseidon2b_compress_trace::<F>,
            limb_fn: limb_fn::<BF, F>(),
        });
    }

    /// One field-level compression: 16 input limbs (2 fields) → 8 output limbs (1 field).
    pub fn add_poseidon2b_compress(
        &mut self,
        input: &[ExprId],
    ) -> Result<Vec<ExprId>, CircuitBuilderError> {
        let op_type = NpoTypeId::poseidon2b_compress();
        self.ensure_op_enabled(&op_type)?;
        if input.len() != P2B_INPUT_LIMBS {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "Poseidon2bCompress",
                expected: alloc::format!("{P2B_INPUT_LIMBS} input limbs"),
                got: input.len(),
            });
        }
        let (_, _, outputs) = self.push_non_primitive_op_with_outputs(
            op_type,
            input.iter().map(|&limb| alloc::vec![limb]).collect(),
            alloc::vec![Some("poseidon2b_compress_out"); P2B_OUTPUT_LIMBS],
            None,
            "poseidon2b_compress",
        );
        Ok(outputs
            .into_iter()
            .map(|out| out.expect("every Poseidon2b output limb is requested"))
            .collect())
    }
}
