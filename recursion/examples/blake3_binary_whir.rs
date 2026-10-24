//! Prove and verify a Blake3 compression on GF(2^128) via WHIR.
//!
//! cargo run -p p3-recursion --profile optimized --features parallel \
//!     --example blake3_binary_whir

use std::error::Error;
use std::time::Instant;

use p3_binary_field::BinaryField128;
use p3_blake3_air::{Blake3BinaryAir, Blake3CompressionInput, generate_binary_trace_rows};
use p3_circuit::ops::ByteHash;
use p3_matrix::Matrix;
use p3_recursion::artifact::{
    BinaryNativeVerifierSpec, BinaryNativeWhirAuthority, BinaryNativeWhirPcsParameters,
};
use p3_recursion::verifier::VerifierLimits;
use p3_whir::{FoldingFactor, ProtocolParameters, SecurityAssumption};
use p3_air::WindowAccess;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

type F = BinaryField128;

/// Wrapper AIR that pads the Blake3 binary width (11,536) up to a power of two
/// (16,384) so WHIR's arity check sees a power-of-two width. The extra columns
/// are unconstrained; the inner AIR only reads the first `INNER_WIDTH` columns.
struct PaddedBlake3Air {
    inner: Blake3BinaryAir,
}

const PADDED_WIDTH: usize = 16_384;

impl<F> p3_air::BaseAir<F> for PaddedBlake3Air {
    fn width(&self) -> usize {
        PADDED_WIDTH
    }
    fn num_public_values(&self) -> usize {
        <Blake3BinaryAir as p3_air::BaseAir<F>>::num_public_values(&self.inner)
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        <Blake3BinaryAir as p3_air::BaseAir<F>>::main_next_row_columns(&self.inner)
    }
}

impl<AB: p3_air::AirBuilder> p3_air::Air<AB> for PaddedBlake3Air {
    fn eval(&self, _builder: &mut AB) {
        // The inner AIR is evaluated over the original 11,536 columns.
        // Full constraint wiring is handled by the inner AIR; this wrapper
        // only exists to make the declared width power-of-two for WHIR.
        self.inner.eval(_builder);
        let _ = _builder.main().current_slice()[0];
    }
}


/// Pads a row-major matrix to the given width by appending zero columns.
fn pad_trace_width(
    trace: p3_matrix::dense::RowMajorMatrix<F>,
    padded_width: usize,
) -> p3_matrix::dense::RowMajorMatrix<F> {
    use p3_matrix::Matrix;
    let height = trace.height();
    let width = trace.width();
    if width == padded_width {
        return trace;
    }
    let mut padded = vec![F::from_le_bytes([0u8; 16]); height * padded_width];
    for r in 0..height {
        for c in 0..width {
            padded[r * padded_width + c] = trace.get(r, c).expect("in bounds");
        }
    }
    p3_matrix::dense::RowMajorMatrix::new(padded, padded_width)
}


fn verifier_limits() -> VerifierLimits {
    VerifierLimits {
        max_metadata_entries: 1 << 20,
        ..Default::default()
    }
}

const SINGLE_BLOCK_FLAGS: u32 = 1 | 2 | 8;
const BLAKE3_IV: [u32; 8] = [
    0x6A09_E667, 0xBB67_AE85, 0x3C6E_F372, 0xA54F_F53A,
    0x510E_527F, 0x9B05_688C, 0x1F83_D9AB, 0x5BE0_CD19,
];

fn single_block_input(message: &[u8]) -> Blake3CompressionInput {
    let mut bytes = [0u8; 64];
    bytes[..message.len()].copy_from_slice(message);
    Blake3CompressionInput {
        chaining_value: BLAKE3_IV,
        block: core::array::from_fn(|i| {
            u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap())
        }),
        counter: 0,
        block_len: message.len() as u32,
        flags: SINGLE_BLOCK_FLAGS,
    }
}

const fn protocol() -> ProtocolParameters {
    ProtocolParameters {
        security_level: 8,
        pow_bits: 0,
        round_log_inv_rates: vec![],
        folding_factor: FoldingFactor::Constant(1),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 1,
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    // Four distinct single-block inputs -> height 4, width 11,536.
    let inputs = vec![
        single_block_input(b""),
        single_block_input(b"a"),
        single_block_input(b"hello"),
        single_block_input(b"world"),
    ];

    let trace = generate_binary_trace_rows::<F>(inputs, 0);
    let height = trace.height();
    let raw_width = trace.width();
    println!("Trace: {} rows x {} cols", height, raw_width);

    // WHIR requires the total number of multilinear variables to be a power of two.
    // We pad the width to the next power of two (11536 -> 16384) with zero columns.
    // The Blake3 AIR only constrains the first 11,536 columns; the padding is unconstrained.
    let padded_width = raw_width.next_power_of_two();
    let total_cells = height * padded_width;
    let log_height = p3_util::log2_strict_usize(height * padded_width);
    println!("Padded width = {}, total cells = {}, log_height = {}", padded_width, total_cells, log_height);

    let padded_trace = pad_trace_width(trace, padded_width);

    let spec = BinaryNativeVerifierSpec {
        main: BinaryNativeWhirPcsParameters::<F>::new(
            log_height,
            protocol(),
            ByteHash::Keccak256,
            0,
        )?,
        preprocessed: None,
        transcript_hash: ByteHash::Keccak256,
        initial_bytes: b"blake3-binary-poc-v1".to_vec(),
        sumcheck_pow_bits: 0,
        max_tau_draws: 64,
        security_bits: 8,
    };

    let (prover, authority) = BinaryNativeWhirAuthority::<F, _>::setup(
        vec![PaddedBlake3Air { inner: Blake3BinaryAir::default() }],
        vec![log_height],
        spec,
        &verifier_limits(),
    )?;

    let expected: Vec<Vec<F>> = vec![vec![]];

    let start = Instant::now();
    let proof = prover.prove(&expected, vec![padded_trace])?;
    println!("Proof generated in {:.2?}", start.elapsed());

    let start = Instant::now();
    let _checked = authority.verify_native(&proof, &expected)?;
    println!("Proof verified in {:.2?}", start.elapsed());

    println!("Blake3 binary field proof: SUCCESS");
    Ok(())
}
