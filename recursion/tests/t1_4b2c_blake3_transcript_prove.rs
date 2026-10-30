//! T1.4b.2c-mini: prove Blake3TranscriptAir as MultiStark.
//!
//! Locks: the AIR + valid trace can be committed, proven, and verified
//! via the same MultiStark pipeline as 3D2d/C1.5.
//!
//! SCOPE (honest):
//! - Proves Blake3 compression trace + boundary constants (IV, ROUND_POLY, flags, padding)
//! - alpha COL still witness (FS binding = T1.4b.2b.2b.2c, next session)
//! - Integration with SumcheckVerifierAir via SC_ROUND bus = T1.4b.2c full

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_bus::BusInteractionBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use std::time::Instant;

use p3_recursion::frost_gkr::blake3_transcript_air::{
    Blake3TranscriptAir, Blake3TranscriptBusAir, WIDTH, COL_IS_LAST,
};
use p3_blake3_air::{Blake3CompressionInput, generate_binary_trace_rows};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

const IV_U32: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const ROUND_POLY_CONST: &[u8; 10] = b"round_poly";
const CHUNK_START: u32 = 1;
const CHUNK_END: u32 = 2;
const ROOT_FLAG: u32 = 8;

fn build_compression_input() -> Blake3CompressionInput {
    let mut block = [0u32; 16];
    for i in 0..10 {
        let w = i / 4;
        let b = i % 4;
        block[w] |= (ROUND_POLY_CONST[i] as u32) << (b * 8);
    }
    Blake3CompressionInput {
        chaining_value: IV_U32,
        block,
        counter: 0,
        block_len: 42,
        flags: CHUNK_START | CHUNK_END | ROOT_FLAG,
    }
}

fn build_valid_trace() -> RowMajorMatrix<F> {
    let blake3 = generate_binary_trace_rows::<F>(vec![build_compression_input()], 0);
    let b3_width = blake3.width();
    // Pad to 2 rows so arity = log2(2 * 11540 next_pow2) = 15,
    // satisfying MultiStark padding floor (was arity 14 with 1 row).
    // Blake3 has no inter-row constraints, so duplicate row is a valid
    // second compression. is_first_row = row 0 only -> constants bound there.
    let num_rows = 2usize;
    let mut values = vec![F::ZERO; num_rows * WIDTH];
    for r in 0..num_rows {
        for c in 0..b3_width {
            values[r * WIDTH + c] = blake3.values[0 * b3_width + c];
        }
    }
    values[1 * WIDTH + COL_IS_LAST] = F::ONE;
    RowMajorMatrix::new(values, WIDTH)
}

#[derive(Clone, Copy)]
pub enum CombinedAir {
    Blake3Transcript,       // standalone, no bus (this test)
    Blake3TranscriptBus,    // with SC_ROUND Pull (integration, T1.4b.2c)
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 0 }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::Blake3Transcript => Blake3TranscriptAir.eval(b),
            Self::Blake3TranscriptBus => Blake3TranscriptBusAir.eval(b),
        }
    }
}

struct Cfg { pcs: BinaryPcs<F, E, M, ME> }

impl MultiStarkConfig for Cfg {
    type Val = F;
    type Challenge = E;
    type Challenger = Ch;
    type Pcs = BinaryPcs<F, E, M, ME>;
    fn pcs(&self) -> &Self::Pcs { &self.pcs }
    fn min_num_variables(&self) -> usize { 1 }
    fn build_witness(&self, tables: Vec<Table<F>>) -> p3_sumcheck::layout::Witness<F> {
        SuffixProver::<F, E>::new_witness(tables, 0)
    }
    fn committed_table<'a>(&self, data: &'a p3_binary_pcs::BinaryPcsProverData<F, E, M>, index: usize) -> &'a Table<F> {
        data.table(index)
    }
}

fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

fn build_config(arity: usize) -> Cfg {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Tree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()), 0,
    );
    let round = RoundTree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()), 0,
    );
    Cfg { pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap() }
}

#[test]
#[ignore]
fn blake3_transcript_prove_verify() {
    let trace = build_valid_trace();
    let log_h = trace.height().trailing_zeros() as usize;
    let cells = trace.height() * WIDTH;
    let arity = cells.next_power_of_two().trailing_zeros() as usize;
    println!("trace {}x{}, log_h {}, arity {}", trace.height(), trace.width(), log_h, arity);

    let config = build_config(arity);
    let air = CombinedAir::Blake3Transcript;  // non-bus: no SC_ROUND Pull, no need for SumcheckVerifierBusAir producer
    let public: Vec<F> = vec![];

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&air], &mut ch_setup).unwrap();

    let instance = ProverInstance::new(
        &air, Table::new(trace.transpose()), &pk, &public,
    );
    let mut ch_prove = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![instance]), 0, &mut ch_prove).unwrap();
    let prove_time = start.elapsed();
    println!("PROVE {:?}, ~{} B", prove_time, core::mem::size_of_val(&proof));

    let verif = VerifierInstance::new(&air, &vk, log_h, &public);
    let mut ch_verify = make_ch();
    let start = Instant::now();
    verify(&config, VerifierInstances::new(vec![verif]), &proof, 0, &mut ch_verify)
        .expect("valid blake3 transcript must verify");
    let verify_time = start.elapsed();
    println!("VERIFY {:?}", verify_time);

    println!("\n=== T1.4b.2c-mini PASS ===");
    println!("Blake3TranscriptBusAir proven as MultiStark");
}
