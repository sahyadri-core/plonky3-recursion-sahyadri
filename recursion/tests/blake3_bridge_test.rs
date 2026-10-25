//! A2.3c — Blake3 binary MultiStarkProof with concrete config.
//!
//! Uses p3-test-utils::binary_field_params::blake3 for ready-made
//! MMCS + challenger, mirroring binary_grouped_prepared_layer.rs.
//!
//! Discovery note: Table::new takes the transposed matrix in the reference
//! test (`RowMajorMatrix::new(vec![value; 2], 1).transpose()`).

use p3_binary_field::{BinaryField128, BinaryField64};
use p3_field::PrimeCharacteristicRing;
use p3_blake3_air::Blake3BinaryAir;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, ProverInstance, ProverInstances};
use p3_sumcheck::layout::{Layout, Table};
use p3_test_utils::binary_field_params::blake3;

// Type aliases from binary_grouped_prepared_layer.rs pattern
type F = BinaryField64;
type E = BinaryField128;   // or BinaryField128; see discovery
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

struct Blake3Config {
    pcs: BinaryPcs<F, E, M, ME>,
}

impl MultiStarkConfig for Blake3Config {
    type Val = F;
    type Challenge = E;
    type Challenger = Ch;
    type Pcs = BinaryPcs<F, E, M, ME>;
    fn pcs(&self) -> &Self::Pcs { &self.pcs }
    fn min_num_variables(&self) -> usize { 1 }
    fn build_witness(&self, tables: Vec<Table<F>>) -> p3_sumcheck::layout::Witness<F> {
        p3_sumcheck::layout::SuffixProver::<F, E>::new_witness(tables, 0)
    }
    fn committed_table<'a>(
        &self,
        data: &'a p3_binary_pcs::BinaryPcsProverData<F, E, M>,
        index: usize,
    ) -> &'a Table<F> {
        data.table(index)
    }
}

fn build_config() -> Blake3Config {
    // Arity 20 = log2(64 rows × 16384 cols). Must match the trace committed against.
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        20,
        BinaryPcsParams {
            log_inv_rate: 2,
            pow_bits: 0,
            security_level: 40,
        },
    ).unwrap();
    let mmcs = Tree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()),
        0,
    );
    let round = RoundTree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()),
        0,
    );
    Blake3Config {
        pcs: BinaryPcs::new(
            cfg,
            M::new(mmcs, 8),
            ME::for_folding(round, &cfg),
        ).unwrap(),
    }
}

fn make_challenger() -> Ch {
    Ch::from_hasher(vec![], blake3::byte_hash())
}

#[test]
#[ignore]
fn blake3_single_compression_multi_stark() {
    // 1. Build Blake3 trace (raw 11536 columns)
    use p3_blake3_air::{Blake3CompressionInput, generate_binary_trace_rows};
    let input = Blake3CompressionInput {
        chaining_value: [0u32; 8],
        block: [0u32; 16],
        counter: 0,
        block_len: 64,
        flags: 0,
    };
    let trace = generate_binary_trace_rows::<F>(vec![input], 0);
    println!("raw trace: {} x {}", trace.height(), trace.width());

    // 2. Pad to 16384 (AIR width)
    use p3_matrix::Matrix;
    let raw_height = trace.height();
    let width = trace.width();
    let padded_width = 16384;
    let target_rows = 64usize;  // match air.width
    let zero = F::ZERO;
    let mut padded = vec![zero; target_rows * padded_width];
    for r in 0..target_rows {
        let src = r % raw_height;
        for c in 0..width {
            padded[r * padded_width + c] = trace.get(src, c).unwrap();
        }
    }
    let padded_trace = RowMajorMatrix::new(padded, padded_width);
    println!(
        "padded trace: {} x {} (arity={})",
        padded_trace.height(),
        padded_trace.width(),
        (padded_trace.height() * padded_trace.width()).trailing_zeros()
    );

    // 3. Setup + prove
    let config = build_config();
    let air = Blake3BinaryAir::default();
    let mut ch_setup = make_challenger();
    let (pk, vk) = setup(&config, &[&air], &mut ch_setup).unwrap();

    // Table::new needs transposed matrix (per reference test)
    let table = Table::new(padded_trace.transpose());
    println!("DEBUG: config.min_num_variables() = {}", config.min_num_variables());
    let public: Vec<F> = vec![];  // Blake3BinaryAir num_public_values = 0
    let instance = ProverInstance::new(&air, table, &pk, &public);

    let mut ch = make_challenger();
    let proof = prove(
        &config,
        ProverInstances::new(vec![instance]),
        0,
        &mut ch,
    ).unwrap();

    println!("MultiStarkProof generated: {} bytes (rough)",
        core::mem::size_of_val(&proof));

    // A2.3d: verify the MultiStarkProof
    // VerifierInstance::new(air, verifying_key, num_variables, public_values)
    // num_variables = log2(trace_height) = log2(64) = 6
    let mut ch_verify = make_challenger();
    let num_variables = 6usize;
    let verifier_instances = p3_multi_stark::VerifierInstances::new(
        vec![p3_multi_stark::VerifierInstance::new(&air, &vk, num_variables, &public)]
    );
    p3_multi_stark::verify(&config, verifier_instances, &proof, 0, &mut ch_verify)
        .expect("MultiStarkProof must verify");
    println!("A2.3d: proof verified ✓");

    // 4. Verify (p3-multi-stark provides verify)
    // TODO after prove: use verify(&config, &[&air], &proof, &[&public])
}
