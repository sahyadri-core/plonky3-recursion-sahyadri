//! A2.3e — Blake3 binary MultiStarkProof → Goldilocks recursive proof.
//!
//! This is H2: Blake3 PoW validity attested inside a Goldilocks recursive proof.
//!
//! Reference: recursion/tests/binary_grouped_prepared_layer.rs (ConstantAir → Blake3)
//! Reference: recursion/tests/blake3_bridge_test.rs (A2.3d, binary proof works)

use p3_binary_field::{BinaryField128, BinaryField64};
use p3_blake3_air::Blake3BinaryAir;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
};
use p3_circuit::ops::ByteHash;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, ProverInstance, ProverInstances};
use p3_recursion::builtin_config::{FriConfigV1, SuiteIdV1, goldilocks_d2_poseidon2_binary};
use p3_recursion::pcs::binary::BinaryCodewordGrouping;
use p3_recursion::prepared::PreparedBinaryGroupedMultiStarkLayer;
use p3_recursion::verifier::BinaryGroupedMultiStarkVerifier;
use p3_recursion::ProveNextLayerParams;
use p3_sumcheck::layout::{Layout, Table};
use p3_test_utils::binary_field_params::blake3;
use p3_matrix::Matrix;
use p3_field::PrimeCharacteristicRing;

// ── Types (from A2.3d, known good) ──
type F = BinaryField64;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

// Output config: Goldilocks D2 binary FriConfig — same as sahyadri's RecursionConfig
type OutSC = p3_recursion::builtin_config::GoldilocksD2Poseidon2BinaryConfig;
const D_OUT: usize = 2;

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

fn build_blake3_pcs() -> (Blake3Config, Tree, RoundTree, BinaryPcsConfig) {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        17,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
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
    let config = Blake3Config {
        pcs: BinaryPcs::new(cfg, M::new(mmcs.clone(), 8), ME::for_folding(round.clone(), &cfg)).unwrap(),
    };
    (config, mmcs, round, cfg)
}

fn make_ch() -> Ch {
    Ch::from_hasher(vec![], blake3::byte_hash())
}

#[test]
#[ignore]
fn blake3_binary_to_goldilocks() {
    // ═══ Step 1: Blake3 trace + MultiStarkProof (from A2.3d, works) ═══
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

    // Pad to 64 x 16384
    let raw_height = trace.height();
    let width = trace.width();
    let padded_width = 16384;
    let target_rows = 8;
    let zero = F::ZERO;
    let mut padded = vec![zero; target_rows * padded_width];
    for r in 0..target_rows {
        let src = r % raw_height;
        for c in 0..width {
            padded[r * padded_width + c] = trace.get(src, c).unwrap();
        }
    }
    let padded_trace = RowMajorMatrix::new(padded, padded_width);
    println!("padded trace: {} x {}", padded_trace.height(), padded_trace.width());

    // ─── Blake3 PCS + proof (A2.3d) ───
    let (blake3_config, mmcs, round, cfg) = build_blake3_pcs();
    let air = Blake3BinaryAir::default();
    let mut ch_setup = make_ch();
    let (pk, _vk) = setup(&blake3_config, &[&air], &mut ch_setup).unwrap();
    let table = Table::new(padded_trace.transpose());
    let public: Vec<F> = vec![];
    let instance = ProverInstance::new(&air, table, &pk, &public);
    let mut ch_prove = make_ch();
    let proof = prove(
        &blake3_config,
        ProverInstances::new(vec![instance]),
        0,
        &mut ch_prove,
    ).unwrap();
    println!("A2.3e step 1: MultiStarkProof generated");

    // ═══ Step 2: Output config — Goldilocks D2 binary ═══
    // Uses sahyadri-compatible Goldilocks config.
    let artifact_limits = p3_recursion::artifact::ArtifactLimits::default();
    let output_config = goldilocks_d2_poseidon2_binary(
        &FriConfigV1::new(
            SuiteIdV1::GoldilocksD2Poseidon2BinaryFri,
            3, 0, 1, 60, 0, 20, 4, 0, 0, 0,
        ),
        &artifact_limits.verifier,
    ).unwrap();
    println!("A2.3e step 2: Goldilocks output config built");

    // ═══ Step 3: Build plan (BinaryGroupedMultiStarkVerifier) ═══
    // Bump metadata_entries limit (default 65536, Blake3 needs 65537+)
    let plan_limits = p3_recursion::verifier::VerifierLimits {
        max_metadata_entries: 1 << 19,
        ..p3_recursion::verifier::VerifierLimits::default()
    };
    let plan = BinaryGroupedMultiStarkVerifier::<F, E>::with_limits(
        &[&air],
        &[3],                         // log2(8 rows) = 3
        cfg,
        ByteHash::Keccak256,
        0, 0, 16, 128,
        BinaryCodewordGrouping::Codeword(8),
        BinaryCodewordGrouping::Folding,
        &plan_limits,                 // extra limits arg
    ).unwrap();
    println!("A2.3e step 3: plan built");

    // ═══ Step 4: PreparedBinaryGroupedMultiStarkLayer (H2 bridge) ═══
    let _ch_layer = make_ch();
    // Layer build: use with_limits (default 65536 too small for Blake3 proof)
    let layer_limits = p3_recursion::verifier::VerifierLimits {
        max_metadata_entries: 1 << 19,
        ..p3_recursion::verifier::VerifierLimits::default()
    };
    let layer = PreparedBinaryGroupedMultiStarkLayer::<F, E, OutSC, D_OUT>::with_limits(
        plan,
        ByteHash::Keccak256,
        b"sahyadri-blake3-bridge",
        output_config,
        ProveNextLayerParams::default(),
        &layer_limits,
    ).unwrap();
    println!("A2.3e step 4: layer built");

    // ═══ Step 5: import_native + prove → RecursionOutput<Goldilocks> ═══
    let mut ch_import = make_ch();
    let native_input = layer
        .binary_verifier()
        .import_native(&mmcs, &round, &vec![public.clone()], &proof, &mut ch_import)
        .unwrap();
    println!("A2.3e step 5a: import_native OK");

    let public_wrapped: Vec<Vec<F>> = vec![public.clone()];
    let output = layer.prove(&native_input, &public_wrapped).unwrap();
    println!("A2.3e step 5b: Goldilocks RecursionOutput produced");
    println!("  output proof size: {} bytes (rough)", core::mem::size_of_val(&output.0));

    // ═══ Step 6: verify the Goldilocks proof ═══
    let expected = layer.statement_layout().pack::<p3_goldilocks::Goldilocks>(&public_wrapped).unwrap();
    layer.verifier().verify(&output.0, &expected).unwrap();
    println!("A2.3e step 6: Goldilocks proof VERIFIED");

    println!("\n✅ A2.3e MILESTONE: Blake3 PoW attested in Goldilocks recursive proof");
}
