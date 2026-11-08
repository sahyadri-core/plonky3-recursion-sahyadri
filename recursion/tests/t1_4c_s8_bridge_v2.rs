//! Phase 2b-2d: V2-only A'2 proof → import_native → Goldilocks output.
//!
//! # Purpose
//! Prove the full bridge end-to-end with a real V2 MultiStark proof
//! using Poseidon2b MerkleTreeMmcs.
//!
//! # Flow
//! 1. Build V2 trace (2 rows, valid fold relations, is_last on row 1)
//! 2. Prove with Poseidon2b MMCS via BinaryPcs
//! 3. BinaryGroupedMultiStarkVerifier::new(&[&V2Air], heights, cfg, ...)
//! 4. PreparedBinaryGroupedMultiStarkLayer::new(verifier, blake3, init_bytes, goldilocks_cfg, params)
//! 5. verifier.import_native(mmcs, round_mmcs, public, proof, ch) → NativeBinaryMultiStarkInput
//! 6. layer.prove(native_input, public) → RecursionOutput<BabyBearD4>
//! 7. layer.verifier().verify(goldilocks_proof, expected_statement)
//!
//! # If this passes
//! Full A'2-to-Goldilocks bridge works for single AIR. Next: add SC, MP, P2B.

use p3_baby_bear::BabyBear;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, BinaryPcsProverData, GroupedCodewordMmcs,
};
use p3_circuit::ops::ByteHash;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, ProverInstance, ProverInstances};
use p3_recursion::artifact::ArtifactLimits;
use p3_recursion::builtin_config::{FriConfigV1, SuiteIdV1, baby_bear_d4_poseidon2_binary};
use p3_recursion::frost_gkr::binary_verifier_air_v2::{
    BinaryVerifierAirV2, COL_BETA, COL_HI, COL_IS_LAST, COL_LO, COL_NEXT, COL_X, WIDTH as V2_WIDTH,
};
use p3_recursion::pcs::binary::BinaryCodewordGrouping;
use p3_recursion::prepared::PreparedBinaryGroupedMultiStarkLayer;
use p3_recursion::verifier::BinaryGroupedMultiStarkVerifier;
use p3_recursion::ProveNextLayerParams;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;

use sahyadri_fri_binius::poseidon2b_hasher::{Poseidon2bFieldCompress, Poseidon2bFieldHash};

type F = BinaryField128;
type E = BinaryField128;
type Ch = blake3::LevelChallenger<F>;

type RawMmcs = MerkleTreeMmcs<F, u8, Poseidon2bFieldHash, Poseidon2bFieldCompress, 2, 32>;
type RawRoundMmcs = MerkleTreeMmcs<E, u8, Poseidon2bFieldHash, Poseidon2bFieldCompress, 2, 32>;
type M = GroupedCodewordMmcs<RawMmcs>;
type ME = GroupedCodewordMmcs<RawRoundMmcs>;

// ─── Config ───

struct Cfg {
    pcs: BinaryPcs<F, E, M, ME>,
}

impl MultiStarkConfig for Cfg {
    type Val = F;
    type Challenge = E;
    type Challenger = Ch;
    type Pcs = BinaryPcs<F, E, M, ME>;

    fn pcs(&self) -> &Self::Pcs {
        &self.pcs
    }

    fn min_num_variables(&self) -> usize {
        1
    }

    fn build_witness(&self, tables: Vec<Table<F>>) -> p3_sumcheck::layout::Witness<F> {
        SuffixProver::<F, E>::new_witness(tables, 0)
    }

    fn committed_table<'a>(
        &self,
        data: &'a BinaryPcsProverData<F, E, M>,
        index: usize,
    ) -> &'a Table<F> {
        data.table(index)
    }
}

fn make_ch() -> Ch {
    Ch::from_hasher(vec![7, 19, 13], blake3::byte_hash())
}

fn build_cfg(arity: usize) -> (BinaryPcsConfig, Cfg, RawMmcs, RawRoundMmcs) {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
        BinaryPcsParams {
            log_inv_rate: 2,
            pow_bits: 0,
            security_level: 40,
        },
    )
    .unwrap();
    let raw_mmcs = RawMmcs::new(Poseidon2bFieldHash, Poseidon2bFieldCompress, 0);
    let raw_round = RawRoundMmcs::new(Poseidon2bFieldHash, Poseidon2bFieldCompress, 0);
    let mmcs = M::new(raw_mmcs.clone(), 8);
    let round = ME::for_folding(raw_round.clone(), &cfg);
    let cfg_full = Cfg {
        pcs: BinaryPcs::new(cfg.clone(), mmcs, round).unwrap(),
    };
    (cfg, cfg_full, raw_mmcs, raw_round)
}

// ─── Valid V2 trace: 2 rows, real fold on both, is_last on row 1 ───

fn build_valid_v2_trace() -> RowMajorMatrix<F> {
    fn fold(lo: F, hi: F, beta: F, x: F) -> F {
        let f1 = lo + hi;
        let f0 = lo + x * f1;
        beta * (f0 + f1) + f0
    }

    let mut values = vec![F::ZERO; 2 * V2_WIDTH];

    // Row 0
    let lo = F::from_le_bytes(3u128.to_le_bytes());
    let hi = F::from_le_bytes(5u128.to_le_bytes());
    let beta = F::from_le_bytes(7u128.to_le_bytes());
    let x = F::from_le_bytes(11u128.to_le_bytes());
    let next = fold(lo, hi, beta, x);
    values[COL_LO] = lo;
    values[COL_HI] = hi;
    values[COL_BETA] = beta;
    values[COL_X] = x;
    values[COL_NEXT] = next;

    // Row 1
    let lo = F::from_le_bytes(13u128.to_le_bytes());
    let hi = F::from_le_bytes(17u128.to_le_bytes());
    let beta = F::from_le_bytes(19u128.to_le_bytes());
    let x = F::from_le_bytes(23u128.to_le_bytes());
    let next = fold(lo, hi, beta, x);
    values[V2_WIDTH + COL_LO] = lo;
    values[V2_WIDTH + COL_HI] = hi;
    values[V2_WIDTH + COL_BETA] = beta;
    values[V2_WIDTH + COL_X] = x;
    values[V2_WIDTH + COL_NEXT] = next;
    values[V2_WIDTH + COL_IS_LAST] = F::ONE;

    RowMajorMatrix::new(values, V2_WIDTH)
}

#[test]
#[ignore]
fn bridge_v2_import_and_prove() {
    println!("=== Phase 2b-2d: V2 bridge to Goldilocks ===");

    // 1. Build V2 trace + prove with Poseidon2b MMCS
    let trace = build_valid_v2_trace();
    println!("V2 trace: {}x{}", trace.height(), trace.width());

    let trace_cells = trace.height() * trace.width();
    let arity = trace_cells.next_power_of_two().trailing_zeros() as usize;
    println!("arity: {}", arity);

    let (cfg, cfg_full, raw_mmcs, raw_round) = build_cfg(arity);
    let air = BinaryVerifierAirV2;
    let v2_public: Vec<F> = vec![];              // V2 has 0 public values (for ProverInstance)
    let publics: Vec<Vec<F>> = vec![vec![]];    // 1 AIR × 0 values (for import_native/layer)

    let mut ch_setup = make_ch();
    let (pk, _vk) = setup(&cfg_full, &[&air], &mut ch_setup).unwrap();
    println!("Setup OK");

    let inst = ProverInstance::new(&air, Table::new(trace.transpose()), &pk, &v2_public);
    let mut ch_prove = make_ch();
    let start = std::time::Instant::now();
    let v2_proof = prove(&cfg_full, ProverInstances::new(vec![inst]), 0, &mut ch_prove)
        .expect("V2 prove with Poseidon2b MMCS");
    println!("V2 PROVE OK {:?}", start.elapsed());

    // 2. Build verifier plan
    let hash = ByteHash::Poseidon2b;  // matches Poseidon2b MMCS
    let v2_log_h = trace.height().trailing_zeros() as usize;
    let verifier = BinaryGroupedMultiStarkVerifier::<F, E>::new(
        &[&air],
        &[v2_log_h],
        cfg.clone(),
        hash,
        0,     // cap_height
        0,     // pow_bits
        128,   // max_tau_draws (was 4 — security_level 40 needs more)
        1024,  // max_query_draws (was 64 — log_blowup 2 needs more)
        BinaryCodewordGrouping::Codeword(8),
        BinaryCodewordGrouping::Folding,
    )
    .expect("BinaryGroupedMultiStarkVerifier::new");
    println!("Verifier plan OK");

    // 3. Build Goldilocks output config
    let artifact_limits = ArtifactLimits::default();
    let output_config = baby_bear_d4_poseidon2_binary(
        &FriConfigV1::new(
            SuiteIdV1::BabyBearD4Poseidon2BinaryFri,
            1, 0, 2, 2, 0, 0, 0, 0, 0, 0,
        ),
        &artifact_limits.verifier,
    )
    .expect("baby_bear_d4_poseidon2_binary");
    println!("Output config OK");

    // 4. Build layer
    // Empty initial_bytes: V2 has no initial transcript state
    let layer = PreparedBinaryGroupedMultiStarkLayer::<F, E, _, 4>::new(
        verifier.clone(),
        hash,
        &[7, 19, 13],
        output_config,
        ProveNextLayerParams::default(),
    )
    .expect("PreparedBinaryGroupedMultiStarkLayer::new");
    println!("Layer OK");

    // 5. Import native
    let mut ch_import = make_ch();
    let native_input = verifier
        .import_native(
            &raw_mmcs,
            &raw_round,
            &publics,
            &v2_proof,
            &mut ch_import,
        )
        .expect("import_native");
    println!("import_native OK");

    // 6. Prove → Goldilocks
    let start = std::time::Instant::now();
    let goldilocks_output = layer
        .prove(&native_input, &publics)
        .expect("layer.prove");
    println!("BRIDGE PROVE OK {:?}, ~{}B",
        start.elapsed(), std::mem::size_of_val(&goldilocks_output.0));

    // 7. Verify
    let expected: Vec<BabyBear> = layer
        .statement_layout()
        .pack::<BabyBear>(&publics)
        .expect("statement pack");
    println!("expected statement: {} values", expected.len());

    layer
        .verifier()
        .verify(&goldilocks_output.0, &expected)
        .expect("goldilocks verify");
    println!("GOLDILOCKS VERIFY OK");

    println!("\n=== PHASE 2b-2d PASS: V2 → Goldilocks bridge works ===");
    println!("Next: add SC → full S7 combined bridge.");
}
