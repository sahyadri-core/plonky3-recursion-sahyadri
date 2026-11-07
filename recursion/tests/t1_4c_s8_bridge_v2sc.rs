//! Phase 2b-2d: V2+SC → Goldilocks bridge.
//!
//! # Flow
//! 1. Build V2 (2 rows, 0 public) + SC (2 rows, 2 public) traces
//! 2. Prove combined MultiStark with Poseidon2b MMCS
//! 3. BinaryGroupedMultiStarkVerifier::new(&[&V2, &SC], ...)
//! 4. PreparedBinaryGroupedMultiStarkLayer::new(verifier, blake3, [7,19,13], goldilocks_cfg, params)
//! 5. import_native(mmcs, round_mmcs, publics, proof, ch)
//! 6. layer.prove(native_input, publics) → RecursionOutput<BabyBearD4>
//! 7. layer.verifier().verify(goldilocks_proof, expected)

use p3_baby_bear::BabyBear;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, BinaryPcsProverData, GroupedCodewordMmcs,
};
use p3_circuit::ops::ByteHash;
use p3_field::{Field, PrimeCharacteristicRing};
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
use p3_recursion::frost_gkr::compressed_sumcheck_air::{
    CompressedSumcheckAir,
    COL_EVALS0, COL_EVALS1, COL_EVALS2, COL_EVALS3,
    COL_RUNNING_IN, COL_RUNNING_OUT, COL_CHALLENGE,
    COL_IS_FIRST, COL_IS_LAST as CS_IS_LAST,
    WIDTH as CS_WIDTH,
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

struct Cfg {
    pcs: BinaryPcs<F, E, M, ME>,
}

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
    fn committed_table<'a>(&self, data: &'a BinaryPcsProverData<F, E, M>, index: usize) -> &'a Table<F> {
        data.table(index)
    }
}

// ─── CombinedAir: enum wrapper so MultiStark accepts V2 + SC ───

#[derive(Clone, Copy)]
pub enum CombinedAir {
    V2,
    SC,
}

impl<Fb> p3_air::BaseAir<Fb> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::V2 => V2_WIDTH,
            Self::SC => CS_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::V2 => 0,
            Self::SC => 2,
        }
    }
}

impl<AB: p3_air::AirBuilder<F = BinaryField128>> p3_air::Air<AB> for CombinedAir {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::V2 => BinaryVerifierAirV2.eval(b),
            Self::SC => CompressedSumcheckAir::new().eval(b),
        }
    }
}

fn make_ch() -> Ch {
    Ch::from_hasher(vec![7, 19, 13], blake3::byte_hash())
}

fn build_cfg(arity: usize) -> (BinaryPcsConfig, Cfg, RawMmcs, RawRoundMmcs) {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let raw_mmcs = RawMmcs::new(Poseidon2bFieldHash, Poseidon2bFieldCompress, 0);
    let raw_round = RawRoundMmcs::new(Poseidon2bFieldHash, Poseidon2bFieldCompress, 0);
    let mmcs = M::new(raw_mmcs.clone(), 8);
    let round = ME::for_folding(raw_round.clone(), &cfg);
    let cfg_full = Cfg {
        pcs: BinaryPcs::new(cfg.clone(), mmcs, round).unwrap(),
    };
    (cfg, cfg_full, raw_mmcs, raw_round)
}

fn build_valid_v2_trace() -> RowMajorMatrix<F> {
    fn fold(lo: F, hi: F, beta: F, x: F) -> F {
        let f1 = lo + hi;
        let f0 = lo + x * f1;
        beta * (f0 + f1) + f0
    }
    let mut values = vec![F::ZERO; 2 * V2_WIDTH];
    // Row 0
    let (lo, hi, beta, x) = (
        F::from_le_bytes(3u128.to_le_bytes()),
        F::from_le_bytes(5u128.to_le_bytes()),
        F::from_le_bytes(7u128.to_le_bytes()),
        F::from_le_bytes(11u128.to_le_bytes()),
    );
    values[COL_LO] = lo; values[COL_HI] = hi; values[COL_BETA] = beta; values[COL_X] = x;
    values[COL_NEXT] = fold(lo, hi, beta, x);
    // Row 1
    let (lo, hi, beta, x) = (
        F::from_le_bytes(13u128.to_le_bytes()),
        F::from_le_bytes(17u128.to_le_bytes()),
        F::from_le_bytes(19u128.to_le_bytes()),
        F::from_le_bytes(23u128.to_le_bytes()),
    );
    values[V2_WIDTH + COL_LO] = lo;
    values[V2_WIDTH + COL_HI] = hi;
    values[V2_WIDTH + COL_BETA] = beta;
    values[V2_WIDTH + COL_X] = x;
    values[V2_WIDTH + COL_NEXT] = fold(lo, hi, beta, x);
    values[V2_WIDTH + COL_IS_LAST] = F::ONE;
    RowMajorMatrix::new(values, V2_WIDTH)
}

fn build_valid_sc_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    fn lagrange_eval(h: [F; 5], alpha: F) -> F {
        let mut result = F::ZERO;
        for i in 0..5 {
            let mut num = F::ONE;
            let mut den = F::ONE;
            for j in 0..5 {
                if i == j { continue; }
                let aj = F::from_le_bytes((j as u128).to_le_bytes());
                let ai = F::from_le_bytes((i as u128).to_le_bytes());
                num = num * (alpha + aj);
                den = den * (ai + aj);
            }
            result = result + h[i] * num * den.inverse();
        }
        result
    }
    let mut values = vec![F::ZERO; 2 * CS_WIDTH];
    // Row 0
    let e0_0 = F::from_le_bytes(3u128.to_le_bytes());
    let e1_0 = F::from_le_bytes(5u128.to_le_bytes());
    let e2_0 = F::from_le_bytes(7u128.to_le_bytes());
    let e3_0 = F::from_le_bytes(11u128.to_le_bytes());
    let r0_in = F::from_le_bytes(13u128.to_le_bytes());
    let alpha0 = F::from_le_bytes(17u128.to_le_bytes());
    let r0_out = lagrange_eval([e0_0, r0_in + e0_0, e1_0, e2_0, e3_0], alpha0);
    values[COL_EVALS0] = e0_0;
    values[COL_EVALS1] = e1_0;
    values[COL_EVALS2] = e2_0;
    values[COL_EVALS3] = e3_0;
    values[COL_RUNNING_IN] = r0_in;
    values[COL_RUNNING_OUT] = r0_out;
    values[COL_CHALLENGE] = alpha0;
    values[COL_IS_FIRST] = F::ONE;
    // Row 1
    let e0_1 = F::from_le_bytes(19u128.to_le_bytes());
    let e1_1 = F::from_le_bytes(23u128.to_le_bytes());
    let e2_1 = F::from_le_bytes(29u128.to_le_bytes());
    let e3_1 = F::from_le_bytes(31u128.to_le_bytes());
    let r1_in = r0_out;
    let alpha1 = F::from_le_bytes(37u128.to_le_bytes());
    let r1_out = lagrange_eval([e0_1, r1_in + e0_1, e1_1, e2_1, e3_1], alpha1);
    values[CS_WIDTH + COL_EVALS0] = e0_1;
    values[CS_WIDTH + COL_EVALS1] = e1_1;
    values[CS_WIDTH + COL_EVALS2] = e2_1;
    values[CS_WIDTH + COL_EVALS3] = e3_1;
    values[CS_WIDTH + COL_RUNNING_IN] = r1_in;
    values[CS_WIDTH + COL_RUNNING_OUT] = r1_out;
    values[CS_WIDTH + COL_CHALLENGE] = alpha1;
    values[CS_WIDTH + CS_IS_LAST] = F::ONE;
    let public = vec![r0_in, r1_out];
    (RowMajorMatrix::new(values, CS_WIDTH), public)
}

#[test]
#[ignore]
fn bridge_v2sc_import_and_prove() {
    println!("=== Phase 2b-2d: V2+SC bridge ===");

    // Build V2 + SC
    let v2_trace = build_valid_v2_trace();
    let (sc_trace, sc_public) = build_valid_sc_trace();
    println!("V2: {}x{}, SC: {}x{}", v2_trace.height(), v2_trace.width(), sc_trace.height(), sc_trace.width());

    // Arity from max
    let max_cells = (v2_trace.height() * v2_trace.width()).max(sc_trace.height() * sc_trace.width());
    let arity = max_cells.next_power_of_two().trailing_zeros() as usize;
    println!("arity: {}", arity);

    let (cfg, cfg_full, raw_mmcs, raw_round) = build_cfg(arity);
    let v2_air = CombinedAir::V2;
    let sc_air = CombinedAir::SC;
    let v2_public: Vec<F> = vec![];
    let publics = vec![v2_public.clone(), sc_public.clone()];

    let mut ch_setup = make_ch();
    let (pk, _vk) = setup(&cfg_full, &[&v2_air, &sc_air], &mut ch_setup).unwrap();
    println!("Setup OK");

    let v2_inst = ProverInstance::new(&v2_air, Table::new(v2_trace.transpose()), &pk, &v2_public);
    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let mut ch_prove = make_ch();
    let start = std::time::Instant::now();
    let proof = prove(&cfg_full, ProverInstances::new(vec![v2_inst, sc_inst]), 0, &mut ch_prove)
        .expect("V2+SC prove");
    println!("V2+SC PROVE OK {:?}", start.elapsed());

    // Verifier
    let v2_log_h = v2_trace.height().trailing_zeros() as usize;
    let sc_log_h = sc_trace.height().trailing_zeros() as usize;
    let hash = ByteHash::Blake3;
    let verifier = BinaryGroupedMultiStarkVerifier::<F, E>::new(
        &[&v2_air, &sc_air],
        &[v2_log_h, sc_log_h],
        cfg.clone(),
        hash,
        0, 0, 128, 1024,
        BinaryCodewordGrouping::Codeword(8),
        BinaryCodewordGrouping::Folding,
    ).expect("verifier plan");
    println!("Verifier plan OK");

    // Goldilocks output config
    let artifact_limits = ArtifactLimits::default();
    let output_config = baby_bear_d4_poseidon2_binary(
        &FriConfigV1::new(SuiteIdV1::BabyBearD4Poseidon2BinaryFri, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0),
        &artifact_limits.verifier,
    ).expect("output config");
    println!("Output config OK");

    // Layer
    let layer = PreparedBinaryGroupedMultiStarkLayer::<F, E, _, 4>::new(
        verifier.clone(),
        hash,
        &[7, 19, 13],
        output_config,
        ProveNextLayerParams::default(),
    ).expect("layer");
    println!("Layer OK");

    // Import native
    let mut ch_import = make_ch();
    let native_input = verifier
        .import_native(&raw_mmcs, &raw_round, &publics, &proof, &mut ch_import)
        .expect("import_native");
    println!("import_native OK");

    // Prove → Goldilocks
    let start = std::time::Instant::now();
    let goldilocks = layer.prove(&native_input, &publics).expect("layer.prove");
    println!("BRIDGE PROVE OK {:?}, ~{}B", start.elapsed(), std::mem::size_of_val(&goldilocks.0));

    // Verify
    let expected: Vec<BabyBear> = layer.statement_layout().pack::<BabyBear>(&publics).expect("pack");
    println!("expected: {} values", expected.len());
    layer.verifier().verify(&goldilocks.0, &expected).expect("verify");
    println!("GOLDILOCKS VERIFY OK");

    println!("\n=== PHASE 2b-2d PASS: V2+SC → Goldilocks bridge ===");
}
