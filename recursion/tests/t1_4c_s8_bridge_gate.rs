//! Phase 2b-2b bridge gate: `MerkleTreeMmcs<F, u8, Poseidon2bFieldHash,
//! Poseidon2bFieldCompress, 2, 32>` works with `BinaryPcs`.
//!
//! # Purpose
//! `PreparedBinaryGroupedMultiStarkLayer::import_native` requires MMCS with
//! `CryptographicHasher<F, [u8; 32]>` + `PseudoCompressionFunction<[u8; 32], 2>`.
//! Our `Poseidon2bFieldHash` / `Poseidon2bFieldCompress` implement both.
//!
//! # Gate test
//! Prove + verify a `ConstantAir` (1 col, 1 public) trace with our MMCS.
//! If this passes, the MMCS adapter integrates cleanly with `BinaryPcs`.
//!
//! # Next (Phase 2b-2c)
//! Wrap the actual S7 combined proof (V2+SC+MP+P2B) with this MMCS and wire
//! via `import_native` → `PreparedBinaryGroupedMultiStarkLayer::prove`.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, BinaryPcsProverData, GroupedCodewordMmcs,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances, VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_test_utils::binary_field_params::blake3;

use sahyadri_fri_binius::poseidon2b_hasher::{Poseidon2bFieldCompress, Poseidon2bFieldHash};

type F = BinaryField128;
type E = BinaryField128;
type Ch = blake3::LevelChallenger<F>;

/// Raw MerkleTreeMmcs with Poseidon2b as hasher + compressor.
type RawMmcs = MerkleTreeMmcs<F, u8, Poseidon2bFieldHash, Poseidon2bFieldCompress, 2, 32>;
type RawRoundMmcs = MerkleTreeMmcs<E, u8, Poseidon2bFieldHash, Poseidon2bFieldCompress, 2, 32>;

/// GroupedCodewordMmcs wrapper (required by BinaryPcs).
type M = GroupedCodewordMmcs<RawMmcs>;
type ME = GroupedCodewordMmcs<RawRoundMmcs>;

// ─── Simple test AIR: 1 column, value must equal public ───

struct ConstantAir;

impl<Fb> BaseAir<Fb> for ConstantAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }
}

impl<AB: AirBuilder> Air<AB> for ConstantAir {
    fn eval(&self, b: &mut AB) {
        let value = b.main().current_slice()[0];
        let public = b.public_values()[0];
        b.assert_eq(value, public);
    }
}

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
    Ch::from_hasher(vec![], blake3::byte_hash())
}

fn build_cfg(arity: usize) -> Cfg {
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
    let mmcs = M::new(raw_mmcs, 8);
    let round = ME::for_folding(raw_round, &cfg);
    Cfg {
        pcs: BinaryPcs::new(cfg, mmcs, round).unwrap(),
    }
}

// ─── Gate test ───

#[test]
#[ignore]
fn bridge_gate_p2b_mmcs_proves_and_verifies() {
    println!("=== Bridge gate: prove with Poseidon2b MMCS ===");

    let value = F::from_le_bytes(3u128.to_le_bytes());
    let public = vec![value];
    let trace = RowMajorMatrix::new(vec![value; 2], 1);
    println!("trace: {}x{}", trace.height(), trace.width());

    // Arity for 2 rows × 1 col = 2 cells → arity 1 (2^1)
    // Must match witness arity exactly
    let trace_cells = trace.height() * trace.width();
    let arity = trace_cells.next_power_of_two().trailing_zeros() as usize;
    let cfg = build_cfg(arity);
    let air = ConstantAir;

    let mut ch_s = make_ch();
    let (pk, vk) = setup(&cfg, &[&air], &mut ch_s).unwrap();
    println!("Setup OK (arity {})", arity);

    // Prove
    let inst = ProverInstance::new(&air, Table::new(trace.transpose()), &pk, &public);
    let mut ch_p = make_ch();
    let start = std::time::Instant::now();
    let proof = prove(&cfg, ProverInstances::new(vec![inst]), 0, &mut ch_p)
        .expect("prove with Poseidon2b MMCS");
    println!("PROVE OK {:?}, ~{}B", start.elapsed(), std::mem::size_of_val(&proof));

    // Verify
    let log_h = trace.height().trailing_zeros() as usize;
    let v = VerifierInstance::new(&air, &vk, log_h, &public);
    let mut ch_v = make_ch();
    verify(&cfg, VerifierInstances::new(vec![v]), &proof, 0, &mut ch_v)
        .expect("verify with Poseidon2b MMCS");
    println!("VERIFY OK");

    // Tamper test: wrong public → verify fails
    let wrong = vec![value + F::ONE];
    let v2 = VerifierInstance::new(&air, &vk, log_h, &wrong);
    let mut ch_v2 = make_ch();
    let result = verify(&cfg, VerifierInstances::new(vec![v2]), &proof, 0, &mut ch_v2);
    assert!(result.is_err(), "tampered public must fail");
    println!("PASS: tampered public rejected");

    println!("\n=== BRIDGE GATE PASS: Poseidon2b MMCS proves + verifies ===");
    println!("Next: full S7 combined proof with this MMCS via import_native.");
}
