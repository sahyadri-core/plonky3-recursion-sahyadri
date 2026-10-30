//! T1.5a: SumcheckVerifier + FRI verifier coexist as 2-AIR MultiStark.
//!
//! # Scope
//! - Proves that SC trace (3 rows) and FRI trace (24 rows) can coexist
//!   in a single MultiStark proof
//! - Different widths (SC=7, FRI=18) via per-variant BaseAir
//! - Different heights via padding
//! - No alpha binding yet (T1.5b, next session adds bus SC_ROUND)
//!
//! # Why this matters
//! Full T1.5 goal is: verify a MultiStarkProof (sumcheck + FRI + bus) in
//! binary circuit. Assembly requires SC + FRI + B3 to share one MultiStark.
//! If this 2-AIR assembly works, 3-AIR is next.
//!
//! # Honest
//! No soundness yet (no alpha binding). Just plumbing.

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

use p3_recursion::frost_gkr::sumcheck_verifier_air::{
    SumcheckVerifierAir,
    COL_H0 as SC_H0, COL_H_INF as SC_H_INF, COL_ALPHA as SC_ALPHA,
    COL_CLAIMED as SC_CLAIMED, COL_NEXT_CLAIMED as SC_NEXT,
    COL_IS_FIRST as SC_IS_FIRST, COL_IS_LAST as SC_IS_LAST,
    WIDTH as SC_WIDTH,
};
use p3_recursion::frost_gkr::binary_verifier_air::{
    BinaryVerifierAir,
    COL_PAIR0 as FRI_PAIR0, COL_PAIR1 as FRI_PAIR1, COL_ALPHA as FRI_ALPHA,
    COL_NEXT as FRI_NEXT, COL_SEL as FRI_SEL,
    WIDTH as FRI_WIDTH,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

const SC_ROWS: usize = 2;
const FRI_ROWS: usize = 4;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum CombinedAir {
    SumcheckVerifier,
    FriVerifier,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::SumcheckVerifier => SC_WIDTH,
            Self::FriVerifier => FRI_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::SumcheckVerifier => 2,
            Self::FriVerifier => 4,
        }
    }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::FriVerifier => BinaryVerifierAir.eval(b),
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

fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

fn fri_fold(p0: F, p1: F, alpha: F, sel: F) -> F {
    let x = p0 + p1;
    let y = sel * x;
    let z = alpha * (p1 + y);
    p0 + y + z
}

/// Raw SC trace (2 rows, both power-of-2). No manual padding --
/// MultiStark pads internally. is_last on raw last row (row 1).
fn build_sc_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let h0 = blk(2);
    let h_inf = blk(0);
    let alpha = blk(2);
    let claimed_0 = blk(1);
    let next_0 = sc_fold(h0, h_inf, alpha, claimed_0);
    let claimed_1 = next_0;

    let mut values = vec![F::ZERO; SC_ROWS * SC_WIDTH];
    values[SC_H0] = h0;
    values[SC_H_INF] = h_inf;
    values[SC_ALPHA] = alpha;
    values[SC_CLAIMED] = claimed_0;
    values[SC_NEXT] = next_0;
    values[SC_IS_FIRST] = F::ONE;

    values[SC_WIDTH + SC_H0] = claimed_1;
    values[SC_WIDTH + SC_CLAIMED] = claimed_1;
    values[SC_WIDTH + SC_NEXT] = claimed_1;
    values[SC_WIDTH + SC_IS_LAST] = F::ONE;

    (RowMajorMatrix::new(values, SC_WIDTH), vec![claimed_0, claimed_1])
}

/// Raw FRI trace (4 rows, power-of-2). No manual padding.
/// is_last on raw last row (row 3).
fn build_fri_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let p0 = blk(10);
    let p1 = blk(20);
    let alpha = blk(30);
    let fold_out = fri_fold(p0, p1, alpha, F::ONE);

    let mut values = vec![F::ZERO; FRI_ROWS * FRI_WIDTH];
    values[FRI_PAIR0] = p0;
    values[FRI_PAIR1] = p1;
    values[FRI_ALPHA] = alpha;
    values[FRI_NEXT] = fold_out;
    values[FRI_SEL] = F::ONE;

    values[3 * FRI_WIDTH + 5] = F::ONE;  // is_last col on row 3
    values[3 * FRI_WIDTH + 6] = F::ONE;  // s0 col

    (RowMajorMatrix::new(values, FRI_WIDTH), vec![F::ZERO; 4])
}

fn prove_verify() {
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();

    // 3D2d pattern: arity = log2(next_pow2(raw_total_cells))
    let raw_cells = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH;
    let arity = raw_cells.next_power_of_two().trailing_zeros() as usize;
    println!("SC {}x{}, FRI {}x{}, raw_cells {}, arity {}",
        sc_trace.height(), sc_trace.width(),
        fri_trace.height(), fri_trace.width(),
        raw_cells, arity);

    let config = build_config(arity);
    let sc_air = CombinedAir::SumcheckVerifier;
    let fri_air = CombinedAir::FriVerifier;

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &fri_air], &mut ch_setup).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);

    let mut ch_prove = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_prove).unwrap();
    println!("PROVE {:?}, ~{} B", start.elapsed(), core::mem::size_of_val(&proof));

    // log_h = log2(raw height) per instance
    let sc_log_h = SC_ROWS.trailing_zeros() as usize;
    let fri_log_h = FRI_ROWS.trailing_zeros() as usize;
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, sc_log_h, &sc_public),
        VerifierInstance::new(&fri_air, &vk, fri_log_h, &fri_public),
    ];

    let mut ch_verify = make_ch();
    let start = Instant::now();
    verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_verify)
        .expect("SC + FRI assembly must verify");
    println!("VERIFY {:?} -- SC + FRI coexist", start.elapsed());

    println!("\n=== T1.5a PASS ===");
}

#[test]
#[ignore]
fn sc_fri_coexist() {
    prove_verify();
}
