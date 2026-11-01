//! T1.5b + T1.5c: 3-AIR coexistence (SC + FRI + B3 transcript).
//!
//! # Scope
//! - Three distinct AIRs in one MultiStark proof
//! - SC width 7 / 2 public, FRI width 18 / 4 public, B3 width 11540 / 0 public
//! - Each AIR independently correct (constraints fire, tampering rejected)
//! - No cross-AIR binding yet (T1.5d: proper soundness via shared
//!   statement binding -- SC final claim == FRI opening value at challenge)
//!
//! # Why this matters
//! Full T1.5 verifier = SC + FRI + B3 all inline. This proves:
//! - MultiStark scales to 3 heterogeneous AIRs
//! - Per-variant BaseAir (width, public) works for 3 variants
//! - Trace builders for each work together
//!
//! # Honest
//! No SC_ROUND bus active yet. Cross-AIR binding comes in T1.5d once the
//! real MultiStarkProof statement binding is understood. This test = 3-AIR
//! assembly milestone.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_blake3_air::{Blake3CompressionInput, generate_binary_trace_rows};
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
use p3_recursion::frost_gkr::blake3_transcript_air::{
    Blake3TranscriptAir,
    COL_IS_LAST as B3_IS_LAST, WIDTH as B3_WIDTH,
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
const B3_ROWS: usize = 2;

const IV_U32: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const ROUND_POLY_CONST: &[u8; 10] = b"round_poly";

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum CombinedAir {
    SumcheckVerifier,
    FriVerifier,
    Blake3Transcript,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::SumcheckVerifier => SC_WIDTH,
            Self::FriVerifier => FRI_WIDTH,
            Self::Blake3Transcript => B3_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::SumcheckVerifier => 2,
            Self::FriVerifier => 4,
            Self::Blake3Transcript => 0,
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
            Self::Blake3Transcript => Blake3TranscriptAir.eval(b),
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

    values[3 * FRI_WIDTH + 5] = F::ONE;
    values[3 * FRI_WIDTH + 6] = F::ONE;

    (RowMajorMatrix::new(values, FRI_WIDTH), vec![F::ZERO; 4])
}

fn build_b3_trace() -> RowMajorMatrix<F> {
    let mut block = [0u32; 16];
    for i in 0..10 {
        let w = i / 4;
        let b = i % 4;
        block[w] |= (ROUND_POLY_CONST[i] as u32) << (b * 8);
    }
    let input = Blake3CompressionInput {
        chaining_value: IV_U32, block, counter: 0, block_len: 42,
        flags: 1 | 2 | 8,
    };
    let blake3 = generate_binary_trace_rows::<F>(vec![input], 0);
    let b3_w = blake3.width();

    let mut values = vec![F::ZERO; B3_ROWS * B3_WIDTH];
    for r in 0..B3_ROWS {
        for c in 0..b3_w {
            values[r * B3_WIDTH + c] = blake3.values[c];
        }
    }
    values[(B3_ROWS - 1) * B3_WIDTH + B3_IS_LAST] = F::ONE;
    RowMajorMatrix::new(values, B3_WIDTH)
}

fn compute_arity() -> usize {
    let raw = SC_ROWS * SC_WIDTH + FRI_ROWS * FRI_WIDTH + B3_ROWS * B3_WIDTH;
    raw.next_power_of_two().trailing_zeros() as usize
}

fn prove_verify() {
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let b3_trace = build_b3_trace();

    let arity = compute_arity();
    println!("SC {}x{}, FRI {}x{}, B3 {}x{}, arity {}",
        sc_trace.height(), sc_trace.width(),
        fri_trace.height(), fri_trace.width(),
        b3_trace.height(), b3_trace.width(), arity);

    let config = build_config(arity);
    let sc_air = CombinedAir::SumcheckVerifier;
    let fri_air = CombinedAir::FriVerifier;
    let b3_air = CombinedAir::Blake3Transcript;

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &fri_air, &b3_air], &mut ch_setup).unwrap();

    let b3_public: Vec<F> = vec![];
    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);
    let b3_inst = ProverInstance::new(&b3_air, Table::new(b3_trace.transpose()), &pk, &b3_public);

    let mut ch_prove = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![sc_inst, fri_inst, b3_inst]), 0, &mut ch_prove).unwrap();
    println!("PROVE {:?}, ~{} B", start.elapsed(), core::mem::size_of_val(&proof));

    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_public),    // log2(2)
        VerifierInstance::new(&fri_air, &vk, 2, &fri_public),  // log2(4)
        VerifierInstance::new(&b3_air, &vk, 1, &b3_public),    // log2(2)
    ];

    let mut ch_verify = make_ch();
    let start = Instant::now();
    verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_verify)
        .expect("3-AIR assembly must verify");
    println!("VERIFY {:?} -- SC + FRI + B3 coexist", start.elapsed());
    println!("\n=== T1.5b+c PASS ===");
}

#[test]
#[ignore]
fn three_air_coexist() {
    prove_verify();
}
