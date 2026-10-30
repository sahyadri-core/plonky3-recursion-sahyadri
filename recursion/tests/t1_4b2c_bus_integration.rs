//! T1.4b.2c: Bus integration between SumcheckVerifier and Blake3Transcript.
//!
//! # Scope
//! - SumcheckVerifierBusAir Pushes (h0, h_inf, alpha) on SC_ROUND per row
//! - Blake3TranscriptBusAir Pulls (h0, h_inf, alpha) on SC_ROUND per row
//! - Bus balance enforced by MultiStark: SC row values == B3 row values
//!
//! # Soundness status
//! - SC's alpha IS constrained by fold equation (C4, C5, C6)
//! - B3's alpha is UNCONSTRAINED witness (bit gadget deferred)
//! - Bus balance: SC.alpha == B3.alpha for every row
//! - Combined: B3.alpha is forced to equal SC's fold-consistent alpha
//!
//! This is the "sandwich": once bit gadget (T1.4b.2b.2b.2b/c) proves
//! B3.alpha == Blake3.compute(IV, ROUND_POLY || h0 || h_inf), FS soundness
//! becomes complete. Today's test locks the SECOND HALF of that sandwich.
//!
//! # Tamper detection
//! - Change SC alpha → fold fails (C4) unless next_claimed also changes
//! - Change B3 alpha → bus unbalanced (SC pushes X, B3 pulls Y)
//! - Both changes together → fold + bus both pass, but attack detection
//!   requires bit gadget to prove B3.alpha is actual Blake3 output

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder};
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

use p3_blake3_air::{Blake3CompressionInput, generate_binary_trace_rows};
use p3_recursion::frost_gkr::blake3_transcript_air::{
    Blake3TranscriptAir, COL_H0 as B3_COL_H0,
    COL_H_INF as B3_COL_H_INF, COL_ALPHA as B3_COL_ALPHA, COL_IS_LAST as B3_COL_IS_LAST,
    WIDTH as B3_WIDTH,
};
use p3_recursion::frost_gkr::sumcheck_verifier_air::{
    SumcheckVerifierAir, SC_ROUND, COL_H0 as SC_COL_H0, COL_H_INF as SC_COL_H_INF,
    COL_ALPHA as SC_COL_ALPHA, COL_CLAIMED as SC_COL_CLAIMED,
    COL_NEXT_CLAIMED as SC_COL_NEXT, COL_IS_FIRST as SC_COL_IS_FIRST,
    COL_IS_LAST as SC_COL_IS_LAST,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

const COMBINED_WIDTH: usize = B3_WIDTH;  // 11540
const ROWS: usize = 2;

const IV_U32: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const ROUND_POLY_CONST: &[u8; 10] = b"round_poly";

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum CombinedAir {
    SumcheckVerifier,
    Blake3Transcript,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize { COMBINED_WIDTH }
    fn num_public_values(&self) -> usize {
        match self {
            Self::SumcheckVerifier => 2,
            Self::Blake3Transcript => 0,   // B3 doesn't use public values
        }
    }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => {
                SumcheckVerifierAir.eval(b);
                // Push (h0, h_inf, alpha) on SC_ROUND, ALWAYS (per row)
                let (h0, h_inf, alpha): (AB::Expr, AB::Expr, AB::Expr) = {
                    let main = b.main();
                    let cur = main.current_slice();
                    (
                        AB::Expr::from(cur[SC_COL_H0]),
                        AB::Expr::from(cur[SC_COL_H_INF]),
                        AB::Expr::from(cur[SC_COL_ALPHA]),
                    )
                };
                b.push_bus_interaction(
                    SC_ROUND,
                    BusDirection::Push,
                    [h0, h_inf, alpha],
                    BusActivation::Always,
                );
            }
            Self::Blake3Transcript => {
                Blake3TranscriptAir.eval(b);
                // Pull (h0, h_inf, alpha) on SC_ROUND, ALWAYS (per row)
                let (h0, h_inf, alpha): (AB::Expr, AB::Expr, AB::Expr) = {
                    let main = b.main();
                    let cur = main.current_slice();
                    (
                        AB::Expr::from(cur[B3_COL_H0]),
                        AB::Expr::from(cur[B3_COL_H_INF]),
                        AB::Expr::from(cur[B3_COL_ALPHA]),
                    )
                };
                b.push_bus_interaction(
                    SC_ROUND,
                    BusDirection::Pull,
                    [h0, h_inf, alpha],
                    BusActivation::Always,
                );
            }
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

fn fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

/// SC trace (2 rows). Row 0 real, row 1 padding with no-op fold.
/// Public = [initial_sum, final_sum]
fn build_sc_trace() -> (RowMajorMatrix<F>, Vec<F>, [(F, F, F); ROWS]) {
    let h0 = blk(2);
    let h_inf = blk(0);
    let alpha = blk(2);
    let claimed_0 = blk(1);
    let next_0 = fold(h0, h_inf, alpha, claimed_0);

    let mut values = vec![F::ZERO; ROWS * COMBINED_WIDTH];

    // Row 0 (real round)
    values[SC_COL_H0] = h0;
    values[SC_COL_H_INF] = h_inf;
    values[SC_COL_ALPHA] = alpha;
    values[SC_COL_CLAIMED] = claimed_0;
    values[SC_COL_NEXT] = next_0;
    values[SC_COL_IS_FIRST] = F::ONE;

    // Row 1 (padding, no-op fold)
    let claimed_1 = next_0;
    values[COMBINED_WIDTH + SC_COL_H0] = claimed_1;
    values[COMBINED_WIDTH + SC_COL_H_INF] = F::ZERO;
    values[COMBINED_WIDTH + SC_COL_ALPHA] = F::ZERO;
    values[COMBINED_WIDTH + SC_COL_CLAIMED] = claimed_1;
    values[COMBINED_WIDTH + SC_COL_NEXT] = claimed_1;
    values[COMBINED_WIDTH + SC_COL_IS_LAST] = F::ONE;

    let public = vec![claimed_0, next_0];
    let matches = [(h0, h_inf, alpha), (claimed_1, F::ZERO, F::ZERO)];
    (RowMajorMatrix::new(values, COMBINED_WIDTH), public, matches)
}

fn build_b3_trace(matches: [(F, F, F); 2]) -> RowMajorMatrix<F> {
    let mut block = [0u32; 16];
    for i in 0..10 {
        let w = i / 4;
        let b = i % 4;
        block[w] |= (ROUND_POLY_CONST[i] as u32) << (b * 8);
    }
    let input = Blake3CompressionInput {
        chaining_value: IV_U32,
        block,
        counter: 0,
        block_len: 42,
        flags: 1 | 2 | 8,
    };
    let blake3 = generate_binary_trace_rows::<F>(vec![input], 0);
    let b3_width = blake3.width();

    let mut values = vec![F::ZERO; ROWS * COMBINED_WIDTH];
    for r in 0..ROWS {
        for c in 0..b3_width {
            values[r * COMBINED_WIDTH + c] = blake3.values[0 * b3_width + c];
        }
        let (h0, h_inf, alpha) = matches[r];
        values[r * COMBINED_WIDTH + B3_COL_H0] = h0;
        values[r * COMBINED_WIDTH + B3_COL_H_INF] = h_inf;
        values[r * COMBINED_WIDTH + B3_COL_ALPHA] = alpha;
        if r == ROWS - 1 {
            values[r * COMBINED_WIDTH + B3_COL_IS_LAST] = F::ONE;
        }
    }
    RowMajorMatrix::new(values, COMBINED_WIDTH)
}

fn arity_for() -> usize {
    let total = 2 * ROWS * COMBINED_WIDTH;  // 2 tables (SC + B3)
    total.next_power_of_two().trailing_zeros() as usize
}

fn prove_and_verify(
    sc_trace: RowMajorMatrix<F>,
    sc_public: Vec<F>,
    b3_trace: RowMajorMatrix<F>,
    b3_public: Vec<F>,
    expect_ok: bool,
) {
    let arity = arity_for();
    println!("arity = {}", arity);
    let config = build_config(arity);

    let sc_air = CombinedAir::SumcheckVerifier;
    let b3_air = CombinedAir::Blake3Transcript;

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &b3_air], &mut ch_setup).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let b3_inst = ProverInstance::new(&b3_air, Table::new(b3_trace.transpose()), &pk, &b3_public);

    let mut ch_prove = make_ch();
    let start = Instant::now();
    let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(&config, ProverInstances::new(vec![sc_inst, b3_inst]), 0, &mut ch_prove)
    }));

    let log_h = ROWS.trailing_zeros() as usize;

    match prove_result {
        Ok(Ok(proof)) => {
            println!("PROVE OK, {:?}, size ~{} B",
                start.elapsed(), core::mem::size_of_val(&proof));
            let mut ch_verify = make_ch();
            let verif = vec![
                VerifierInstance::new(&sc_air, &vk, log_h, &sc_public),
                VerifierInstance::new(&b3_air, &vk, log_h, &b3_public),
            ];
            let start = Instant::now();
            let r = verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_verify);
            match r {
                Ok(()) => {
                    println!("VERIFY OK, {:?} — bus balanced", start.elapsed());
                    assert!(expect_ok, "expected fail but pass");
                }
                Err(e) => {
                    println!("VERIFY ERR: {:?}", e);
                    assert!(!expect_ok, "expected pass but fail");
                }
            }
        }
        Ok(Err(e)) => {
            println!("PROVE ERR: {:?}", e);
            assert!(!expect_ok, "expected pass but prove err");
        }
        Err(_) => {
            println!("PROVE PANIC");
            assert!(!expect_ok, "expected pass but panic");
        }
    }
}

#[test]
#[ignore]
fn bus_integration_balanced() {
    let (sc_trace, sc_public, matches) = build_sc_trace();
    let b3_trace = build_b3_trace(matches);
    prove_and_verify(sc_trace, sc_public, b3_trace, vec![], true);
}

#[test]
#[ignore]
fn bus_integration_tampered_b3_alpha_rejected() {
    let (sc_trace, sc_public, matches) = build_sc_trace();
    // Tamper row 0's alpha in B3 to be different from SC
    let mut tampered_matches = matches;
    tampered_matches[0].2 = matches[0].2 + F::ONE;
    let b3_trace = build_b3_trace(tampered_matches);
    prove_and_verify(sc_trace, sc_public, b3_trace, vec![], false);
}
