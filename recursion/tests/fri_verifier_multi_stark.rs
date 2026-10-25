//! Phase 3F base test: prove FriVerifierAir via MultiStark (binary field).
//!
//! This is the memory/time baseline for the composed FRI verifier circuit.
//! Uses the current FriVerifierAir (fold + booleanity + root-pin), which
//! passes only in artificial tests until Phase 3D part 2 adds the real
//! final_poly binding. Purpose here is to measure proving cost at scale
//! so we know whether 16 GB is feasible.

#![allow(clippy::too_many_arguments)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::{BinaryField128, BinaryField64};
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, ProverInstance, ProverInstances};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use std::time::Instant;

type F = BinaryField64;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

// Copy of FriVerifierAir (same constraints as sahyadri-fri-binius)
const COL_PAIR0: usize = 0;
const COL_PAIR1: usize = 1;
const COL_ALPHA: usize = 2;
const COL_NEXT: usize = 3;
const COL_SEL: usize = 4;
const COL_IS_LAST: usize = 5;
const WIDTH: usize = 6;

pub struct FriVerifierAir;

impl<F2> BaseAir<F2> for FriVerifierAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 1 }
}

impl<AB: AirBuilder> Air<AB> for FriVerifierAir
where
    AB::F: PrimeCharacteristicRing,
{
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let cur = main.current_slice();
        let pair0: AB::Expr = cur[COL_PAIR0].into();
        let pair1: AB::Expr = cur[COL_PAIR1].into();
        let alpha: AB::Expr = cur[COL_ALPHA].into();
        let next: AB::Expr = cur[COL_NEXT].into();
        let sel: AB::Expr = cur[COL_SEL].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();

        let sel_sq = sel.clone() * sel.clone();
        b.assert_eq(sel_sq + sel.clone(), AB::F::ZERO);
        let last_sq = is_last.clone() * is_last.clone();
        b.assert_eq(last_sq + is_last.clone(), AB::F::ZERO);

        let x = pair0.clone() + pair1.clone();
        let y = sel * x;
        let z = alpha * (pair1 + y.clone());
        let folded = pair0 + y + z;
        b.assert_eq(next.clone(), folded);

        let public = b.public_values();
        let root: AB::Expr = public[0].into();
        let diff = next + root;
        let pinned = is_last * diff;
        b.assert_eq(pinned, AB::F::ZERO);
    }
}

struct FriConfig {
    pcs: BinaryPcs<F, E, M, ME>,
}

impl MultiStarkConfig for FriConfig {
    type Val = F;
    type Challenge = E;
    type Challenger = Ch;
    type Pcs = BinaryPcs<F, E, M, ME>;
    fn pcs(&self) -> &Self::Pcs { &self.pcs }
    fn min_num_variables(&self) -> usize { 1 }
    fn build_witness(&self, tables: Vec<Table<F>>) -> p3_sumcheck::layout::Witness<F> {
        SuffixProver::<F, E>::new_witness(tables, 0)
    }
    fn committed_table<'a>(
        &self,
        data: &'a p3_binary_pcs::BinaryPcsProverData<F, E, M>,
        index: usize,
    ) -> &'a Table<F> {
        data.table(index)
    }
}


fn f(v: u64) -> F {
    F::from_u64(v)
}

fn build_trace(target_rows: usize) -> RowMajorMatrix<F> {
    let mut values = Vec::with_capacity(target_rows * WIDTH);
    for i in 0..target_rows {
        let pair0 = f(i as u64);
        let pair1 = f((i + 1000) as u64);
        let alpha = f(7);
        let sel_val = (i & 1) as u8;
        let sel = f(sel_val as u64);
        let folded = if sel_val == 0 {
            pair0 + alpha * pair1
        } else {
            pair1 + alpha * pair0
        };
        let mut row = [F::ZERO; WIDTH];
        row[COL_PAIR0] = pair0;
        row[COL_PAIR1] = pair1;
        row[COL_ALPHA] = alpha;
        row[COL_NEXT] = folded;
        row[COL_SEL] = sel;
        row[COL_IS_LAST] = F::ZERO;
        values.extend_from_slice(&row);
    }
    RowMajorMatrix::new(values, WIDTH)
}

fn make_ch() -> Ch {
    Ch::from_hasher(vec![], blake3::byte_hash())
}

fn build_config(arity: usize) -> FriConfig {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
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
    FriConfig {
        pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap(),
    }
}

#[test]
#[ignore]
fn prove_fri_verifier_small() {
    // 4096 rows × 6 cols = 24576 cells, arity 15
    let target_rows = 4096;
    let arity = (target_rows * WIDTH).next_power_of_two().trailing_zeros() as usize;
    println!("trace {} x {}, arity {}", target_rows, WIDTH, arity);

    let trace = build_trace(target_rows);
    let air = FriVerifierAir;
    let config = build_config(arity);

    let mut ch_setup = make_ch();
    let (pk, _) = setup(&config, &[&air], &mut ch_setup).unwrap();

    let table = Table::new(trace.transpose());
    let public = vec![F::ZERO];
    let instance = ProverInstance::new(&air, table, &pk, &public);

    let mut ch = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![instance]), 0, &mut ch);
    let elapsed = start.elapsed();

    match proof {
        Ok(p) => {
            let size = core::mem::size_of_val(&p);
            println!("PASS: proof ~{} bytes (size_of_val), elapsed {:?}", size, elapsed);
        }
        Err(e) => {
            println!("FAIL: {:?}", e);
        }
    }
}
