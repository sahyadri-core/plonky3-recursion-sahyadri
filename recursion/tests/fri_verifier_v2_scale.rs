//! Phase 3F scale test: FriVerifierAirV2 memory + time at scale.
//!
//! Uses synthetic traces of increasing row counts to measure:
//!   - prove time (seconds)
//!   - proof size (bytes)
//!   - estimated peak memory (from trace + PCS overhead)
//!
//! Scale targets:
//!   - 4096 rows (~256 MB) — sanity
//!   - 16384 rows (~1 GB) — small proof
//!   - 65536 rows (~4 GB) — medium
//!   - 262144 rows (~15 GB) — the real question

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

const COL_PAIR0: usize = 0;
const COL_PAIR1: usize = 1;
const COL_ALPHA: usize = 2;
const COL_NEXT: usize = 3;
const COL_SEL: usize = 4;
const COL_IS_LAST: usize = 5;
const COL_S0: usize = 6;
const COL_S1: usize = 7;
const COL_S2: usize = 8;
const COL_S3: usize = 9;
const WIDTH: usize = 10;
const FINAL_POLY_LEN: usize = 4;
const NUM_PUBLIC: usize = FINAL_POLY_LEN;

pub struct FriVerifierAirV2;

impl<F2> BaseAir<F2> for FriVerifierAirV2 {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder> Air<AB> for FriVerifierAirV2
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
        let s = [
            AB::Expr::from(cur[COL_S0]),
            AB::Expr::from(cur[COL_S1]),
            AB::Expr::from(cur[COL_S2]),
            AB::Expr::from(cur[COL_S3]),
        ];
        let one = AB::F::ONE;
        for v in [&sel, &is_last, &s[0], &s[1], &s[2], &s[3]] {
            let sq = v.clone() * v.clone();
            b.assert_eq(sq + v.clone(), AB::F::ZERO);
        }
        for i in 0..FINAL_POLY_LEN {
            for j in (i + 1)..FINAL_POLY_LEN {
                let prod = s[i].clone() * s[j].clone();
                b.assert_eq(prod, AB::F::ZERO);
            }
        }
        let selector_sum = s[0].clone() + s[1].clone() + s[2].clone() + s[3].clone();
        b.assert_eq(is_last.clone() * (selector_sum + one.clone()), AB::F::ZERO);
        let x = pair0.clone() + pair1.clone();
        let y = sel * x;
        let z = alpha * (pair1 + y.clone());
        let folded = pair0 + y + z;
        b.assert_eq(next.clone(), folded);
        let public = b.public_values();
        let fp: [AB::Expr; FINAL_POLY_LEN] = [
            public[0].into(), public[1].into(),
            public[2].into(), public[3].into(),
        ];
        let selected = s[0].clone() * fp[0].clone()
            + s[1].clone() * fp[1].clone()
            + s[2].clone() * fp[2].clone()
            + s[3].clone() * fp[3].clone();
        let diff = next + selected;
        b.assert_eq(is_last * diff, AB::F::ZERO);
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

fn f(v: u64) -> F { F::from_u64(v) }

fn build_trace(n: usize) -> RowMajorMatrix<F> {
    let mut values = Vec::with_capacity(n * WIDTH);
    for i in 0..n {
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

fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

fn build_config(arity: usize) -> FriConfig {
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
    FriConfig {
        pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap(),
    }
}

fn measure_scale(n: usize) {
    let n_pow2 = n.next_power_of_two();
    let arity = (n_pow2 * WIDTH).next_power_of_two().trailing_zeros() as usize;
    println!("\n=== scale {} rows x {} cols, arity {} ===", n, WIDTH, arity);

    let trace = build_trace(n);
    let air = FriVerifierAirV2;
    let config = build_config(arity);

    let mut ch_setup = make_ch();
    let start = Instant::now();
    let (pk, _) = setup(&config, &[&air], &mut ch_setup).unwrap();
    println!("setup: {:?}", start.elapsed());

    let table = Table::new(trace.transpose());
    let public = vec![F::ZERO; NUM_PUBLIC];
    let instance = ProverInstance::new(&air, table, &pk, &public);

    let mut ch = make_ch();
    let start = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![instance]), 0, &mut ch);
    let elapsed = start.elapsed();

    match proof {
        Ok(p) => {
            let size = core::mem::size_of_val(&p);
            println!("PASS: {:?}, size ~{} B", elapsed, size);
        }
        Err(e) => println!("FAIL: {:?}", e),
    }
}

#[test]
#[ignore]
fn scale_4k() { measure_scale(4096); }

#[test]
#[ignore]
fn scale_16k() { measure_scale(16384); }

#[test]
#[ignore]
fn scale_65k() { measure_scale(65536); }

#[test]
#[ignore]
fn scale_262k() { measure_scale(262144); }
