//! Phase T1.1: 2-to-1 FRI aggregation.
//!
//! Demonstrates `BinaryAggregationAir` verifying TWO FRI proofs in one AIR
//! with commitment binding. Uses synthetic traces (like C1.5).
//!
//! Real E2E with 3F proofs (T1.3) needs Poseidon2b PCS 3F regeneration
//! (T1.0), since 3F uses blake3 Merkle today.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_bus::BusInteractionBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_poseidon2b::{generate_poseidon2b_trace, poseidon2b_permutation, trace::WIDTH as P2B_WIDTH};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN;
use std::time::Instant;

use p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir;
use p3_recursion::frost_gkr::binary_verifier_air::{
    COL_PAIR0, COL_PAIR1, COL_ALPHA, COL_NEXT, COL_SEL, COL_IS_LAST,
    COL_S0, COL_MERKLE_SIB_BASE, COL_MERKLE_PARENT_BASE,
};
use p3_recursion::frost_gkr::binary_aggregation_air::{
    BinaryAggregationBusAir, AGG_WIDTH, AGG_PUBLIC,
    ROOT_A_IDX, ROOT_B_IDX,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

const COMBINED_WIDTH: usize = 1024;
const TRACE_ROWS: usize = 4;
const FRI_HALF_COLS: usize = 18;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum CombinedAir {
    Poseidon2b,
    Aggregation,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize {
        match self {
            Self::Poseidon2b => COMBINED_WIDTH,
            Self::Aggregation => AGG_WIDTH,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::Poseidon2b => 8,
            Self::Aggregation => AGG_PUBLIC,
        }
    }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::Poseidon2b => Poseidon2bBusAir.eval(b),
            Self::Aggregation => BinaryAggregationBusAir.eval(b),
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

fn merkle_parent(curr: F, sib: F) -> F {
    let state_in = [curr, sib, blk(0), blk(MERKLE_DOMAIN)];
    let mut state_out = state_in;
    poseidon2b_permutation(&mut state_out);
    state_out[0] + state_out[1]
}

fn make_producer(curr: F, sib: F) -> (RowMajorMatrix<F>, Vec<F>) {
    let state_in = [curr, sib, blk(0), blk(MERKLE_DOMAIN)];
    let mut state_out = state_in;
    poseidon2b_permutation(&mut state_out);
    let base = generate_poseidon2b_trace(state_in);
    let mut values = Vec::with_capacity(TRACE_ROWS * P2B_WIDTH);
    for _ in 0..TRACE_ROWS {
        values.extend_from_slice(&base.values);
    }
    let trace = RowMajorMatrix::new(values, COMBINED_WIDTH);
    let public = vec![
        state_in[0], state_in[1], state_in[2], state_in[3],
        state_out[0], state_out[1], state_out[2], state_out[3],
    ];
    (trace, public)
}

/// Build one half's FRI verifier trace (4 rows × 18 cols), values for last row
/// have is_last=1 and s[fp_idx]=1.
fn build_half_trace(
    pair0: F, pair1: F, alpha: F, sel: F,
    sibs: [F; 4], parents: [F; 4],
    fp_idx: usize,
) -> Vec<Vec<F>> {
    let fold_out = pair0 + sel * (pair0 + pair1) + alpha * (pair1 + sel * (pair0 + pair1));

    let mut rows = Vec::with_capacity(TRACE_ROWS);
    for r in 0..TRACE_ROWS {
        let mut row = vec![F::ZERO; FRI_HALF_COLS];
        row[COL_PAIR0] = pair0;
        row[COL_PAIR1] = pair1;
        row[COL_ALPHA] = alpha;
        row[COL_NEXT] = fold_out;
        row[COL_SEL] = sel;
        let is_last = if r == TRACE_ROWS - 1 { F::ONE } else { F::ZERO };
        row[COL_IS_LAST] = is_last;
        if r == TRACE_ROWS - 1 {
            row[COL_S0 + fp_idx] = F::ONE;
        }
        for i in 0..4 {
            row[COL_MERKLE_SIB_BASE + i] = sibs[i];
            row[COL_MERKLE_PARENT_BASE + i] = parents[i];
        }
        rows.push(row);
    }
    rows
}

fn interleave_halves(a: Vec<Vec<F>>, b: Vec<Vec<F>>) -> RowMajorMatrix<F> {
    let mut values = Vec::with_capacity(TRACE_ROWS * AGG_WIDTH);
    for r in 0..TRACE_ROWS {
        values.extend_from_slice(&a[r]);
        values.extend_from_slice(&b[r]);
    }
    RowMajorMatrix::new(values, AGG_WIDTH)
}

fn build_chain(leaf: F, sibs: [F; 4]) -> [F; 4] {
    let mut parents = [F::ZERO; 4];
    let mut curr = leaf;
    for i in 0..4 {
        parents[i] = merkle_parent(curr, sibs[i]);
        curr = parents[i];
    }
    parents
}

fn build_aggregation_case() -> (
    RowMajorMatrix<F>, Vec<F>,                      // consumer trace + public
    Vec<(RowMajorMatrix<F>, Vec<F>)>,                // producers (8)
) {
    // Half A
    let p0a = blk(0x11); let p1a = blk(0x22); let aa = blk(0x33);
    let sel_a = F::ONE;
    let sibs_a = [blk(0xA0), blk(0xA1), blk(0xA2), blk(0xA3)];
    let parents_a = build_chain(p0a, sibs_a);
    let fold_a = p0a + sel_a * (p0a + p1a) + aa * (p1a + sel_a * (p0a + p1a));
    let fp_idx_a = 2usize;
    let mut fp_a = [F::ZERO; 4];
    fp_a[fp_idx_a] = fold_a;
    let trace_a = build_half_trace(p0a, p1a, aa, sel_a, sibs_a, parents_a, fp_idx_a);

    // Half B
    let p0b = blk(0x44); let p1b = blk(0x55); let ab = blk(0x66);
    let sel_b = F::ONE;
    let sibs_b = [blk(0xB0), blk(0xB1), blk(0xB2), blk(0xB3)];
    let parents_b = build_chain(p0b, sibs_b);
    let fold_b = p0b + sel_b * (p0b + p1b) + ab * (p1b + sel_b * (p0b + p1b));
    let fp_idx_b = 1usize;
    let mut fp_b = [F::ZERO; 4];
    fp_b[fp_idx_b] = fold_b;
    let trace_b = build_half_trace(p0b, p1b, ab, sel_b, sibs_b, parents_b, fp_idx_b);

    let consumer_trace = interleave_halves(trace_a, trace_b);

    let root_a = parents_a[3];
    let root_b = parents_b[3];
    let mut public = Vec::with_capacity(AGG_PUBLIC);
    public.extend_from_slice(&fp_a);
    public.extend_from_slice(&fp_b);
    public.push(root_a);
    public.push(root_b);
    assert_eq!(public.len(), AGG_PUBLIC);
    assert_eq!(public[ROOT_A_IDX], root_a);
    assert_eq!(public[ROOT_B_IDX], root_b);

    // 8 producers: 4 for A, 4 for B
    let mut producers = Vec::with_capacity(8);
    let mut curr = p0a;
    for i in 0..4 {
        producers.push(make_producer(curr, sibs_a[i]));
        curr = parents_a[i];
    }
    let mut curr = p0b;
    for i in 0..4 {
        producers.push(make_producer(curr, sibs_b[i]));
        curr = parents_b[i];
    }

    (consumer_trace, public, producers)
}

fn arity_for() -> usize {
    // 1 consumer (4×36) + 8 producers (4×1024 each)
    let total = TRACE_ROWS * AGG_WIDTH + 8 * TRACE_ROWS * COMBINED_WIDTH;
    total.next_power_of_two().trailing_zeros() as usize
}

fn prove_and_verify(
    consumer_trace: RowMajorMatrix<F>,
    consumer_pub: Vec<F>,
    producers: Vec<(RowMajorMatrix<F>, Vec<F>)>,
    expect_ok: bool,
) {
    let arity = arity_for();
    println!("arity = {}", arity);
    let config = build_config(arity);

    let consumer_air = CombinedAir::Aggregation;
    let producer_air = CombinedAir::Poseidon2b;
    let airs: Vec<&CombinedAir> = std::iter::once(&consumer_air)
        .chain(std::iter::repeat(&producer_air).take(8))
        .collect();

    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &airs, &mut ch_setup).unwrap();

    let mut instances = Vec::new();
    instances.push(ProverInstance::new(
        &consumer_air, Table::new(consumer_trace.transpose()), &pk, &consumer_pub,
    ));
    for (t, p) in &producers {
        instances.push(ProverInstance::new(
            &producer_air, Table::new(t.transpose()), &pk, p,
        ));
    }
    let mut ch_prove = make_ch();
    let start = Instant::now();
    let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(&config, ProverInstances::new(instances), 0, &mut ch_prove)
    }));

    match prove_result {
        Ok(Ok(proof)) => {
            println!("PROVE OK, {:?}, size ~{} B",
                start.elapsed(), core::mem::size_of_val(&proof));

            let mut verif = Vec::new();
            verif.push(VerifierInstance::new(&consumer_air, &vk, 2, &consumer_pub));
            for (_, p) in &producers {
                verif.push(VerifierInstance::new(&producer_air, &vk, 2, p));
            }
            let mut ch_v = make_ch();
            let start = Instant::now();
            let r = verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_v);
            match r {
                Ok(()) => {
                    println!("VERIFY OK, {:?}", start.elapsed());
                    assert!(expect_ok, "expected fail but got pass");
                }
                Err(e) => {
                    println!("VERIFY ERR: {:?}", e);
                    assert!(!expect_ok, "expected pass but got fail");
                }
            }
        }
        Ok(Err(e)) => {
            println!("PROVE ERR: {:?}", e);
            assert!(!expect_ok, "expected pass but got prove err");
        }
        Err(_) => {
            println!("PROVE PANIC");
            assert!(!expect_ok, "expected pass but got panic");
        }
    }
}

#[test]
#[ignore]
fn t1_1_two_to_one_aggregation() {
    let (consumer_trace, consumer_pub, producers) = build_aggregation_case();
    prove_and_verify(consumer_trace, consumer_pub, producers, true);
}

#[test]
#[ignore]
fn t1_1_tampered_root_rejected() {
    let (consumer_trace, mut consumer_pub, producers) = build_aggregation_case();
    // Tamper expected root A — constraint should fail
    consumer_pub[ROOT_A_IDX] = consumer_pub[ROOT_A_IDX] + F::ONE;
    prove_and_verify(consumer_trace, consumer_pub, producers, false);
}
