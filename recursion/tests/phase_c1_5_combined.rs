//! Phase C1.5: combined MultiStark bus balance (BinaryVerifier + Poseidon2b)
//!
//! Reuses 3D2d's producer pattern verbatim:
//!   - 4 × Poseidon2bBusAir instances, each 4-identical-row trace
//!   - `Boolean(is_last_row)` activation → 1 push per instance
//!
//! Consumer swapped to BinaryVerifierBusAir (depth-4 unrolled):
//!   - 4-identical-row trace, `Boolean(is_last_row)` → 4 pulls from last row
//!
//! Balance: 4 pulls == 4 pushes.

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
    BinaryVerifierBusAir,
    COL_PAIR0, COL_PAIR1, COL_ALPHA, COL_NEXT, COL_SEL, COL_IS_LAST,
    COL_MERKLE_SIB_BASE, COL_MERKLE_PARENT_BASE,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

const COMBINED_WIDTH: usize = 1024;
const COMBINED_PUBLIC: usize = 8;
const MERKLE_DEPTH_C: usize = 4;
const TRACE_ROWS: usize = 4; // match 3D2d; both sides 4 identical rows

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum CombinedAir {
    Poseidon2b,
    BinaryVerifier,
}

impl<F> BaseAir<F> for CombinedAir {
    fn width(&self) -> usize { COMBINED_WIDTH }
    fn num_public_values(&self) -> usize { COMBINED_PUBLIC }
}

impl<AB> Air<AB> for CombinedAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::Poseidon2b => Poseidon2bBusAir.eval(b),
            Self::BinaryVerifier => BinaryVerifierBusAir.eval(b),
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

// --- Producer side (verbatim from 3D2d pattern) ---

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
    let base_values: Vec<F> = base.values;
    let mut values = Vec::with_capacity(TRACE_ROWS * P2B_WIDTH);
    for _ in 0..TRACE_ROWS {
        values.extend_from_slice(&base_values);
    }
    let trace = RowMajorMatrix::new(values, COMBINED_WIDTH);

    let public = vec![
        state_in[0], state_in[1], state_in[2], state_in[3],
        state_out[0], state_out[1], state_out[2], state_out[3],
    ];
    (trace, public)
}

// --- Consumer side (BinaryVerifierBusAir, depth-4, 4 identical rows) ---

fn build_consumer_trace(leaf: F, sibs: [F; 4], parents: [F; 4]) -> RowMajorMatrix<F> {
    let mut base = vec![F::ZERO; COMBINED_WIDTH];

    // FRI fold dummy columns (must satisfy fold constraint on every row)
    let p1 = blk(0);
    let a = blk(0);
    base[COL_PAIR0] = leaf;
    base[COL_PAIR1] = p1;
    base[COL_ALPHA] = a;
    let x = leaf + p1;
    let y = x; // sel = 1
    let z = a * (p1 + y);
    base[COL_NEXT] = leaf + y + z;
    base[COL_SEL] = F::ONE;
    base[COL_IS_LAST] = F::ZERO; // not last FRI round for this row

    for i in 0..MERKLE_DEPTH_C {
        base[COL_MERKLE_SIB_BASE + i] = sibs[i];
        base[COL_MERKLE_PARENT_BASE + i] = parents[i];
    }

    // Replicate to TRACE_ROWS identical rows (matches producer height).
    // Boolean(is_last_row) on bus Pull fires only on last row → 4 pulls total.
    let mut values = Vec::with_capacity(TRACE_ROWS * COMBINED_WIDTH);
    for _ in 0..TRACE_ROWS {
        values.extend_from_slice(&base);
    }
    RowMajorMatrix::new(values, COMBINED_WIDTH)
}

fn consumer_public() -> Vec<F> { vec![F::ZERO; COMBINED_PUBLIC] }

// --- Setup + prove helpers ---

fn setup_airs<'a>(consumer: &'a CombinedAir, producer: &'a CombinedAir) -> Vec<&'a CombinedAir> {
    std::iter::once(consumer)
        .chain(std::iter::repeat(producer).take(4))
        .collect()
}

fn arity_for() -> usize {
    // 5 tables × 4 rows × 1024 cols = 20480 → next_pow2 32768 → log2 = 15
    let cells = 5 * TRACE_ROWS * COMBINED_WIDTH;
    cells.next_power_of_two().trailing_zeros() as usize
}

fn prove_combined(
    consumer_trace: RowMajorMatrix<F>,
    consumer_pub: Vec<F>,
    producers: Vec<(RowMajorMatrix<F>, Vec<F>)>,
    expect_ok: bool,
) {
    let arity = arity_for();
    println!("arity = {}", arity);

    let config = build_config(arity);
    let consumer_air = CombinedAir::BinaryVerifier;
    let producer_air = CombinedAir::Poseidon2b;
    let airs = setup_airs(&consumer_air, &producer_air);

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
                    println!("VERIFY OK, {:?} — bus balance held", start.elapsed());
                    assert!(expect_ok, "prove+verify succeeded but expect_ok=false");
                }
                Err(e) => {
                    println!("VERIFY ERR: {:?}", e);
                    assert!(!expect_ok, "verify failed but expect_ok=true");
                }
            }
        }
        Ok(Err(e)) => {
            println!("PROVE ERR: {:?}", e);
            assert!(!expect_ok, "prove failed but expect_ok=true");
        }
        Err(_) => {
            println!("PROVE PANIC — constraint or bus failure");
            assert!(!expect_ok, "prove panicked but expect_ok=true");
        }
    }
}

fn build_path() -> (F, [F; 4], [F; 4]) {
    let leaf = blk(0xCAFE);
    let sibs: [F; 4] = [blk(0x100), blk(0x200), blk(0x300), blk(0x400)];
    let mut parents = [F::ZERO; 4];
    let mut curr = leaf;
    for i in 0..4 {
        parents[i] = merkle_parent(curr, sibs[i]);
        curr = parents[i];
    }
    (leaf, sibs, parents)
}

fn build_producers(leaf: F, sibs: [F; 4], parents: [F; 4]) -> Vec<(RowMajorMatrix<F>, Vec<F>)> {
    let mut v = Vec::new();
    let mut curr = leaf;
    for i in 0..4 {
        v.push(make_producer(curr, sibs[i]));
        curr = parents[i];
    }
    v
}

#[test]
#[ignore]
fn c1_5_combined_prove_verify() {
    let (leaf, sibs, parents) = build_path();
    println!("merkle root = {:?}", parents[3]);

    let consumer_trace = build_consumer_trace(leaf, sibs, parents);
    let consumer_pub = consumer_public();
    let producers = build_producers(leaf, sibs, parents);

    prove_combined(consumer_trace, consumer_pub, producers, true);
}

#[test]
#[ignore]
fn c1_5_tampered_parent_rejected() {
    let (leaf, sibs, parents) = build_path();

    let mut consumer_trace = build_consumer_trace(leaf, sibs, parents);
    // Flip parent[2] in EVERY row (since replicated). Bus Pull at level 2 will
    // emit a tuple that does not match producer's Push at level 2.
    for row in 0..TRACE_ROWS {
        let idx = row * COMBINED_WIDTH + COL_MERKLE_PARENT_BASE + 2;
        consumer_trace.values[idx] = parents[2] + F::ONE;
    }

    let consumer_pub = consumer_public();
    let producers = build_producers(leaf, sibs, parents);

    prove_combined(consumer_trace, consumer_pub, producers, false);
}
