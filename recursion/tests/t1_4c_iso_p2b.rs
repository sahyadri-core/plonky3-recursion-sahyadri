//! Isolate P2B trace in MultiStark alone. Find where FinalSumMismatch comes from.
use p3_air::BaseAir;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{prove, setup, verify, ProverInstance, ProverInstances, VerifierInstance, VerifierInstances};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_poseidon2b::{generate_poseidon2b_trace, poseidon2b_permutation, trace::WIDTH as P2B_WIDTH};
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;
use p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir;

type F = BinaryField128;
type E = BinaryField128;
type M = GroupedCodewordMmcs<Poseidon2bMmcs>;
type ME = GroupedCodewordMmcs<Poseidon2bMmcs>;
type Ch = p3_test_utils::binary_field_params::blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }
fn make_ch() -> Ch { Ch::from_hasher(vec![], p3_test_utils::binary_field_params::blake3::byte_hash()) }

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
}

fn pad_trace_zeros(trace: RowMajorMatrix<F>, min_cells: usize) -> RowMajorMatrix<F> {
    let w = trace.width();
    let h = trace.height();
    let cells = h * w;
    if cells >= min_cells { return trace; }
    let target_rows = (min_cells / w + 1).next_power_of_two().max(h);
    let mut vals = trace.values.clone();
    vals.resize(target_rows * w, F::ZERO);
    RowMajorMatrix::new(vals, w)
}

fn pad_trace_repeat_last(trace: RowMajorMatrix<F>, min_cells: usize) -> RowMajorMatrix<F> {
    let w = trace.width();
    let h = trace.height();
    let cells = h * w;
    if cells >= min_cells { return trace; }
    let target_rows = (min_cells / w + 1).next_power_of_two().max(h);
    let mut vals = trace.values.clone();
    // Capture last row
    let last_row = vals[(h-1) * w..h * w].to_vec();
    vals.resize(target_rows * w, F::ZERO);
    // Fill padding with last row repeated
    for r in h..target_rows {
        for c in 0..w {
            vals[r * w + c] = last_row[c];
        }
    }
    RowMajorMatrix::new(vals, w)
}

struct Cfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for Cfg {
    type Val = F; type Challenge = E; type Challenger = Ch;
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

fn run_iso(pad_strategy: &str, min_cells: usize) -> bool {
    let a = blk(0xCAFE);
    let b = blk(0xBABE);
    let mut state_in = [blk(0); 4];
    state_in[0] = a;
    state_in[1] = b;
    state_in[3] = blk(0x4D45_524B_4C45_0001u128);  // MERKLE_DOMAIN

    let mut state_out = state_in;
    poseidon2b_permutation(&mut state_out);

    let trace_raw = generate_poseidon2b_trace(state_in);
    let raw_h = trace_raw.height();
    let raw_w = trace_raw.width();
    println!("[{}] raw P2B trace: {}x{}", pad_strategy, raw_h, raw_w);

    let trace = match pad_strategy {
        "zeros" => pad_trace_zeros(trace_raw, min_cells),
        "repeat_last" => pad_trace_repeat_last(trace_raw, min_cells),
        _ => panic!("unknown"),
    };
    println!("[{}] padded: {}x{}", pad_strategy, trace.height(), trace.width());

    let public = vec![
        state_in[0], state_in[1], state_in[2], state_in[3],
        state_out[0], state_out[1], state_out[2], state_out[3],
    ];

    let p2b_w = P2B_WIDTH;
    let total_cells = trace.height() * p2b_w;
    let arity = total_cells.next_power_of_two().trailing_zeros() as usize;
    let cfg = Cfg { pcs: build_pcs(arity.max(15)) };
    let air = Poseidon2bBusAir;

    let mut ch_s = make_ch();
    let (pk, vk) = setup(&cfg, &[&air], &mut ch_s).unwrap();
    let log_h = trace.height().trailing_zeros() as usize;

    let i = ProverInstance::new(&air, Table::new(trace.transpose()), &pk, &public);
    let mut ch_p = make_ch();
    let proof = prove(&cfg, ProverInstances::new(vec![i]), 0, &mut ch_p).expect("prove");

    let v = VerifierInstance::new(&air, &vk, log_h, &public);
    let mut ch_v = make_ch();
    verify(&cfg, VerifierInstances::new(vec![v]), &proof, 0, &mut ch_v).is_ok()
}

#[test]
#[ignore]
fn iso_p2b_zeros_padding() {
    let ok = run_iso("zeros", 1 << 15);
    println!("P2B with zero-padding: {}", if ok { "PASS" } else { "FAIL" });
    assert!(ok, "P2B with zero-padding failed");
}

#[test]
#[ignore]
fn iso_p2b_repeat_last_padding() {
    let ok = run_iso("repeat_last", 1 << 15);
    println!("P2B with repeat-last padding: {}", if ok { "PASS" } else { "FAIL" });
    assert!(ok, "P2B with repeat-last padding failed");
}
