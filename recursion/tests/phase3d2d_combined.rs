//! Phase 3D2d + 3D2e: combined MultiStark with in-circuit bus balance.
//!
//! 3D2d: FriVerifierAirV2 + MerklePathBusAir (Pull) + Poseidon2bBusAir (Push)
//!       all in one MultiStark proof. Plonky3's bus multiset equality forces
//!       every Merkle-path tuple `(curr, sib, next)` to correspond to a real
//!       Poseidon2b compression `next = compress(curr, sib)`.
//!
//! 3D2e: tamper a Merkle-path `next` → bus unbalanced → verify rejects.

use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_poseidon2b::{generate_poseidon2b_trace, poseidon2b_permutation, trace::WIDTH as P2B_WIDTH};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::merkle::MerkleTree;
use sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN;
use p3_recursion::frost_gkr::combined_air::{
    CombinedAir, COMBINED_WIDTH, COMBINED_PUBLIC,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

// MerklePathAir column layout (from sahyadri-fri-binius)
const MP_CURR: usize = 0;
const MP_SIB: usize = 1;
const MP_NEXT: usize = 2;
const MP_SEL: usize = 3;

const MERKLE_DEPTH: usize = 4;

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

fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

/// Build a MerklePath trace (4 levels, depth 4) padded to COMBINED_WIDTH.
/// Also returns 4 Poseidon2b trace instances (one per level, 4 rows each).
fn build_traces(
    tree: &MerkleTree,
    leaf_idx: usize,
) -> (
    RowMajorMatrix<F>,             // MerklePath trace (4 × 1024)
    Vec<Vec<F>>,                    // Poseidon2b public (4 × 8)
    Vec<RowMajorMatrix<F>>,         // Poseidon2b traces (4 × [4 × 1024])
    Vec<F>,                         // MerklePath public (8)
) {
    let depth = tree.depth();
    assert_eq!(depth, MERKLE_DEPTH);

    // 1. MerklePath trace: 4 rows × 1024 cols
    let mut mp_values = vec![blk(0); MERKLE_DEPTH * COMBINED_WIDTH];
    let mut curr = tree.leaves[leaf_idx];
    let mut idx = leaf_idx;

    for level in 0..MERKLE_DEPTH {
        let sib = tree.layers[level][idx ^ 1];
        let next = tree.layers[level + 1][idx >> 1];
        let sel = blk((idx & 1) as u128);
        let row_off = level * COMBINED_WIDTH;
        mp_values[row_off + MP_CURR] = curr;
        mp_values[row_off + MP_SIB] = sib;
        mp_values[row_off + MP_NEXT] = next;
        mp_values[row_off + MP_SEL] = sel;
        // Rest of cols zero.
        curr = next;
        idx >>= 1;
    }
    let mp_trace = RowMajorMatrix::new(mp_values, COMBINED_WIDTH);

    // 2. MerklePath public: [root, 0, 0, 0, 0, 0, 0, 0]
    let mut mp_public = vec![blk(0); COMBINED_PUBLIC];
    mp_public[0] = tree.root();

    // 3. Poseidon2b traces + public, one per level.
    //    Trace: 4 rows × 1024 cols, all 4 rows identical (valid permutation).
    let mut p2b_traces = Vec::with_capacity(MERKLE_DEPTH);
    let mut p2b_publics = Vec::with_capacity(MERKLE_DEPTH);

    curr = tree.leaves[leaf_idx];
    idx = leaf_idx;
    for level in 0..MERKLE_DEPTH {
        let sib = tree.layers[level][idx ^ 1];

        // Input state: (curr, sib, 0, MERKLE_DOMAIN)
        let state_in = [curr, sib, blk(0), blk(MERKLE_DOMAIN)];
        let mut state_out = state_in;
        poseidon2b_permutation(&mut state_out);

        // Generate the one-row trace from generate_poseidon2b_trace.
        let base_trace = generate_poseidon2b_trace(state_in);
        let base_values: Vec<F> = base_trace.values;
        // Replicate to 4 rows (all identical — constraints pass on each).
        let mut values = Vec::with_capacity(4 * P2B_WIDTH);
        for _ in 0..4 {
            values.extend_from_slice(&base_values);
        }
        p2b_traces.push(RowMajorMatrix::new(values, COMBINED_WIDTH));

        // Public: [state_in_0..3, state_out_0..3]
        let public = vec![
            state_in[0], state_in[1], state_in[2], state_in[3],
            state_out[0], state_out[1], state_out[2], state_out[3],
        ];
        p2b_publics.push(public);

        curr = tree.layers[level + 1][idx >> 1];
        idx >>= 1;
    }

    (mp_trace, p2b_publics, p2b_traces, mp_public)
}

fn build_config() -> Cfg {
    // 5 tables of 4 rows × 1024 cols = 20480 cells total. Arity = 15.
    // Each table alone: 4096 cells, arity 12.
    // BinaryPcsConfig::try_new(12, ...) if witness = max per-table,
    // or try_new(15, ...) if witness = sum. Try 12 first.
    let arity = 15;
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

fn make_airs() -> [CombinedAir; 5] {
    [
        CombinedAir::MerklePath,
        CombinedAir::Poseidon2b,
        CombinedAir::Poseidon2b,
        CombinedAir::Poseidon2b,
        CombinedAir::Poseidon2b,
    ]
}

#[test]
#[ignore]
fn combined_prove_and_verify() {
    // 1. Build 16-leaf Merkle tree (depth 4)
    let leaves: Vec<_> = (0..16u128).map(blk).collect();
    let tree = MerkleTree::new(leaves);
    assert_eq!(tree.depth(), 4);

    // 2. Build traces
    let (mp_trace, p2b_publics, p2b_traces, mp_public) = build_traces(&tree, 0);

    // 3. Airs — 5 instances of CombinedAir
    let airs = make_airs();
    let air_refs: Vec<&CombinedAir> = airs.iter().collect();

    // 4. Setup
    let config = build_config();
    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &air_refs, &mut ch_setup).unwrap();

    // 5. Prover instances
    let mut instances = Vec::with_capacity(5);
    instances.push(ProverInstance::new(
        &airs[0], Table::new(mp_trace.transpose()), &pk, &mp_public,
    ));
    for i in 0..4 {
        instances.push(ProverInstance::new(
            &airs[i + 1], Table::new(p2b_traces[i].transpose()), &pk, &p2b_publics[i],
        ));
    }

    // 6. Prove
    let mut ch_prove = make_ch();
    let proof = prove(
        &config,
        ProverInstances::new(instances),
        0,
        &mut ch_prove,
    ).expect("combined prove should succeed");
    println!("PROVE OK, size ~{} B", core::mem::size_of_val(&proof));

    // 7. Verify
    let log_height = 2; // 4 rows
    let mut vi = Vec::with_capacity(5);
    vi.push(VerifierInstance::new(&airs[0], &vk, log_height, &mp_public));
    for i in 0..4 {
        vi.push(VerifierInstance::new(&airs[i + 1], &vk, log_height, &p2b_publics[i]));
    }
    let mut ch_verify = make_ch();
    verify(&config, VerifierInstances::new(vi), &proof, 0, &mut ch_verify)
        .expect("combined verify should succeed");
    println!("VERIFY OK — bus balance held");
}

#[test]
#[ignore]
fn tampered_merkle_path_rejected() {
    let leaves: Vec<_> = (0..16u128).map(blk).collect();
    let tree = MerkleTree::new(leaves);

    let (mut mp_trace, p2b_publics, p2b_traces, mp_public) = build_traces(&tree, 0);

    // Tamper row 1's `next` — makes Pull tuple (curr, sib, wrong_next) that no
    // Poseidon2b instance will produce. Bus should become unbalanced.
    let row_off = 1 * COMBINED_WIDTH;
    mp_trace.values[row_off + MP_NEXT] = blk(0xDEAD);

    let airs = make_airs();
    let air_refs: Vec<&CombinedAir> = airs.iter().collect();

    let config = build_config();
    let mut ch_setup = make_ch();
    let (pk, vk) = setup(&config, &air_refs, &mut ch_setup).unwrap();

    let mut instances = Vec::with_capacity(5);
    instances.push(ProverInstance::new(
        &airs[0], Table::new(mp_trace.transpose()), &pk, &mp_public,
    ));
    for i in 0..4 {
        instances.push(ProverInstance::new(
            &airs[i + 1], Table::new(p2b_traces[i].transpose()), &pk, &p2b_publics[i],
        ));
    }

    let mut ch_prove = make_ch();
    let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(&config, ProverInstances::new(instances), 0, &mut ch_prove)
    }));

    match prove_result {
        Ok(Ok(proof)) => {
            let log_height = 2;
            let mut vi = Vec::with_capacity(5);
            vi.push(VerifierInstance::new(&airs[0], &vk, log_height, &mp_public));
            for i in 0..4 {
                vi.push(VerifierInstance::new(&airs[i + 1], &vk, log_height, &p2b_publics[i]));
            }
            let mut ch_verify = make_ch();
            let verify_result = verify(&config, VerifierInstances::new(vi), &proof, 0, &mut ch_verify);
            assert!(verify_result.is_err(),
                "tampered Merkle path must fail verify (bus unbalanced)");
            println!("PASS: tampered Merkle path → verify rejected");
        }
        Ok(Err(_)) | Err(_) => {
            println!("PASS: tampered Merkle path → prove rejected");
        }
    }
}
