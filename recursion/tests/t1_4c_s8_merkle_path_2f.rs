//! Phase 2b-2e: MerklePathBusAir2F (`[F;2]` digests) — bus balance with
//! Poseidon2b producers, using the same `MerkleTreeMmcs` compression as
//! `Poseidon2bFieldCompress`.
//!
//! # What this proves
//! For a single tree level with a 2-field digest, the MP2 AIR's 2 Pulls
//! `(curr0,sib0,parent0)` + `(curr1,sib1,parent1)` are exactly balanced
//! by 2 `Poseidon2bBusAir` pushes where `parentL = compress(currL, sibL)`.
//!
//! # Next (Phase 2b-2f, next session)
//! Full S7 rebuild: MP2 over N levels + V2 + SC + 2N P2B, then import_native.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
};
use p3_bus::BusInteractionBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_poseidon2b::poseidon2b_permutation;
use p3_symmetric::PseudoCompressionFunction;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;

use sahyadri_fri_binius::merkle_path_bus_air_2f::{
    MerklePathBusAir2F, MP2_CURR0, MP2_CURR1, MP2_SIB0, MP2_SIB1,
    MP2_PARENT0, MP2_PARENT1, MP2_IS_REAL, MP2_WIDTH,
};
use sahyadri_fri_binius::poseidon2b_compression::MERKLE_DOMAIN;
use sahyadri_fri_binius::poseidon2b_hasher::Poseidon2bFieldCompress;
use p3_recursion::frost_gkr::poseidon2b_bus_air::Poseidon2bBusAir;

type F = BinaryField128;
type E = BinaryField128;
type M = GroupedCodewordMmcs<sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs>;
type ME = GroupedCodewordMmcs<sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs>;
type Ch = blake3::LevelChallenger<F>;

const P2B_WIDTH: usize = 1024;
const P2B_ROWS: usize = 32;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }
fn make_ch() -> Ch { Ch::from_hasher(vec![], blake3::byte_hash()) }

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    BinaryPcs::new(
        cfg,
        GroupedCodewordMmcs::new(sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs::new(), 1),
        GroupedCodewordMmcs::new(sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs::new(), 1),
    ).unwrap()
}

fn build_p2b_trace(left: F, right: F, domain: F) -> RowMajorMatrix<F> {
    let state_in = [left, right, F::ZERO, domain];
    let base = p3_poseidon2b::generate_poseidon2b_trace(state_in);
    let base_values = base.values;
    let mut values = Vec::with_capacity(P2B_ROWS * P2B_WIDTH);
    for _ in 0..P2B_ROWS { values.extend_from_slice(&base_values); }
    RowMajorMatrix::new(values, P2B_WIDTH)
}

fn build_p2b_public(left: F, right: F, domain: F) -> Vec<F> {
    let state_in = [left, right, F::ZERO, domain];
    let mut state_out = state_in;
    poseidon2b_permutation(&mut state_out);
    vec![state_in[0], state_in[1], state_in[2], state_in[3],
         state_out[0], state_out[1], state_out[2], state_out[3]]
}

#[derive(Clone, Copy)]
pub enum CombinedAir { MP2, P2B }

impl<Fb> BaseAir<Fb> for CombinedAir {
    fn width(&self) -> usize {
        match self { Self::MP2 => MP2_WIDTH, Self::P2B => P2B_WIDTH }
    }
    fn num_public_values(&self) -> usize {
        match self { Self::MP2 => 0, Self::P2B => 8 }
    }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB> for CombinedAir {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::MP2 => MerklePathBusAir2F.eval(b),
            Self::P2B => Poseidon2bBusAir.eval(b),
        }
    }
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

#[test]
#[ignore]
fn merkle_path_2f_bus_balance_one_level() {
    println!("=== Phase 2b-2e: MP2 (2-field digest) bus balance ===");

    // One tree level: (curr0, curr1) + (sib0, sib1)
    let curr = [blk(3), blk(5)];
    let sib = [blk(7), blk(11)];
    let compress = Poseidon2bFieldCompress;
    let parent: [F; 2] = {
        // Match Poseidon2bFieldCompress lane semantics
        let c = compress.compress([
            // Lane 0 in first 16B, lane 1 in second 16B
            {
                let mut a = [0u8; 32];
                a[..16].copy_from_slice(&unsafe { core::mem::transmute_copy::<F, [u8; 16]>(&curr[0]) });
                a[16..].copy_from_slice(&unsafe { core::mem::transmute_copy::<F, [u8; 16]>(&curr[1]) });
                a
            },
            {
                let mut a = [0u8; 32];
                a[..16].copy_from_slice(&unsafe { core::mem::transmute_copy::<F, [u8; 16]>(&sib[0]) });
                a[16..].copy_from_slice(&unsafe { core::mem::transmute_copy::<F, [u8; 16]>(&sib[1]) });
                a
            },
        ]);
        [
            F::from_le_bytes(c[..16].try_into().unwrap()),
            F::from_le_bytes(c[16..].try_into().unwrap()),
        ]
    };
    println!("curr = [{:?}, {:?}], sib = [{:?}, {:?}], parent = [{:?}, {:?}]",
        curr[0], curr[1], sib[0], sib[1], parent[0], parent[1]);

    // MP2 trace: 1 real row + 1 padding row (power-of-2)
    let mp_rows = 2;
    let mut mp_values = vec![F::ZERO; mp_rows * MP2_WIDTH];
    mp_values[MP2_CURR0] = curr[0];
    mp_values[MP2_CURR1] = curr[1];
    mp_values[MP2_SIB0] = sib[0];
    mp_values[MP2_SIB1] = sib[1];
    mp_values[MP2_PARENT0] = parent[0];
    mp_values[MP2_PARENT1] = parent[1];
    mp_values[MP2_IS_REAL] = F::ONE;
    let mp_trace = RowMajorMatrix::new(mp_values, MP2_WIDTH);

    // 2 P2B producers: lane 0 (curr[0], sib[0]), lane 1 (curr[1], sib[1])
    let p2b_0 = build_p2b_trace(curr[0], sib[0], blk(MERKLE_DOMAIN));
    let p2b_1 = build_p2b_trace(curr[1], sib[1], blk(MERKLE_DOMAIN));
    let p2b_pub_0 = build_p2b_public(curr[0], sib[0], blk(MERKLE_DOMAIN));
    let p2b_pub_1 = build_p2b_public(curr[1], sib[1], blk(MERKLE_DOMAIN));

    // Total cells
    let total_cells = mp_rows * MP2_WIDTH + 2 * P2B_ROWS * P2B_WIDTH;
    let arity = (total_cells.next_power_of_two().trailing_zeros() as usize).max(15);
    println!("Total cells: {}, arity: {}", total_cells, arity);

    let cfg = Cfg { pcs: build_pcs(arity) };
    let air_mp = CombinedAir::MP2;
    let air_p0 = CombinedAir::P2B;
    let air_p1 = CombinedAir::P2B;
    let air_refs: Vec<&CombinedAir> = vec![&air_mp, &air_p0, &air_p1];

    let mut ch_s = make_ch();
    let (pk, vk) = setup(&cfg, &air_refs, &mut ch_s).unwrap();
    println!("Setup OK");

    let inst_mp = ProverInstance::new(
        &air_mp, Table::new(mp_trace.transpose()), &pk, &[],
    );
    let inst_p0 = ProverInstance::new(
        &air_p0, Table::new(p2b_0.transpose()), &pk, &p2b_pub_0,
    );
    let inst_p1 = ProverInstance::new(
        &air_p1, Table::new(p2b_1.transpose()), &pk, &p2b_pub_1,
    );

    let mut ch_p = make_ch();
    let start = std::time::Instant::now();
    let proof = prove(
        &cfg,
        ProverInstances::new(vec![inst_mp, inst_p0, inst_p1]),
        0,
        &mut ch_p,
    ).expect("prove");
    println!("PROVE OK {:?}, ~{}B", start.elapsed(), core::mem::size_of_val(&proof));

    let log_h_mp = mp_rows.trailing_zeros() as usize;
    let log_h_p2b = P2B_ROWS.trailing_zeros() as usize;
    let v_mp = VerifierInstance::new(&air_mp, &vk, log_h_mp, &[]);
    let v_p0 = VerifierInstance::new(&air_p0, &vk, log_h_p2b, &p2b_pub_0);
    let v_p1 = VerifierInstance::new(&air_p1, &vk, log_h_p2b, &p2b_pub_1);
    let mut ch_v = make_ch();
    verify(&cfg, VerifierInstances::new(vec![v_mp, v_p0, v_p1]), &proof, 0, &mut ch_v)
        .expect("verify — bus must balance: 2 MP2 pulls = 2 P2B pushes");
    println!("VERIFY OK — bus balanced");

    println!("\n=== PHASE 2b-2e PASS: MP2 bus-balanced with Poseidon2b producers ===");
    println!("Next: S7 rebuild (MP2 over N levels + V2 + SC + 2N P2B).");
}
