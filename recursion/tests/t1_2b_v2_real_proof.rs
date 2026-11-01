//! BinaryVerifierAirV2 with real proof data from T1.2b extraction.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_dft::domain_point;
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{
    BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs,
    take_last_betas_bytes, take_last_indices,
};
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
use p3_recursion::frost_gkr::binary_verifier_air_v2::{
    BinaryVerifierAirV2, WIDTH as V2_WIDTH,
    COL_LO, COL_HI, COL_BETA, COL_X, COL_NEXT, COL_IS_LAST,
};

type F = BinaryField128;
type E = BinaryField128;
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

#[derive(Clone, Copy)]
pub enum SrcAir { SumcheckVerifier, FriVerifier }

impl<Fb> BaseAir<Fb> for SrcAir {
    fn width(&self) -> usize {
        match self { Self::SumcheckVerifier => SC_WIDTH, Self::FriVerifier => FRI_WIDTH }
    }
    fn num_public_values(&self) -> usize {
        match self { Self::SumcheckVerifier => 2, Self::FriVerifier => 4 }
    }
}

impl<AB> Air<AB> for SrcAir
where AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder {
    fn eval(&self, b: &mut AB) {
        match self {
            Self::SumcheckVerifier => SumcheckVerifierAir.eval(b),
            Self::FriVerifier => BinaryVerifierAir.eval(b),
        }
    }
}

struct SrcCfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for SrcCfg {
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

struct V2Cfg { pcs: BinaryPcs<F, E, M, ME> }
impl MultiStarkConfig for V2Cfg {
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

fn build_config(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Tree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    let round = RoundTree::new(blake3::FieldHash::new(blake3::byte_hash()), blake3::Compress::new(blake3::byte_hash()), 0);
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
}

fn sc_fold(h0: F, h_inf: F, alpha: F, claimed: F) -> F {
    h0 + (claimed + h_inf) * alpha + h_inf * alpha * alpha
}

fn build_sc_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let h0 = blk(2); let h_inf = blk(0); let alpha = blk(2);
    let claimed_0 = blk(1);
    let next_0 = sc_fold(h0, h_inf, alpha, claimed_0);
    let claimed_1 = next_0;
    let mut v = vec![F::ZERO; 2 * SC_WIDTH];
    v[SC_H0] = h0; v[SC_H_INF] = h_inf; v[SC_ALPHA] = alpha;
    v[SC_CLAIMED] = claimed_0; v[SC_NEXT] = next_0; v[SC_IS_FIRST] = F::ONE;
    v[SC_WIDTH + SC_H0] = claimed_1; v[SC_WIDTH + SC_CLAIMED] = claimed_1;
    v[SC_WIDTH + SC_NEXT] = claimed_1; v[SC_WIDTH + SC_IS_LAST] = F::ONE;
    (RowMajorMatrix::new(v, SC_WIDTH), vec![claimed_0, claimed_1])
}

fn build_fri_trace() -> (RowMajorMatrix<F>, Vec<F>) {
    let p0 = blk(10); let p1 = blk(20); let alpha = blk(30);
    let x = p0 + p1; let y = x; let z = alpha * (p1 + y);
    let fo = p0 + y + z;
    let mut v = vec![F::ZERO; 4 * FRI_WIDTH];
    v[FRI_PAIR0] = p0; v[FRI_PAIR1] = p1; v[FRI_ALPHA] = alpha;
    v[FRI_NEXT] = fo; v[FRI_SEL] = F::ONE;
    v[3 * FRI_WIDTH + 5] = F::ONE; v[3 * FRI_WIDTH + 6] = F::ONE;
    (RowMajorMatrix::new(v, FRI_WIDTH), vec![F::ZERO; 4])
}

fn build_v2_trace_from_real_proof(
    proof: &p3_multi_stark::MultiStarkProof<SrcCfg>,
    indices: &[usize],
    betas: &[F],
) -> RowMajorMatrix<F> {
    let opening = &proof.opening;
    let base = &opening.base_opened_values;
    let rounds = &opening.rounds;
    let final_cw = opening.final_codeword.as_slice();

    let num_batches = betas.len();
    let num_queries = indices.len();
    let total_rows = num_batches * num_queries;
    let target_rows = total_rows.next_power_of_two().max(2);

    let mut values = vec![F::ZERO; target_rows * V2_WIDTH];

    for batch in 0..num_batches {
        let curr_rows: &Vec<Vec<F>> = if batch == 0 { base } else { &rounds[batch - 1].opened_values };
        for q in 0..num_queries {
            let index = indices[q];
            let next_position = index >> (batch + 1);
            let x = domain_point::<F>(next_position << 1);
            let beta = betas[batch];

            let lo = curr_rows[2 * q][0];
            let hi = curr_rows[2 * q + 1][0];

            // Compute expected next (matches real fold_pair)
            let f1 = lo + hi;
            let f0 = lo + x * f1;
            let expected_next = beta * (f0 + f1) + f0;

            // Verify against real data (sanity)
            let real_next = if batch + 1 < num_batches {
                let np_size = 1usize << 1;  // arity 1, so 2 symbols
                let offset = next_position & (np_size - 1);
                rounds[batch].opened_values[q * np_size + offset][0]
            } else {
                final_cw[next_position & (final_cw.len() - 1)]
            };

            assert_eq!(expected_next, real_next,
                "Fold mismatch at batch={} q={}", batch, q);

            let row = batch * num_queries + q;
            values[row * V2_WIDTH + COL_LO] = lo;
            values[row * V2_WIDTH + COL_HI] = hi;
            values[row * V2_WIDTH + COL_BETA] = beta;
            values[row * V2_WIDTH + COL_X] = x;
            values[row * V2_WIDTH + COL_NEXT] = expected_next;
            if batch == num_batches - 1 && q == num_queries - 1 {
                values[row * V2_WIDTH + COL_IS_LAST] = F::ONE;
            }
        }
    }

    RowMajorMatrix::new(values, V2_WIDTH)
}

#[test]
#[ignore]
fn v2_proves_real_fold_data() {
    // ===== 1. Generate source proof =====
    let (sc_trace, sc_public) = build_sc_trace();
    let (fri_trace, fri_public) = build_fri_trace();
    let raw = 2 * SC_WIDTH + 4 * FRI_WIDTH;
    let src_arity = raw.next_power_of_two().trailing_zeros() as usize;
    let src_pcs = build_config(src_arity);

    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;
    let src_cfg = SrcCfg { pcs: src_pcs };
    let mut ch_s = make_ch();
    let (pk, vk) = setup(&src_cfg, &[&sc_air, &fri_air], &mut ch_s).unwrap();

    let sc_inst = ProverInstance::new(&sc_air, Table::new(sc_trace.transpose()), &pk, &sc_public);
    let fri_inst = ProverInstance::new(&fri_air, Table::new(fri_trace.transpose()), &pk, &fri_public);
    let mut ch_p = make_ch();
    let proof = prove(&src_cfg, ProverInstances::new(vec![sc_inst, fri_inst]), 0, &mut ch_p).unwrap();

    // ===== 2. Extract indices + betas =====
    let _ = take_last_indices();
    let _ = take_last_betas_bytes();
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_public),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_public),
    ];
    let mut ch_v = make_ch();
    verify(&src_cfg, VerifierInstances::new(verif), &proof, 0, &mut ch_v).unwrap();

    let indices = take_last_indices().unwrap();
    let betas_bytes = take_last_betas_bytes().unwrap();
    let betas: Vec<F> = betas_bytes.iter().map(|b| {
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b[..16]);
        F::from_le_bytes(arr)
    }).collect();

    println!("Extracted: {} indices, {} betas", indices.len(), betas.len());

    // ===== 3. Build V2 trace from real data =====
    let v2_trace = build_v2_trace_from_real_proof(&proof, &indices, &betas);
    let v2_rows = v2_trace.height();
    println!("V2 trace: {} rows x {} cols", v2_rows, v2_trace.width());

    // ===== 4. Prove with BinaryVerifierAirV2 =====
    let v2_air = BinaryVerifierAirV2;
    let v2_raw = v2_rows * V2_WIDTH;
    let v2_arity = v2_raw.next_power_of_two().trailing_zeros() as usize;
    let v2_pcs = build_config(v2_arity);
    let v2_cfg = V2Cfg { pcs: v2_pcs };
    let mut ch_v2s = make_ch();
    let (v2_pk, v2_vk) = setup(&v2_cfg, &[&v2_air], &mut ch_v2s).unwrap();

    let v2_inst = ProverInstance::new(&v2_air, Table::new(v2_trace.transpose()), &v2_pk, &[]);
    let mut ch_v2p = make_ch();
    let start = Instant::now();
    let v2_proof = prove(&v2_cfg, ProverInstances::new(vec![v2_inst]), 0, &mut ch_v2p).unwrap();
    println!("V2 PROVE: {:?}, ~{}B", start.elapsed(), core::mem::size_of_val(&v2_proof));

    // ===== 5. Verify =====
    let log_h = v2_rows.trailing_zeros() as usize;
    let v2_verif = VerifierInstance::new(&v2_air, &v2_vk, log_h, &[]);
    let mut ch_v2v = make_ch();
    let start = Instant::now();
    verify(&v2_cfg, VerifierInstances::new(vec![v2_verif]), &v2_proof, 0, &mut ch_v2v)
        .expect("V2 proof must verify");
    println!("V2 VERIFY: {:?}", start.elapsed());

    println!("\n=== BinaryVerifierAirV2 with REAL proof data PASS ===");
    println!("{} fold relations proven in-circuit", v2_rows);
}
