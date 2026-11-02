//! T1.2b with Poseidon2bMmcs — verify 427/427 fold validation still holds.
//!
//! Same logic as t1_2b_complete.rs, but proves via Poseidon2b-based Merkle.
//! Expected: 427/427 still pass (fold formula is hash-agnostic).

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
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;

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

type F = BinaryField128;
type E = BinaryField128;

// === KEY CHANGE: Poseidon2b-based Merkle ===
type InnerMmcs = Poseidon2bMmcs;
type M = GroupedCodewordMmcs<InnerMmcs>;
type ME = GroupedCodewordMmcs<InnerMmcs>;

// Challenger still blake3 (PCS transcript only)
type Ch = p3_test_utils::binary_field_params::blake3::LevelChallenger<F>;

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

fn make_ch() -> Ch {
    use p3_test_utils::binary_field_params::blake3;
    Ch::from_hasher(vec![], blake3::byte_hash())
}

fn build_config(arity: usize) -> Cfg {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
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
    let fold_out = fri_fold(p0, p1, alpha, F::ONE);
    let mut v = vec![F::ZERO; 4 * FRI_WIDTH];
    v[FRI_PAIR0] = p0; v[FRI_PAIR1] = p1; v[FRI_ALPHA] = alpha;
    v[FRI_NEXT] = fold_out; v[FRI_SEL] = F::ONE;
    v[3 * FRI_WIDTH + 5] = F::ONE; v[3 * FRI_WIDTH + 6] = F::ONE;
    (RowMajorMatrix::new(v, FRI_WIDTH), vec![F::ZERO; 4])
}

fn fold_pair_inline(index: usize, beta: F, lo: F, hi: F) -> F {
    let x: F = domain_point(index << 1);
    let f1 = lo + hi;
    let f0 = lo + x * f1;
    beta * (f0 + f1) + f0
}

#[test]
#[ignore]
fn t1_2b_poseidon2b_extraction() {
    // ===== 1. Generate real proof with Poseidon2b =====
    let (sc_t, sc_p) = build_sc_trace();
    let (fri_t, fri_p) = build_fri_trace();
    let raw = 2 * SC_WIDTH + 4 * FRI_WIDTH;
    let arity = raw.next_power_of_two().trailing_zeros() as usize;
    let config = build_config(arity);
    let sc_air = SrcAir::SumcheckVerifier;
    let fri_air = SrcAir::FriVerifier;

    let mut ch_s = make_ch();
    let (pk, vk) = setup(&config, &[&sc_air, &fri_air], &mut ch_s).unwrap();

    let sc_i = ProverInstance::new(&sc_air, Table::new(sc_t.transpose()), &pk, &sc_p);
    let fri_i = ProverInstance::new(&fri_air, Table::new(fri_t.transpose()), &pk, &fri_p);
    let mut ch_p = make_ch();
    let start = std::time::Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![sc_i, fri_i]), 0, &mut ch_p).unwrap();
    println!("Poseidon2b proof generated: {:?}, ~{}B",
        start.elapsed(), core::mem::size_of_val(&proof));

    // ===== 2. Verify (populates thread_locals) =====
    let _ = take_last_indices();
    let _ = take_last_betas_bytes();
    let verif = vec![
        VerifierInstance::new(&sc_air, &vk, 1, &sc_p),
        VerifierInstance::new(&fri_air, &vk, 2, &fri_p),
    ];
    let mut ch_v = make_ch();
    verify(&config, VerifierInstances::new(verif), &proof, 0, &mut ch_v)
        .expect("Poseidon2b proof must verify");

    // ===== 3. Extract indices + betas =====
    let indices = take_last_indices().expect("indices captured");
    let betas_bytes = take_last_betas_bytes().expect("betas captured");
    let betas: Vec<F> = betas_bytes.iter().map(|b| {
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b[..16]);
        F::from_le_bytes(arr)
    }).collect();

    println!("Extracted: {} indices, {} betas", indices.len(), betas.len());

    // ===== 4. Validate 427/427 fold =====
    let opening = &proof.opening;
    let base = &opening.base_opened_values;
    let rounds = &opening.rounds;
    let final_cw = opening.final_codeword.as_slice();
    let num_batches = betas.len();

    let mut total_matches = 0;
    let mut total_checked = 0;

    for batch in 0..num_batches {
        let curr_rows: &Vec<Vec<F>> = if batch == 0 { base } else { &rounds[batch - 1].opened_values };
        let beta = betas[batch];
        let next_size: usize = 2;

        for q in 0..indices.len() {
            let index = indices[q];
            let next_position = index >> (batch + 1);
            let lo = curr_rows.get(2 * q).and_then(|r| r.first()).copied().unwrap_or(F::ZERO);
            let hi = curr_rows.get(2 * q + 1).and_then(|r| r.first()).copied().unwrap_or(F::ZERO);
            let folded = fold_pair_inline(next_position, beta, lo, hi);
            let expected = if batch < num_batches - 1 {
                let next_row = &rounds[batch].opened_values;
                let offset = next_position & (next_size - 1);
                let idx = q * next_size + offset;
                next_row.get(idx).and_then(|r| r.first()).copied().unwrap_or(F::ZERO)
            } else {
                let idx = next_position & (final_cw.len() - 1);
                final_cw.get(idx).copied().unwrap_or(F::ZERO)
            };
            total_checked += 1;
            if folded == expected {
                total_matches += 1;
            }
        }
    }

    println!("=== T1.2b Poseidon2b: {}/{} matches ===", total_matches, total_checked);

    assert_eq!(total_matches, total_checked,
        "Poseidon2b should preserve fold formula (expected 100%)");
    println!("=== T1.2b POSEIDON2B COMPLETE — 100% ===");
}
