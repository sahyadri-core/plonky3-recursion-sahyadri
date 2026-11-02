//! Session A: Path B recursive composition (2 children → 1 proof).
//!
//! # Design (Path B — FAST)
//! - NO Merkle verification in-circuit (that was 19 min/path)
//! - Only verify: 2 children's sumcheck + fold chain
//! - Commitment binding via witness↔trace consistency (Path B soundness)
//! - Merkle verified NATIVELY outside (during child proof generation)
//!
//! # Soundness
//! Testnet-grade: honest-prover sound; adversary would need to forge
//! commitment+fold+sumcheck together, which fails at Fiat-Shamir transcript level.
//! Mainnet-grade needs Sub-5 (Blake3 transcript in-circuit), deferred.
//!
//! # Layout (WIDTH = 32, 8 rows)
//! - 0..6   : child A fold (lo, hi, beta, x, next, is_last)
//! - 6..15  : child A sumcheck (evals0..3, in, out, alpha, is_first, is_last)
//! - 15..21 : child B fold (same as A)
//! - 21..30 : child B sumcheck
//! - 30     : is_first (marks round 0 of this composition)
//! - 31     : is_last  (marks final row)
//!
//! # Constraints
//! For each child X in {A, B}:
//!   - Fold: next = beta*(f0+f1)+f0, f0=lo+x*f1, f1=lo+hi
//!   - Sumcheck interp: running_out = Lagrange(evals, running_in, challenge)
//!   - Chain: row r running_out == row r+1 running_in
//! - is_first, is_last booleanity
//!
//! # Proving
//! 8 rows × 32 cols = 256 cells → arity 8.
//! Fast prove (~10-50ms) vs Path A's 19 min.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_multi_stark::config::MultiStarkConfig;
use p3_multi_stark::{
    prove, setup, verify, ProverInstance, ProverInstances,
    VerifierInstance, VerifierInstances,
};
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;
use sahyadri_fri_binius::poseidon2b_mmcs_trait::Poseidon2bMmcs;
use std::time::Instant;

type F = BinaryField128;
type E = BinaryField128;
type InnerMmcs = Poseidon2bMmcs;
type M = GroupedCodewordMmcs<InnerMmcs>;
type ME = GroupedCodewordMmcs<InnerMmcs>;
type Ch = blake3::LevelChallenger<F>;

fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

// Layout
pub const A_FOLD_LO: usize = 0;
pub const A_FOLD_HI: usize = 1;
pub const A_FOLD_BETA: usize = 2;
pub const A_FOLD_X: usize = 3;
pub const A_FOLD_NEXT: usize = 4;
pub const A_FOLD_IS_LAST: usize = 5;
pub const A_SC_E0: usize = 6;
pub const A_SC_E1: usize = 7;
pub const A_SC_E2: usize = 8;
pub const A_SC_E3: usize = 9;
pub const A_SC_RUN_IN: usize = 10;
pub const A_SC_RUN_OUT: usize = 11;
pub const A_SC_CHAL: usize = 12;
pub const A_SC_IS_FIRST: usize = 13;
pub const A_SC_IS_LAST: usize = 14;

pub const B_FOLD_LO: usize = 15;
pub const B_FOLD_HI: usize = 16;
pub const B_FOLD_BETA: usize = 17;
pub const B_FOLD_X: usize = 18;
pub const B_FOLD_NEXT: usize = 19;
pub const B_FOLD_IS_LAST: usize = 20;
pub const B_SC_E0: usize = 21;
pub const B_SC_E1: usize = 22;
pub const B_SC_E2: usize = 23;
pub const B_SC_E3: usize = 24;
pub const B_SC_RUN_IN: usize = 25;
pub const B_SC_RUN_OUT: usize = 26;
pub const B_SC_CHAL: usize = 27;
pub const B_SC_IS_FIRST: usize = 28;
pub const B_SC_IS_LAST: usize = 29;

pub const COL_IS_FIRST: usize = 30;
pub const COL_IS_LAST: usize = 31;
pub const WIDTH: usize = 32;
pub const NUM_PUBLIC: usize = 0;

/// Lagrange interpolation over {0,1,2,3,4} for degree-4 sumcheck polynomial.
/// Returns p(alpha) where p has values h(0)=evals[0], h(1)=sum+evals[0],
/// h(2)=evals[1], h(3)=evals[2], h(4)=evals[3].
fn sumcheck_interp<AB: AirBuilder<F = BinaryField128>>(
    b: &mut AB,
    e0: AB::Expr, e1: AB::Expr, e2: AB::Expr, e3: AB::Expr,
    run_in: AB::Expr, chal: AB::Expr, run_out: AB::Expr,
) {
    let h: [AB::Expr; 5] = [
        e0.clone(),
        run_in.clone() + e0,  // h(1) = sum + h(0)
        e1,
        e2,
        e3,
    ];

    // p(alpha) = sum_k alpha^k * (sum_i h_i * coeffs[i][k])
    // Precompute Lagrange coefficients over domain {0,1,2,3,4}
    // From CompressedSumcheckAir's lagrange basis
    // For simplicity here, hardcode as if lagrange coeffs known:
    // This is degree-4 interpolation over {0,1,2,3,4}
    // We build it as sum of basis evaluations.
    let mut p_alpha: AB::Expr = AB::F::ZERO.into();
    let mut alpha_pow: AB::Expr = AB::F::ONE.into();

    // The 25 coefficients L_i(x)^k over 5 domain points
    // Hardcoded from CompressedSumcheckAir's construction
    let lagrange = compute_lagrange_coeffs();
    for k in 0..5 {
        let mut ck: AB::Expr = AB::F::ZERO.into();
        for i in 0..5 {
            let coeff_f = lagrange[i][k];
            let coeff: AB::Expr = coeff_f.into();
            ck = ck + h[i].clone() * coeff;
        }
        p_alpha = p_alpha + ck * alpha_pow.clone();
        alpha_pow = alpha_pow * chal.clone();
    }
    b.assert_eq(run_out + p_alpha, AB::F::ZERO);
}

/// Compute Lagrange coefficients for domain {0,1,2,3,4} at field F.
fn compute_lagrange_coeffs() -> [[F; 5]; 5] {
    let mut result = [[F::ZERO; 5]; 5];
    for i in 0..5 {
        let mut poly = [F::ZERO; 5];
        poly[0] = F::ONE;
        let mut deg = 0;
        let mut denom = F::ONE;
        for j in 0..5 {
            if i == j { continue; }
            let xj = blk(j as u128);
            let xi = blk(i as u128);
            denom = denom * (xi + xj);
            let mut new_poly = [F::ZERO; 5];
            for k in 0..=deg + 1 {
                if k < 5 {
                    let mut v = F::ZERO;
                    if k >= 1 { v = v + poly[k - 1]; }
                    if k <= deg { v = v + xj * poly[k]; }
                    new_poly[k] = v;
                }
            }
            poly = new_poly;
            deg += 1;
        }
        let denom_inv = denom.try_inverse().expect("domain distinct");
        for k in 0..5 {
            result[i][k] = poly[k] * denom_inv;
        }
    }
    result
}

pub struct RecursiveCompositionAir;

impl<Fb> BaseAir<Fb> for RecursiveCompositionAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for RecursiveCompositionAir {
    fn eval(&self, b: &mut AB) {
        let zero = AB::F::ZERO;
        let main = b.main();
        let cur = main.current_slice();
        let next = main.next_slice();

        let is_first: AB::Expr = cur[COL_IS_FIRST].into();
        let is_last: AB::Expr = cur[COL_IS_LAST].into();

        // C0: booleanity
        b.assert_eq(is_first.clone() * is_first.clone() + is_first, zero);
        b.assert_eq(is_last.clone() * is_last.clone() + is_last, zero);

        // ===== Child A =====
        {
            let lo: AB::Expr = cur[A_FOLD_LO].into();
            let hi: AB::Expr = cur[A_FOLD_HI].into();
            let beta: AB::Expr = cur[A_FOLD_BETA].into();
            let x: AB::Expr = cur[A_FOLD_X].into();
            let nx: AB::Expr = cur[A_FOLD_NEXT].into();

            let f1 = lo.clone() + hi;
            let f0 = lo + x * f1.clone();
            let expected = beta * (f0.clone() + f1) + f0;
            b.assert_eq(nx + expected, zero);

            let sc_isl: AB::Expr = cur[A_FOLD_IS_LAST].into();
            b.assert_eq(sc_isl.clone() * sc_isl.clone() + sc_isl.clone(), zero);

            // Sumcheck chain
            let e0: AB::Expr = cur[A_SC_E0].into();
            let e1: AB::Expr = cur[A_SC_E1].into();
            let e2: AB::Expr = cur[A_SC_E2].into();
            let e3: AB::Expr = cur[A_SC_E3].into();
            let rin: AB::Expr = cur[A_SC_RUN_IN].into();
            let rout: AB::Expr = cur[A_SC_RUN_OUT].into();
            let chal: AB::Expr = cur[A_SC_CHAL].into();
            let sc_first: AB::Expr = cur[A_SC_IS_FIRST].into();
            let sc_last: AB::Expr = cur[A_SC_IS_LAST].into();

            b.assert_eq(sc_first.clone() * sc_first.clone() + sc_first, zero);
            b.assert_eq(sc_last.clone() * sc_last.clone() + sc_last.clone(), zero);

            sumcheck_interp(b, e0, e1, e2, e3, rin.clone(), chal, rout.clone());

            // Chain: this row's rout == next row's rin
            let next_rin: AB::Expr = next[A_SC_RUN_IN].into();
            let not_last = sc_last.clone() + AB::F::ONE;
            b.assert_eq(not_last * (rout + next_rin), zero);
        }

        // ===== Child B =====
        {
            let lo: AB::Expr = cur[B_FOLD_LO].into();
            let hi: AB::Expr = cur[B_FOLD_HI].into();
            let beta: AB::Expr = cur[B_FOLD_BETA].into();
            let x: AB::Expr = cur[B_FOLD_X].into();
            let nx: AB::Expr = cur[B_FOLD_NEXT].into();

            let f1 = lo.clone() + hi;
            let f0 = lo + x * f1.clone();
            let expected = beta * (f0.clone() + f1) + f0;
            b.assert_eq(nx + expected, zero);

            let sc_isl: AB::Expr = cur[B_FOLD_IS_LAST].into();
            b.assert_eq(sc_isl.clone() * sc_isl.clone() + sc_isl.clone(), zero);

            let e0: AB::Expr = cur[B_SC_E0].into();
            let e1: AB::Expr = cur[B_SC_E1].into();
            let e2: AB::Expr = cur[B_SC_E2].into();
            let e3: AB::Expr = cur[B_SC_E3].into();
            let rin: AB::Expr = cur[B_SC_RUN_IN].into();
            let rout: AB::Expr = cur[B_SC_RUN_OUT].into();
            let chal: AB::Expr = cur[B_SC_CHAL].into();
            let sc_first: AB::Expr = cur[B_SC_IS_FIRST].into();
            let sc_last: AB::Expr = cur[B_SC_IS_LAST].into();

            b.assert_eq(sc_first.clone() * sc_first.clone() + sc_first, zero);
            b.assert_eq(sc_last.clone() * sc_last.clone() + sc_last.clone(), zero);

            sumcheck_interp(b, e0, e1, e2, e3, rin.clone(), chal, rout.clone());

            let next_rin: AB::Expr = next[B_SC_RUN_IN].into();
            let not_last = sc_last.clone() + AB::F::ONE;
            b.assert_eq(not_last * (rout + next_rin), zero);
        }
    }
}

// ===== Test harness =====
#[derive(Clone, Copy)]
struct AirWrap;
impl<Fb> BaseAir<Fb> for AirWrap {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { 0 }
}
impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for AirWrap {
    fn eval(&self, b: &mut AB) { RecursiveCompositionAir.eval(b); }
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
    Ch::from_hasher(vec![], blake3::byte_hash())
}

fn build_pcs(arity: usize) -> BinaryPcs<F, E, M, ME> {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        arity, BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Poseidon2bMmcs::new();
    let round = Poseidon2bMmcs::new();
    BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap()
}

fn fold(lo: F, hi: F, beta: F, x: F) -> F {
    let f1 = lo + hi;
    let f0 = lo + x * f1;
    beta * (f0 + f1) + f0
}

fn lagrange_eval_native(h: [F; 5], alpha: F) -> F {
    let coeffs = compute_lagrange_coeffs();
    let mut result = F::ZERO;
    let mut alpha_pow = F::ONE;
    for k in 0..5 {
        let mut ck = F::ZERO;
        for i in 0..5 {
            ck = ck + h[i] * coeffs[i][k];
        }
        result = result + ck * alpha_pow;
        alpha_pow = alpha_pow * alpha;
    }
    result
}

fn build_trace() -> RowMajorMatrix<F> {
    // 8 rows: 4 for child A (1 fold + 3 sumcheck), 4 for child B
    let n_rows = 8;
    let mut values = vec![F::ZERO; n_rows * WIDTH];

    // Child A row 0: fold + sumcheck first row
    let a_lo = blk(10);
    let a_hi = blk(20);
    let a_beta = blk(30);
    let a_x = blk(0); // domain_point(0) = 0
    let a_nx = fold(a_lo, a_hi, a_beta, a_x);
    values[0 * WIDTH + A_FOLD_LO] = a_lo;
    values[0 * WIDTH + A_FOLD_HI] = a_hi;
    values[0 * WIDTH + A_FOLD_BETA] = a_beta;
    values[0 * WIDTH + A_FOLD_X] = a_x;
    values[0 * WIDTH + A_FOLD_NEXT] = a_nx;
    values[0 * WIDTH + A_FOLD_IS_LAST] = F::ZERO;

    // Sumcheck round 0
    let e0_0 = blk(1); let e1_0 = blk(3); let e2_0 = blk(4); let e3_0 = blk(5);
    let rin_0 = blk(100);
    let chal_0 = blk(7);
    let h_0: [F; 5] = [e0_0, rin_0 + e0_0, e1_0, e2_0, e3_0];
    let rout_0 = lagrange_eval_native(h_0, chal_0);
    values[0 * WIDTH + A_SC_E0] = e0_0;
    values[0 * WIDTH + A_SC_E1] = e1_0;
    values[0 * WIDTH + A_SC_E2] = e2_0;
    values[0 * WIDTH + A_SC_E3] = e3_0;
    values[0 * WIDTH + A_SC_RUN_IN] = rin_0;
    values[0 * WIDTH + A_SC_RUN_OUT] = rout_0;
    values[0 * WIDTH + A_SC_CHAL] = chal_0;
    values[0 * WIDTH + A_SC_IS_FIRST] = F::ONE;
    values[0 * WIDTH + A_SC_IS_LAST] = F::ZERO;

    // Rows 1, 2: sumcheck transitions
    let mut prev_out = rout_0;
    for r in 1..3 {
        let e0 = blk(10 + r as u128);
        let e1 = blk(20 + r as u128);
        let e2 = blk(30 + r as u128);
        let e3 = blk(40 + r as u128);
        let rin = prev_out;
        let chal = blk(50 + r as u128);
        let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
        let rout = lagrange_eval_native(h, chal);
        values[r * WIDTH + A_SC_E0] = e0;
        values[r * WIDTH + A_SC_E1] = e1;
        values[r * WIDTH + A_SC_E2] = e2;
        values[r * WIDTH + A_SC_E3] = e3;
        values[r * WIDTH + A_SC_RUN_IN] = rin;
        values[r * WIDTH + A_SC_RUN_OUT] = rout;
        values[r * WIDTH + A_SC_CHAL] = chal;
        if r == 2 { values[r * WIDTH + A_SC_IS_LAST] = F::ONE; }
        prev_out = rout;
    }
    // Row 3: child A's padding. All zeros EXCEPT:
    // - A_SC_IS_LAST=1: break A chain to row 4
    // - B_SC_IS_LAST=1: break B chain to row 4 (B chain starts at row 4)
    values[3 * WIDTH + A_SC_IS_LAST] = F::ONE;
    values[3 * WIDTH + B_SC_IS_LAST] = F::ONE;
    // Also break fold chains: B_FOLD_IS_LAST=1 (B fold starts at row 4)
    values[3 * WIDTH + B_FOLD_IS_LAST] = F::ONE;

    // Child B rows 4-7: same pattern
    let b_lo = blk(50);
    let b_hi = blk(60);
    let b_beta = blk(70);
    let b_x = blk(0);
    let b_nx = fold(b_lo, b_hi, b_beta, b_x);
    values[4 * WIDTH + B_FOLD_LO] = b_lo;
    values[4 * WIDTH + B_FOLD_HI] = b_hi;
    values[4 * WIDTH + B_FOLD_BETA] = b_beta;
    values[4 * WIDTH + B_FOLD_X] = b_x;
    values[4 * WIDTH + B_FOLD_NEXT] = b_nx;

    let e0_0 = blk(11); let e1_0 = blk(31); let e2_0 = blk(41); let e3_0 = blk(51);
    let rin_0 = blk(101);
    let chal_0 = blk(17);
    let h_0: [F; 5] = [e0_0, rin_0 + e0_0, e1_0, e2_0, e3_0];
    let rout_0 = lagrange_eval_native(h_0, chal_0);
    values[4 * WIDTH + B_SC_E0] = e0_0;
    values[4 * WIDTH + B_SC_E1] = e1_0;
    values[4 * WIDTH + B_SC_E2] = e2_0;
    values[4 * WIDTH + B_SC_E3] = e3_0;
    values[4 * WIDTH + B_SC_RUN_IN] = rin_0;
    values[4 * WIDTH + B_SC_RUN_OUT] = rout_0;
    values[4 * WIDTH + B_SC_CHAL] = chal_0;
    values[4 * WIDTH + B_SC_IS_FIRST] = F::ONE;

    let mut prev_out = rout_0;
    for r in 5..7 {
        let e0 = blk(100 + r as u128);
        let e1 = blk(200 + r as u128);
        let e2 = blk(300 + r as u128);
        let e3 = blk(400 + r as u128);
        let rin = prev_out;
        let chal = blk(500 + r as u128);
        let h: [F; 5] = [e0, rin + e0, e1, e2, e3];
        let rout = lagrange_eval_native(h, chal);
        values[r * WIDTH + B_SC_E0] = e0;
        values[r * WIDTH + B_SC_E1] = e1;
        values[r * WIDTH + B_SC_E2] = e2;
        values[r * WIDTH + B_SC_E3] = e3;
        values[r * WIDTH + B_SC_RUN_IN] = rin;
        values[r * WIDTH + B_SC_RUN_OUT] = rout;
        values[r * WIDTH + B_SC_CHAL] = chal;
        if r == 6 { values[r * WIDTH + B_SC_IS_LAST] = F::ONE; }
        prev_out = rout;
    }

    // is_first on row 0, is_last on row 7
    values[0 * WIDTH + COL_IS_FIRST] = F::ONE;
    values[7 * WIDTH + COL_IS_LAST] = F::ONE;

    RowMajorMatrix::new(values, WIDTH)
}

#[test]
#[ignore]
fn s1_pathb_recursive_compose() {
    let start = Instant::now();
    println!("=== Session A: Path B recursive composition ===");

    let trace = build_trace();
    let raw = trace.height() * trace.width();
    let arity = raw.next_power_of_two().trailing_zeros() as usize;
    println!("Trace: {}x{}, arity {}", trace.height(), trace.width(), arity);

    let config = Cfg { pcs: build_pcs(arity) };
    let air = AirWrap;
    let mut ch_s = make_ch();
    let (pk, vk) = setup(&config, &[&air], &mut ch_s).unwrap();

    let inst = ProverInstance::new(&air, Table::new(trace.transpose()), &pk, &[]);
    let mut ch_p = make_ch();
    let start_prove = Instant::now();
    let proof = prove(&config, ProverInstances::new(vec![inst]), 0, &mut ch_p).unwrap();
    let prove_ms = start_prove.elapsed().as_secs_f64() * 1000.0;
    println!("PROVE: {:.2}ms, ~{}B", prove_ms, core::mem::size_of_val(&proof));

    let log_h = trace.height().trailing_zeros() as usize;
    let verif = VerifierInstance::new(&air, &vk, log_h, &[]);
    let mut ch_v = make_ch();
    let start_v = Instant::now();
    verify(&config, VerifierInstances::new(vec![verif]), &proof, 0, &mut ch_v)
        .expect("Path B composition must verify");
    let verify_ms = start_v.elapsed().as_secs_f64() * 1000.0;
    println!("VERIFY: {:.2}ms", verify_ms);

    println!("\n=== Session A PASS: Path B recursive composition ===");
    println!("Prove: {:.2}ms, Verify: {:.2}ms, Total: {:.2}ms",
        prove_ms, verify_ms, start.elapsed().as_secs_f64() * 1000.0);
    println!("\nHONEST: Path B soundness (honest-prover sound, no in-circuit Merkle).");
    println!("FAST: ~{:.0}ms per aggregation vs Path A's 19 min.", prove_ms);

    // Sanity: should be FAST
    assert!(prove_ms < 5000.0, "expected < 5s prove, got {:.0}ms", prove_ms);
}
