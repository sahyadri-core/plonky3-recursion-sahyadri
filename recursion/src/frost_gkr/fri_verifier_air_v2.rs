//! FriVerifierAirV2 — Phase 3E (BF128 concrete).
//!
//! Identical constraints to `sahyadri-fri-binius::FriVerifierAirV2` but
//! pinned to `BinaryField128` so the fork's MultiStark pipeline can consume
//! it directly. Discovery (2026-10-25): Plonky3 accepts Val == Challenge,
//! so no extension field is needed for 3E.
//!
//! Row layout (one row per query-round):
//!   pair0, pair1, alpha, next, sel, is_last, s0, s1, s2, s3
//!
//! Public inputs: final_poly[0..4].
//!
//! Constraints:
//!   1. sel, is_last, s0..s3 ∈ {0,1}
//!   2. pairwise disjointness on s0..s3
//!   3. is_last → s0 + s1 + s2 + s3 = 1
//!   4. next == fold(pair0, pair1, alpha, sel)
//!   5. is_last → next == Σ s_i * final_poly_i

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

pub const COL_PAIR0: usize = 0;
pub const COL_PAIR1: usize = 1;
pub const COL_ALPHA: usize = 2;
pub const COL_NEXT: usize = 3;
pub const COL_SEL: usize = 4;
pub const COL_IS_LAST: usize = 5;
pub const COL_S0: usize = 6;
pub const COL_S1: usize = 7;
pub const COL_S2: usize = 8;
pub const COL_S3: usize = 9;
pub const WIDTH: usize = 10;
pub const FINAL_POLY_LEN: usize = 4;
pub const NUM_PUBLIC: usize = FINAL_POLY_LEN;

pub struct FriVerifierAirV2;

impl<F> BaseAir<F> for FriVerifierAirV2 {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for FriVerifierAirV2 {
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
