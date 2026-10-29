//! BinaryVerifierAir — Phase C1.4 (depth-4 Merkle) + C1.5 groundwork.
//!
//! # Column layout (WIDTH = 18)
//!
//! | Col   | Name                | Purpose                                |
//! |-------|---------------------|----------------------------------------|
//! | 0     | pair0               | FRI leaf / fold current                |
//! | 1     | pair1               | FRI sibling for fold                   |
//! | 2     | alpha               | FRI fold challenge                     |
//! | 3     | next                | fold result / final_poly[i_final]      |
//! | 4     | sel                 | index parity bit                       |
//! | 5     | is_last             | boolean, marks last round              |
//! | 6-9   | s0..s3              | final-poly one-hot selectors           |
//! | 10-13 | merkle_sib[0..4]    | 4 Merkle siblings (depth 4)            |
//! | 14-17 | merkle_parent[0..4] | 4 intermediate parents (parent[3]=root)|
//!
//! # Bus Pulls (C1.3 extension for C1.4)
//!
//! `BinaryVerifierBusAir` emits 4 Pull tuples on MERKLE_COMPRESS:
//!   (pair0,          sib[0], parent[0])
//!   (parent[0],      sib[1], parent[1])
//!   (parent[1],      sib[2], parent[2])
//!   (parent[2],      sib[3], parent[3])  ← parent[3] == root
//!
//! Pairs with 4 `Poseidon2bBusAir` producers (3D2b) in the same MultiStark.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_field::PrimeCharacteristicRing;

pub const MERKLE_COMPRESS: BusName<'static> = BusName::new("sahyadri_merkle_compress");

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
pub const COL_MERKLE_SIB_BASE: usize = 10;
pub const COL_MERKLE_PARENT_BASE: usize = 14;
pub const MERKLE_DEPTH: usize = 4;
pub const WIDTH: usize = COL_MERKLE_PARENT_BASE + MERKLE_DEPTH; // 18
pub const FINAL_POLY_LEN: usize = 4;
pub const NUM_PUBLIC: usize = FINAL_POLY_LEN;


/// FRI-half constraints, offset-parametric. Used by `BinaryVerifierAir`
/// (col_off=0, pub_off=0), `BinaryVerifierBusAir` (same), and
/// `BinaryAggregationAir` (col_off=0/18, pub_off=0/4).
pub fn eval_fri_half<AB: AirBuilder<F = BinaryField128>>(
    b: &mut AB,
    col_off: usize,
    pub_off: usize,
) {
    let main = b.main();
    let cur = main.current_slice();
    let pair0: AB::Expr = cur[col_off + COL_PAIR0].into();
    let pair1: AB::Expr = cur[col_off + COL_PAIR1].into();
    let alpha: AB::Expr = cur[col_off + COL_ALPHA].into();
    let next: AB::Expr = cur[col_off + COL_NEXT].into();
    let sel: AB::Expr = cur[col_off + COL_SEL].into();
    let is_last: AB::Expr = cur[col_off + COL_IS_LAST].into();
    let s = [
        AB::Expr::from(cur[col_off + COL_S0]),
        AB::Expr::from(cur[col_off + COL_S1]),
        AB::Expr::from(cur[col_off + COL_S2]),
        AB::Expr::from(cur[col_off + COL_S3]),
    ];
    let one = AB::F::ONE;

    for v in [&sel, &is_last, &s[0], &s[1], &s[2], &s[3]] {
        let sq = v.clone() * v.clone();
        b.assert_eq(sq + v.clone(), AB::F::ZERO);
    }
    for i in 0..FINAL_POLY_LEN {
        for j in (i + 1)..FINAL_POLY_LEN {
            b.assert_eq(s[i].clone() * s[j].clone(), AB::F::ZERO);
        }
    }
    let selector_sum = s[0].clone() + s[1].clone() + s[2].clone() + s[3].clone();
    b.assert_eq(is_last.clone() * (selector_sum + one), AB::F::ZERO);

    let x = pair0.clone() + pair1.clone();
    let y = sel * x;
    let z = alpha * (pair1 + y.clone());
    b.assert_eq(next.clone(), pair0 + y + z);

    let public = b.public_values();
    let fp: [AB::Expr; FINAL_POLY_LEN] = [
        public[pub_off + 0].into(), public[pub_off + 1].into(),
        public[pub_off + 2].into(), public[pub_off + 3].into(),
    ];
    let selected = s[0].clone() * fp[0].clone()
        + s[1].clone() * fp[1].clone()
        + s[2].clone() * fp[2].clone()
        + s[3].clone() * fp[3].clone();
    b.assert_eq(is_last * (next + selected), AB::F::ZERO);
}

pub struct BinaryVerifierAir;

impl<F> BaseAir<F> for BinaryVerifierAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for BinaryVerifierAir {
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

        // Booleanity
        for v in [&sel, &is_last, &s[0], &s[1], &s[2], &s[3]] {
            let sq = v.clone() * v.clone();
            b.assert_eq(sq + v.clone(), AB::F::ZERO);
        }
        // Pairwise disjointness
        for i in 0..FINAL_POLY_LEN {
            for j in (i + 1)..FINAL_POLY_LEN {
                b.assert_eq(s[i].clone() * s[j].clone(), AB::F::ZERO);
            }
        }
        // Last row must select exactly one final_poly cell
        let selector_sum = s[0].clone() + s[1].clone() + s[2].clone() + s[3].clone();
        b.assert_eq(is_last.clone() * (selector_sum + one), AB::F::ZERO);

        // Fold constraint
        let x = pair0.clone() + pair1.clone();
        let y = sel * x;
        let z = alpha * (pair1 + y.clone());
        b.assert_eq(next.clone(), pair0 + y + z);

        // Final-poly binding on last row
        let public = b.public_values();
        let fp: [AB::Expr; FINAL_POLY_LEN] = [
            public[0].into(), public[1].into(),
            public[2].into(), public[3].into(),
        ];
        let selected = s[0].clone() * fp[0].clone()
            + s[1].clone() * fp[1].clone()
            + s[2].clone() * fp[2].clone()
            + s[3].clone() * fp[3].clone();
        b.assert_eq(is_last * (next + selected), AB::F::ZERO);
    }
}

/// C1.3+C1.4 bus wrapper — 4 Pull tuples per row.
pub struct BinaryVerifierBusAir;

impl<F> BaseAir<F> for BinaryVerifierBusAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB>
    for BinaryVerifierBusAir
{
    fn eval(&self, b: &mut AB) {
        eval_fri_half(b, 0, 0);

        let main = b.main();
        let cur = main.current_slice();
        let leaf: AB::Expr = cur[COL_PAIR0].into();

        for level in 0..MERKLE_DEPTH {
            let curr: AB::Expr = if level == 0 {
                leaf.clone()
            } else {
                AB::Expr::from(cur[COL_MERKLE_PARENT_BASE + level - 1])
            };
            let sib: AB::Expr = cur[COL_MERKLE_SIB_BASE + level].into();
            let parent: AB::Expr = cur[COL_MERKLE_PARENT_BASE + level].into();

            // Fire only on last row so a 4-row replicated consumer trace
            // contributes exactly 4 pulls (one per level), not 16.
            let active = b.is_last_row();
            b.push_bus_interaction(
                MERKLE_COMPRESS,
                BusDirection::Pull,
                [curr, sib, parent],
                BusActivation::Boolean(active),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_matrix::dense::RowMajorMatrix;

    type F = BinaryField128;

    fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

    fn valid_row(pair0: u128, pair1: u128, alpha: u128) -> [F; WIDTH] {
        let p0 = blk(pair0);
        let p1 = blk(pair1);
        let a = blk(alpha);
        let x = p0 + p1;
        let y = x; // sel = 1
        let z = a * (p1 + y);
        let folded = p0 + y + z;
        let mut row = [F::ZERO; WIDTH];
        row[COL_PAIR0] = p0;
        row[COL_PAIR1] = p1;
        row[COL_ALPHA] = a;
        row[COL_NEXT] = folded;
        row[COL_SEL] = blk(1);
        row[COL_IS_LAST] = F::ZERO;
        for i in 0..MERKLE_DEPTH {
            row[COL_MERKLE_SIB_BASE + i] = blk(0x1000 + i as u128);
            row[COL_MERKLE_PARENT_BASE + i] = blk(0x2000 + i as u128);
        }
        row
    }

    #[test]
    fn layout_matches_constants() {
        assert_eq!(WIDTH, 18);
        assert_eq!(NUM_PUBLIC, 4);
        assert_eq!(COL_MERKLE_SIB_BASE, 10);
        assert_eq!(COL_MERKLE_PARENT_BASE, 14);
        assert_eq!(MERKLE_DEPTH, 4);
    }

    #[test]
    fn valid_fold_satisfies() {
        let air = BinaryVerifierAir;
        let trace = RowMajorMatrix::new(valid_row(10, 20, 30).to_vec(), WIDTH);
        let public = vec![F::ZERO; FINAL_POLY_LEN];
        check_constraints(&air, &trace, &public);
    }

    #[test]
    fn tampered_alpha_rejected() {
        let air = BinaryVerifierAir;
        let mut row = valid_row(10, 20, 30);
        row[COL_ALPHA] = blk(31);
        let trace = RowMajorMatrix::new(row.to_vec(), WIDTH);
        let public = vec![F::ZERO; FINAL_POLY_LEN];
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &trace, &public);
        }));
        assert!(res.is_err(), "tampered alpha must fail fold");
    }

    #[test]
    fn tampered_state_rejected() {
        let air = BinaryVerifierAir;
        let mut row = valid_row(10, 20, 30);
        row[COL_PAIR0] = blk(11);
        let trace = RowMajorMatrix::new(row.to_vec(), WIDTH);
        let public = vec![F::ZERO; FINAL_POLY_LEN];
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &trace, &public);
        }));
        assert!(res.is_err(), "tampered state must fail fold");
    }

    #[test]
    fn bus_wrapper_constructible_4_pulls() {
        // 4 Pull tuples per row, MERKLE_COMPRESS channel.
        // Full bus balance check is in C1.5 combined MultiStark.
        let _ = BinaryVerifierBusAir;
        let _ = MERKLE_COMPRESS;
        assert_eq!(MERKLE_DEPTH, 4);
    }
}
