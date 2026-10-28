//! BinaryVerifierAir — Phase C1.2 (fold) + C1.3 (Merkle bus Pull).
//!
//! # Column layout (per query-round row, 12 cols)
//!
//! | Col | Name          | Purpose                                    |
//! |-----|---------------|--------------------------------------------|
//! | 0   | pair0         | codeword eval at index i_0 (Merkle leaf)   |
//! | 1   | pair1         | sibling eval (FRI pair)                    |
//! | 2   | alpha         | FRI fold challenge                         |
//! | 3   | next          | fold result or final_poly[i_final]         |
//! | 4   | sel           | index parity bit (0/1)                     |
//! | 5   | is_last       | boolean, marks last round                  |
//! | 6-9 | s0..s3        | final-poly one-hot selectors (last row)    |
//! | 10  | merkle_sib    | 1 Merkle sibling (leaf-parent level)       |
//! | 11  | merkle_parent | expected parent hash                       |
//!
//! # C1.2 constraints (always on)
//!
//! - Booleanity: sel, is_last, s0..s3 ∈ {0,1}
//! - Pairwise disjointness on s0..s3
//! - Last row: exactly one selector active
//! - Fold: next == pair0 + sel·(p0+p1) + α·(p1 + sel·(p0+p1))
//! - Last row: next == Σ sᵢ · final_poly[i]
//!
//! # C1.3 (bus wrapper only)
//!
//! `BinaryVerifierBusAir` adds Bus Pull `(pair0, merkle_sib, merkle_parent)`
//! on `MERKLE_COMPRESS`. Consumer pairs with `Poseidon2bBusAir` producer
//! (3D2b). Bus balance is enforced at MultiStark prove time (see 3D2d).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};

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
pub const COL_MERKLE_SIB: usize = 10;
pub const COL_MERKLE_PARENT: usize = 11;
pub const WIDTH: usize = 12;
pub const FINAL_POLY_LEN: usize = 4;
pub const NUM_PUBLIC: usize = FINAL_POLY_LEN;

pub struct BinaryVerifierAir;

impl<F> BaseAir<F> for BinaryVerifierAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

/// C1.2 constraints only (no bus). Standalone, testable via check_constraints.
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

/// C1.3 — wraps `BinaryVerifierAir` with bus Pull on MERKLE_COMPRESS.
///
/// Consumer side of the (pair0, sib, parent) tuple; producer is
/// `Poseidon2bBusAir` (3D2b). Pairs with `Poseidon2bBusAir` in the same
/// MultiStark — full bus balance check happens at prove time (3D2d pattern).
pub struct BinaryVerifierBusAir;

impl<F> BaseAir<F> for BinaryVerifierBusAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { NUM_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder> Air<AB>
    for BinaryVerifierBusAir
{
    fn eval(&self, b: &mut AB) {
        BinaryVerifierAir.eval(b);

        let main = b.main();
        let cur = main.current_slice();
        let pair0: AB::Expr = cur[COL_PAIR0].into();
        let sib: AB::Expr = cur[COL_MERKLE_SIB].into();
        let parent: AB::Expr = cur[COL_MERKLE_PARENT].into();

        b.push_bus_interaction(
            MERKLE_COMPRESS,
            BusDirection::Pull,
            [pair0, sib, parent],
            BusActivation::Always,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;

    type F = BinaryField128;

    fn blk(n: u128) -> F { F::from_le_bytes(n.to_le_bytes()) }

    fn valid_row(pair0: u128, pair1: u128, alpha: u128) -> [F; WIDTH] {
        let p0 = blk(pair0);
        let p1 = blk(pair1);
        let a = blk(alpha);
        let x = p0 + p1;
        let y = x;  // sel = 1
        let z = a * (p1 + y);
        let folded = p0 + y + z;
        let mut row = [F::ZERO; WIDTH];
        row[COL_PAIR0] = p0;
        row[COL_PAIR1] = p1;
        row[COL_ALPHA] = a;
        row[COL_NEXT] = folded;
        row[COL_SEL] = blk(1);
        row[COL_IS_LAST] = F::ZERO;
        row[COL_MERKLE_SIB] = blk(0xdead);
        row[COL_MERKLE_PARENT] = blk(0xbeef);
        row
    }

    #[test]
    fn layout_matches_constants() {
        assert_eq!(WIDTH, 12);
        assert_eq!(NUM_PUBLIC, 4);
        assert_eq!(COL_MERKLE_SIB, 10);
        assert_eq!(COL_MERKLE_PARENT, 11);
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
        row[COL_ALPHA] = blk(31); // next unchanged → fold fails
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
        row[COL_PAIR0] = blk(11); // next now stale
        let trace = RowMajorMatrix::new(row.to_vec(), WIDTH);
        let public = vec![F::ZERO; FINAL_POLY_LEN];
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &trace, &public);
        }));
        assert!(res.is_err(), "tampered state must fail fold");
    }

    #[test]
    fn bus_wrapper_constructible() {
        // C1.3: BinaryVerifierBusAir implements Air + BusInteractionBuilder.
        // Full bus balance check is deferred to C1.5 integration (needs
        // combined MultiStark with Poseidon2bBusAir producer, like 3D2d).
        let _ = BinaryVerifierBusAir;
        let _ = MERKLE_COMPRESS;
    }
}
