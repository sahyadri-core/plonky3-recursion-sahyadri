//! FROST-GKR verifier AIR.
//!
//! Verifies the algebraic layer of a UnifiedProof:
//!   - boolean sum consistency for each sumcheck round
//!   - round-to-round folding via sampled rho challenges
//!   - final claim equality
//!   - degree bound on round polynomials
//!
//! rho challenges are PUBLIC inputs (extracted from the proof bytes
//! outside this circuit). A follow-up "extraction circuit" proves rho
//! was correctly derived via Poseidon2b Fiat-Shamir. This separation
//! keeps the algebraic circuit tractable while preserving soundness
//! composition when composed with the extraction circuit.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;
use p3_field::PrimeCharacteristicRing;

pub const MAX_ROUND_DEGREE: usize = 9;
pub const N_COEFS: usize = 16;
pub const N_ROUNDS: usize = 15;

pub const COL_RHO: usize = 0;
pub const COL_CLAIM: usize = COL_RHO + N_ROUNDS;
pub const COL_COEFS: usize = COL_CLAIM + (N_ROUNDS + 1);
pub const WIDTH_PADDED: usize = 512;

pub struct FrostGkrVerifierAir;

impl<F> BaseAir<F> for FrostGkrVerifierAir {
    fn width(&self) -> usize {
        WIDTH_PADDED
    }
    fn num_public_values(&self) -> usize {
        N_ROUNDS + 1
    }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for FrostGkrVerifierAir {
    fn eval(&self, b: &mut AB) {
        let cur: alloc::vec::Vec<AB::Expr> = {
            let main = b.main();
            main.current_slice().iter().map(|v| (*v).into()).collect()
        };
        let public: alloc::vec::Vec<AB::Expr> =
            b.public_values().iter().map(|v| (*v).into()).collect();

        let one: AB::Expr = AB::F::ONE.into();
        let two: AB::Expr = AB::F::TWO.into();

        let rho = |i: usize| -> AB::Expr { cur[COL_RHO + i].clone() };
        let claim = |i: usize| -> AB::Expr { cur[COL_CLAIM + i].clone() };
        let coef = |i: usize, j: usize| -> AB::Expr {
            cur[COL_COEFS + i * N_COEFS + j].clone()
        };

        // Constraint: rho[i] equals public rho[i]
        for i in 0..N_ROUNDS {
            b.assert_eq(rho(i), public[i].clone());
        }

        // Constraint: final claim equals public expected claim
        b.assert_eq(claim(N_ROUNDS), public[N_ROUNDS].clone());

        // Constraint: boolean sum consistency per round
        // claim[i] = P_i(0) + P_i(1) = 2*P_i[0] + sum_{j>=1} P_i[j]
        for i in 0..N_ROUNDS {
            let mut boolean_sum: AB::Expr = two.clone() * coef(i, 0);
            for j in 1..=MAX_ROUND_DEGREE {
                boolean_sum = boolean_sum + coef(i, j);
            }
            b.assert_eq(claim(i), boolean_sum);
        }

        // Constraint: round eval  claim[i+1] = P_i(rho[i])
        // Horner: start with top coefficient, fold down
        for i in 0..N_ROUNDS {
            let mut eval: AB::Expr = coef(i, MAX_ROUND_DEGREE);
            for j in (0..MAX_ROUND_DEGREE).rev() {
                eval = eval * rho(i) + coef(i, j);
            }
            b.assert_eq(claim(i + 1), eval);
        }

        // Constraint: degree bound  coef[i][j] = 0 for j in 10..16
        for i in 0..N_ROUNDS {
            for j in (MAX_ROUND_DEGREE + 1)..N_COEFS {
                b.assert_zero(coef(i, j));
            }
        }

        // Silence unused var warning for `one` (kept for future use)
        let _ = one;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::{check_constraints, BaseAir};
    use p3_matrix::dense::RowMajorMatrix;

    fn fe(v: u128) -> BinaryField128 {
        BinaryField128::from_le_bytes(v.to_le_bytes())
    }

    fn build_constant_poly_trace() -> (RowMajorMatrix<BinaryField128>, alloc::vec::Vec<BinaryField128>) {
        // Trivial valid proof: round poly = 2 (constant).
        // P(0)+P(1) = 2+2 = 4, so claim_i = 4 for all i.
        // P(rho) = 2 for all rho, so claim_{i+1} = 2.
        // Contradiction — need P such that P(0)+P(1)=claim_i and P(rho_i)=claim_{i+1}.
        //
        // Simpler: use P(X) = claim (constant). Then P(0)+P(1) = 2*claim.
        // Round consistency: claim_i = 2*claim_i, so claim_i = 0.
        // Final claim = 0. Valid trivial proof.
        let mut values = alloc::vec![fe(0); WIDTH_PADDED];
        let mut public = alloc::vec![fe(0); N_ROUNDS + 1];
        // rho[i] = 0 for all i
        for i in 0..N_ROUNDS {
            values[COL_RHO + i] = fe(0);
            public[i] = fe(0);
        }
        // claim[i] = 0
        for i in 0..=N_ROUNDS {
            values[COL_CLAIM + i] = fe(0);
        }
        // coefs all 0
        public[N_ROUNDS] = fe(0);

        (RowMajorMatrix::new(values, WIDTH_PADDED), public)
    }

    #[test]
    fn trivial_proof_satisfies() {
        let air = FrostGkrVerifierAir;
        let (trace, public) = build_constant_poly_trace();
        check_constraints(&air, &trace, &public);
    }

    #[test]
    fn width_matches() {
        assert_eq!(<FrostGkrVerifierAir as BaseAir<BinaryField128>>::width(&FrostGkrVerifierAir), WIDTH_PADDED);
    }

    #[test]
    fn public_inputs_match() {
        assert_eq!(
            <FrostGkrVerifierAir as BaseAir<BinaryField128>>::num_public_values(&FrostGkrVerifierAir),
            N_ROUNDS + 1
        );
    }
}
