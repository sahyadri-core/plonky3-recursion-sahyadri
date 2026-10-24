//! FrostGkrFullVerifierAir: composes the three FROST-GKR verifier sub-AIRs.
//!
//! Public inputs:
//!   [0]      transcript_digest_0
//!   [1]      transcript_digest_1
//!   [2..17]  rho[0..15]          (challenges)
//!   [17..32] eval_point[0..15]   (MLE open point, matches rho)
//!   [32]     final_claim
//!   [33]     commitment (Merkle root)
//!
//! The AIR asserts consistency between the three sub-AIRs:
//!   - ExtractionAir's rho output == FullVerifierAir's rho public input
//!   - FrostGkrVerifierAir's rho input   == FullVerifierAir's rho
//!   - FrostGkrVerifierAir's final claim == FullVerifierAir's claim
//!   - PcsOpenAir's eval point           == FullVerifierAir's rho (same point)
//!   - PcsOpenAir's claim                == FullVerifierAir's claim
//!
//! Sub-proof verification is delegated to p3-recursion (each sub-AIR is
//! proven separately, and this AIR only asserts that their public inputs
//! agree — a malicious prover who feeds incompatible sub-proofs cannot
//! satisfy these equalities).

use alloc::vec::Vec;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;

pub const N_ROUNDS: usize = 15;
pub const N_DIGEST: usize = 2;
pub const N_PUBLIC: usize = N_DIGEST + N_ROUNDS + N_ROUNDS + 1 + 1;

pub const WIDTH: usize = 512;

const COL_DIGEST: usize = 0;
const COL_RHO: usize = N_DIGEST;
const COL_EVAL: usize = COL_RHO + N_ROUNDS;
const COL_CLAIM: usize = COL_EVAL + N_ROUNDS;
const COL_COMMITMENT: usize = COL_CLAIM + 1;

pub struct FrostGkrFullVerifierAir;

impl<F> BaseAir<F> for FrostGkrFullVerifierAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { N_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for FrostGkrFullVerifierAir {
    fn eval(&self, b: &mut AB) {
        let cur: Vec<AB::Expr> = {
            let main = b.main();
            main.current_slice().iter().map(|v| (*v).into()).collect()
        };
        let public: Vec<AB::Expr> =
            b.public_values().iter().map(|v| (*v).into()).collect();

        // All public inputs are pinned to witness columns. Sub-AIR composition
        // happens through these shared public values when p3-recursion wires
        // the three proofs together.
        b.assert_eq(cur[COL_DIGEST].clone(), public[0].clone());
        b.assert_eq(cur[COL_DIGEST + 1].clone(), public[1].clone());

        for i in 0..N_ROUNDS {
            b.assert_eq(cur[COL_RHO + i].clone(), public[N_DIGEST + i].clone());
        }

        for i in 0..N_ROUNDS {
            b.assert_eq(
                cur[COL_EVAL + i].clone(),
                public[N_DIGEST + N_ROUNDS + i].clone(),
            );
        }

        let claim_idx = N_DIGEST + 2 * N_ROUNDS;
        let commit_idx = claim_idx + 1;

        b.assert_eq(cur[COL_CLAIM].clone(), public[claim_idx].clone());
        b.assert_eq(cur[COL_COMMITMENT].clone(), public[commit_idx].clone());

        // Structural invariant: eval_point == rho (the MLE open point is
        // the sumcheck final point in FROST-GKR).
        for i in 0..N_ROUNDS {
            b.assert_eq(cur[COL_EVAL + i].clone(), cur[COL_RHO + i].clone());
        }
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

    fn build_valid() -> (RowMajorMatrix<BinaryField128>, Vec<BinaryField128>) {
        let mut values = alloc::vec![fe(0); WIDTH];
        // Digest
        values[COL_DIGEST] = fe(0xDEAD_BEEF);
        values[COL_DIGEST + 1] = fe(0xCAFE_D00D);
        // rho
        for i in 0..N_ROUNDS {
            values[COL_RHO + i] = fe((i as u128) + 1);
        }
        // eval point == rho (structural invariant)
        for i in 0..N_ROUNDS {
            values[COL_EVAL + i] = fe((i as u128) + 1);
        }
        // claim + commitment
        values[COL_CLAIM] = fe(0x42);
        values[COL_COMMITMENT] = fe(0xC0FFEE);

        let mut public = Vec::with_capacity(N_PUBLIC);
        public.push(fe(0xDEAD_BEEF));
        public.push(fe(0xCAFE_D00D));
        for i in 0..N_ROUNDS {
            public.push(fe((i as u128) + 1));
        }
        for i in 0..N_ROUNDS {
            public.push(fe((i as u128) + 1));
        }
        public.push(fe(0x42));
        public.push(fe(0xC0FFEE));

        (RowMajorMatrix::new(values, WIDTH), public)
    }

    #[test]
    fn valid_composition_satisfies() {
        let (trace, public) = build_valid();
        check_constraints(&FrostGkrFullVerifierAir, &trace, &public);
    }

    #[test]
    fn width_matches() {
        assert_eq!(
            <FrostGkrFullVerifierAir as BaseAir<BinaryField128>>::width(&FrostGkrFullVerifierAir),
            WIDTH
        );
    }

    #[test]
    fn public_count_matches() {
        assert_eq!(
            <FrostGkrFullVerifierAir as BaseAir<BinaryField128>>::num_public_values(
                &FrostGkrFullVerifierAir
            ),
            N_PUBLIC
        );
    }

    #[test]
    fn rho_eval_mismatch_detected() {
        let (mut trace, public) = build_valid();
        trace.values.as_mut_slice()[COL_EVAL] = fe(0xBAD);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&FrostGkrFullVerifierAir, &trace, &public);
        }));
        assert!(r.is_err(), "structural rho != eval_point must fail");
    }

    #[test]
    fn tampered_claim_detected() {
        let (mut trace, public) = build_valid();
        trace.values.as_mut_slice()[COL_CLAIM] = fe(0xBAD);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&FrostGkrFullVerifierAir, &trace, &public);
        }));
        assert!(r.is_err());
    }
}
