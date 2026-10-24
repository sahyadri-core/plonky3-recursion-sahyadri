//! ExtractionAir: verifies FROST-GKR challenge derivation from public digest.
//!
//! Public: transcript_digest (2 Block128s = 32 bytes), rho[0..15]
//! Witness: sponge state after each Poseidon2b permutation
//!
//! Constraints (this AIR):
//!   - rho[i] pattern matches pending-cache squeeze semantics
//!   - public rho matches witness rho
//!
//! Delegated (Poseidon2bAir sub-proof, composed via p3-recursion):
//!   - sponge state transitions are correct Poseidon2b permutations

use alloc::vec::Vec;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;

pub const N_SQUEEZES: usize = 8;
pub const N_RHO: usize = 15;
pub const STATE_SIZE: usize = 4;
pub const WIDTH: usize = 512;
pub const N_PUBLIC: usize = 2 + N_RHO;

const COL_DIGEST: usize = 0;
const COL_PERM_STATES: usize = 2;
const COL_RHO: usize = COL_PERM_STATES + N_SQUEEZES * STATE_SIZE;

pub struct ExtractionAir;

impl<F> BaseAir<F> for ExtractionAir {
    fn width(&self) -> usize { WIDTH }
    fn num_public_values(&self) -> usize { N_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for ExtractionAir {
    fn eval(&self, b: &mut AB) {
        let cur: Vec<AB::Expr> = {
            let main = b.main();
            main.current_slice().iter().map(|v| (*v).into()).collect()
        };
        let public: Vec<AB::Expr> =
            b.public_values().iter().map(|v| (*v).into()).collect();

        let digest = |i: usize| -> AB::Expr { cur[COL_DIGEST + i].clone() };
        let perm = |sqz: usize, lane: usize| -> AB::Expr {
            cur[COL_PERM_STATES + sqz * STATE_SIZE + lane].clone()
        };
        let rho = |i: usize| -> AB::Expr { cur[COL_RHO + i].clone() };

        // Public: digest
        for i in 0..2 {
            b.assert_eq(digest(i), public[i].clone());
        }
        // Public: rho
        for i in 0..N_RHO {
            b.assert_eq(rho(i), public[2 + i].clone());
        }

        // Squeeze pattern (pending-cache semantics from Poseidon2bChannel):
        //   squeeze 1: rho[0] = perm_0[0], pending = perm_0[1]
        //   squeeze 2: return pending = perm_0[1]  -> rho[1] = perm_0[1]
        //   squeeze 3: rho[2] = perm_1[0], pending = perm_1[1]
        //   squeeze 4: rho[3] = perm_1[1]
        //   ...
        //   squeeze 15: rho[14] = perm_7[0]  (only first element used)
        for i in 0..(N_SQUEEZES - 1) {
            b.assert_eq(rho(2 * i), perm(i, 0));
            b.assert_eq(rho(2 * i + 1), perm(i, 1));
        }
        // Last squeeze (i = 7): only first element
        b.assert_eq(rho(14), perm(N_SQUEEZES - 1, 0));
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

    fn build_trace() -> (RowMajorMatrix<BinaryField128>, Vec<BinaryField128>) {
        let mut values = alloc::vec![fe(0); WIDTH];
        // digest
        values[COL_DIGEST] = fe(0xDEAD);
        values[COL_DIGEST + 1] = fe(0xBEEF);
        // perm states: fill with deterministic pattern
        for sqz in 0..N_SQUEEZES {
            for lane in 0..STATE_SIZE {
                values[COL_PERM_STATES + sqz * STATE_SIZE + lane] =
                    fe((sqz as u128 + 1) * 100 + (lane as u128 + 1));
            }
        }
        // rho derived from perm states per pending pattern
        for i in 0..(N_SQUEEZES - 1) {
            values[COL_RHO + 2 * i] = values[COL_PERM_STATES + i * STATE_SIZE];
            values[COL_RHO + 2 * i + 1] = values[COL_PERM_STATES + i * STATE_SIZE + 1];
        }
        values[COL_RHO + 14] = values[COL_PERM_STATES + (N_SQUEEZES - 1) * STATE_SIZE];

        // public: digest || rho[0..15]
        let mut public = Vec::new();
        public.push(fe(0xDEAD));
        public.push(fe(0xBEEF));
        for i in 0..N_RHO {
            public.push(values[COL_RHO + i]);
        }
        (RowMajorMatrix::new(values, WIDTH), public)
    }

    #[test]
    fn valid_trace_satisfies() {
        let (trace, public) = build_trace();
        check_constraints(&ExtractionAir, &trace, &public);
    }

    #[test]
    fn width_matches() {
        assert_eq!(
            <ExtractionAir as BaseAir<BinaryField128>>::width(&ExtractionAir),
            WIDTH
        );
    }

    #[test]
    fn public_count_matches() {
        assert_eq!(
            <ExtractionAir as BaseAir<BinaryField128>>::num_public_values(&ExtractionAir),
            N_PUBLIC
        );
    }

    #[test]
    fn tampered_rho_detected() {
        let (mut trace, public) = build_trace();
        // Tamper rho[0]
        let values_mut = trace.values.as_mut_slice();
        values_mut[COL_RHO] = fe(0xFFFF_FFFF);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&ExtractionAir, &trace, &public);
        }));
        assert!(result.is_err(), "tampered rho must fail constraint check");
    }
}
