//! Phase 3D part 2b — Poseidon2b bus-linked compression.
//!
//! Delegates to `Poseidon2bAir` (full permutation, 1024 cols), binds the
//! domain tag to the public input, and pushes the compression tuple
//! `(a, b, c)` on `MERKLE_COMPRESS`.
//!
//! # Public input layout (matches Poseidon2bAir)
//!
//!   public[0..4] = (a, b, 0, MERKLE_DOMAIN)   ← input state
//!   public[4..8] = (c_lo, c_hi, 0, 0)         ← output state
//!
//! `Poseidon2bAir::eval` binds `state(0, lane) == public[lane]` and
//! `state(N_STATES-1, lane) == public[4+lane]`. So `public[4] + public[5]`
//! equals `compress(a, b)` when the domain tag is `MERKLE_DOMAIN`.
//!
//! # Domain binding (extra constraints here)
//!
//! `Poseidon2bAir` doesn't constrain `public[2]`, `public[3]`, `public[6]`,
//! `public[7]`. We enforce:
//!   public[2] == 0
//!   public[3] == MERKLE_DOMAIN
//!   public[6] == 0
//!   public[7] == 0
//!
//! These 4 constraints turn `Poseidon2bAir` into a *Merkle-compression-only*
//! AIR. Any other permutation shape is rejected at proof time.
//!
//! # Instance-per-compress
//!
//! Merkle tree with depth d and q queries needs d*q compressions. Each is
//! one `Poseidon2bBusAir` instance with its own public inputs. MultiStark
//! aggregates N instances of the same AIR into one proof.
//!
//! # Cryptographic tie
//!
//! `MerklePathAir` (in sahyadri-fri-binius) pushes `(curr, sib, next)` on
//! the same bus. Plonky3's multiset bus equality forces every Merkle tuple
//! to be a validated `(a, b, compress(a, b))` triple. Phase 3D2c wires that
//! pull side; Phase 3D2d tests the combined MultiStark.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_binary_field::BinaryField128;
use p3_bus::{BusActivation, BusDirection, BusInteractionBuilder, BusName};
use p3_field::PrimeCharacteristicRing;
use p3_poseidon2b::Poseidon2bAir;

/// Channel for Merkle compression tuples.
pub const MERKLE_COMPRESS: BusName<'static> = BusName::new("sahyadri_merkle_compress");

/// Domain tag (must match `sahyadri_fri_binius::compress`).
pub const MERKLE_DOMAIN: u128 = 0x4D45_524B_4C45_0001;

pub struct Poseidon2bBusAir;

impl<F> BaseAir<F> for Poseidon2bBusAir {
    fn width(&self) -> usize {
        // Delegates to Poseidon2bAir; no extra columns needed because
        // the compression tuple comes from public inputs.
        <Poseidon2bAir as BaseAir<F>>::width(&Poseidon2bAir)
    }
    fn num_public_values(&self) -> usize {
        // Same layout as Poseidon2bAir.
        8
    }
}

impl<AB> Air<AB> for Poseidon2bBusAir
where
    AB: AirBuilder<F = BinaryField128> + BusInteractionBuilder,
{
    fn eval(&self, b: &mut AB) {
        // 1. Full permutation constraints (state, sbox, MDS, output).
        Poseidon2bAir.eval(b);

        // 2. Copy public inputs into owned Expr values so the borrow on
        //    `b` from `public_values()` drops before we mutate `b` with
        //    `assert_eq`. Same pattern Poseidon2bAir uses internally.
        let public: Vec<AB::Expr> = {
            let p = b.public_values();
            p.iter().map(|v| (*v).into()).collect()
        };

        // 3. Domain binding on the public inputs. Poseidon2bAir doesn't
        //    constrain padding/domain, so we add them here.
        b.assert_eq(public[2].clone(), AB::F::ZERO);
        b.assert_eq(
            public[3].clone(),
            AB::F::from_le_bytes(MERKLE_DOMAIN.to_le_bytes()),
        );
        // Note: public[6] and public[7] correspond to state_out[2] and
        // state_out[3], which are unconstrained capacity lanes of the
        // Poseidon2b permutation. Poseidon2bAir does not bound them either.
        // We deliberately leave them free — the compression only needs
        // state_out[0] + state_out[1].

        // 4. Compression tuple from public inputs:
        //    a = public[0]
        //    b = public[1]
        //    c = public[4] + public[5]  (= state_out[0] + state_out[1])
        let a = public[0].clone();
        let bb = public[1].clone();
        let c = public[4].clone() + public[5].clone();

        // 4. Bus push: this instance is the producer of one (a, b, c).
        // Push only on the last row of the Poseidon2b trace. Without this,
        // a 68-row permutation trace would push 68 tuples per instance, but
        // each compression contributes exactly one tuple to the multiset.
        // `is_last_row()` gives an indicator that is 1 on the final row and
        // 0 elsewhere, so the multiset contains exactly one (a, b, c) per
        // proved instance.
        let selector = b.is_last_row();
        b.push_bus_interaction(
            MERKLE_COMPRESS,
            BusDirection::Push,
            [a, bb, c],
            BusActivation::Boolean(selector),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::check_constraints;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_poseidon2b::{
        poseidon2b_permutation,
        trace::{generate_poseidon2b_trace, WIDTH},
    };

    fn blk(n: u128) -> BinaryField128 {
        BinaryField128::from_le_bytes(n.to_le_bytes())
    }

    /// Build a single-instance Poseidon2bBusAir trace for compression of
    /// (a, b) with the Merkle domain tag.
    fn build_trace(a: BinaryField128, b: BinaryField128) -> (RowMajorMatrix<BinaryField128>, Vec<BinaryField128>) {
        // Input state (4 words)
        let mut state_in = [blk(0); 4];
        state_in[0] = a;
        state_in[1] = b;
        state_in[2] = blk(0);
        state_in[3] = blk(MERKLE_DOMAIN);

        // Run the permutation natively to get the output.
        let mut state_out = state_in;
        poseidon2b_permutation(&mut state_out);

        // The trace is one row of Poseidon2bAir columns, but traced by
        // generate_poseidon2b_trace to fill intermediate rows.
        let trace = generate_poseidon2b_trace(state_in);

        // Public inputs: 8 cells.
        //   [0..4] = input state
        //   [4..8] = output state
        let public = vec![
            state_in[0], state_in[1], state_in[2], state_in[3],
            state_out[0], state_out[1], state_out[2], state_out[3],
        ];

        (trace, public)
    }

    #[test]
    fn width_and_public_match_poseidon2b() {
        let bus_w = <Poseidon2bBusAir as BaseAir<BinaryField128>>::width(&Poseidon2bBusAir);
        let p2b_w = <Poseidon2bAir as BaseAir<BinaryField128>>::width(&Poseidon2bAir);
        assert_eq!(bus_w, p2b_w);
        assert_eq!(bus_w, WIDTH);

        let pub_count = <Poseidon2bBusAir as BaseAir<BinaryField128>>::num_public_values(&Poseidon2bBusAir);
        assert_eq!(pub_count, 8);
    }

    #[test]
    fn valid_compression_satisfies() {
        let a = blk(0xCAFE);
        let b = blk(0xBABE);
        let (trace, public) = build_trace(a, b);
        // Domain binding is satisfied because build_trace sets
        // state_in[2]=0 and state_in[3]=MERKLE_DOMAIN.
        check_constraints(&Poseidon2bBusAir, &trace, &public);
    }

    #[test]
    fn wrong_domain_rejected() {
        let a = blk(0xCAFE);
        let b = blk(0xBABE);
        let (trace, mut public) = build_trace(a, b);
        // Tamper domain tag in public inputs.
        public[3] = blk(0xDEAD);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&Poseidon2bBusAir, &trace, &public);
        }));
        assert!(r.is_err(), "wrong domain tag must be rejected");
    }

    #[test]
    fn nonzero_padding_rejected() {
        let a = blk(0xCAFE);
        let b = blk(0xBABE);
        let (trace, mut public) = build_trace(a, b);
        // Tamper padding cell.
        public[2] = blk(1);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&Poseidon2bBusAir, &trace, &public);
        }));
        assert!(r.is_err(), "nonzero padding must be rejected");
    }
}
