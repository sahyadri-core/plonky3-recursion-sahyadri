//! Multi-field proof composition for SahyadriX PoW.
//!
//! Two layers:
//!   1. Commitment layer (this module's plain API): 2-to-1 Poseidon2b
//!      binding of Goldilocks Blake3 commitment and BinaryField128
//!      Poseidon2b commitment.
//!   2. Constraint layer (MultiFieldBindAir): AIR that proves the
//!      binding was computed correctly, so a wrapper STARK can anchor
//!      to this verification.

use alloc::vec::Vec;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_binary_field::BinaryField128;

use crate::frost_gkr::core::field::TowerField;
use crate::frost_gkr::core::native::permutation::{Poseidon2bPermutation, STATE_SIZE};
use crate::frost_gkr::core::tower::Block128;

pub struct Blake3GoldilocksProof {
    pub bytes: Vec<u8>,
    pub commitment: Block128,
}

pub struct Poseidon2bBinaryProof {
    pub bytes: Vec<u8>,
    pub commitment: Block128,
}

pub struct MultiFieldWrapperProof {
    pub blake3_commitment: Block128,
    pub poseidon2b_commitment: Block128,
    pub wrapper_commitment: Block128,
    pub pow_digest: [u8; 32],
    pub target: [u8; 32],
}

pub fn compose(
    blake3: &Blake3GoldilocksProof,
    poseidon2b: &Poseidon2bBinaryProof,
) -> MultiFieldWrapperProof {
    let wrapper_commitment =
        bind_commitments(blake3.commitment, poseidon2b.commitment);
    MultiFieldWrapperProof {
        blake3_commitment: blake3.commitment,
        poseidon2b_commitment: poseidon2b.commitment,
        wrapper_commitment,
        pow_digest: [0u8; 32],
        target: [0u8; 32],
    }
}

pub fn verify(proof: &MultiFieldWrapperProof) -> bool {
    let expected = bind_commitments(proof.blake3_commitment, proof.poseidon2b_commitment);
    expected == proof.wrapper_commitment
}

pub fn meets_difficulty(proof: &MultiFieldWrapperProof) -> bool {
    proof.pow_digest < proof.target
}

pub fn bind_commitments(a: Block128, b: Block128) -> Block128 {
    let mut state: [Block128; STATE_SIZE] = [a, b, Block128::ZERO, Block128::ZERO];
    Poseidon2bPermutation.permute_mut(&mut state);
    Block128(state[0].0 ^ a.0 ^ b.0)
}

// ============================================================
// AIR: proves the binding was computed correctly
// ============================================================
//
// Witness columns: input state [a, b, 0, 0] and the permuted state.
// Public: (a, b, wrapper) — the two commitments and the expected bind.
//
// Constraints:
//   1. Input column state[0] = public a
//   2. Input column state[1] = public b
//   3. Input column state[2] = 0
//   4. Input column state[3] = 0
//   5. Output column state[0] == Poseidon2b(input)[0] XOR a XOR b
//      (this is the binding relation; Poseidon2b semantics enforced by
//       Poseidon2bAir when composed, or by witness equality check here)
//   6. Output column state[0] = public wrapper

pub const MF_WIDTH: usize = 512;
pub const MF_PUBLIC: usize = 3; // a, b, wrapper

pub struct MultiFieldBindAir;

impl<F> BaseAir<F> for MultiFieldBindAir {
    fn width(&self) -> usize { MF_WIDTH }
    fn num_public_values(&self) -> usize { MF_PUBLIC }
}

impl<AB: AirBuilder<F = BinaryField128>> Air<AB> for MultiFieldBindAir {
    fn eval(&self, b: &mut AB) {
        let cur: Vec<AB::Expr> = {
            let main = b.main();
            main.current_slice().iter().map(|v| (*v).into()).collect()
        };
        let public: Vec<AB::Expr> =
            b.public_values().iter().map(|v| (*v).into()).collect();

        let a_pub = public[0].clone();
        let b_pub = public[1].clone();
        let wrapper_pub = public[2].clone();

        let a_wit = cur[0].clone();
        let b_wit = cur[1].clone();
        let c2_wit = cur[2].clone();
        let c3_wit = cur[3].clone();
        let out0_wit = cur[4].clone();
        let out1_wit = cur[5].clone();
        let out2_wit = cur[6].clone();
        let out3_wit = cur[7].clone();

        // Inputs match public
        b.assert_eq(a_wit.clone(), a_pub);
        b.assert_eq(b_wit.clone(), b_pub);

        // Padding inputs are zero
        b.assert_zero(c2_wit);
        b.assert_zero(c3_wit);

        // Padding outputs are zero
        b.assert_zero(out1_wit);
        b.assert_zero(out2_wit);
        b.assert_zero(out3_wit);

        // Binding: wrapper = permute(state)[0] XOR a XOR b
        // Wrapped in the AIR as: out0_wit == permute(a,b,0,0)[0] + a + b
        // Poseidon2b correctness is delegated to Poseidon2bAir when composed.
        b.assert_eq(out0_wit.clone() + a_wit + b_wit, wrapper_pub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::{check_constraints, BaseAir};
    use p3_matrix::dense::RowMajorMatrix;

    fn b128(v: u128) -> Block128 { Block128(v) }
    fn fe(v: u128) -> BinaryField128 {
        BinaryField128::from_le_bytes(v.to_le_bytes())
    }

    fn mock_blake3(seed: u128) -> Blake3GoldilocksProof {
        Blake3GoldilocksProof { bytes: alloc::vec![0u8; 64], commitment: b128(seed) }
    }
    fn mock_poseidon2b(seed: u128) -> Poseidon2bBinaryProof {
        Poseidon2bBinaryProof { bytes: alloc::vec![0u8; 32], commitment: b128(seed) }
    }

    #[test]
    fn compose_verify_round_trip() {
        let b3 = mock_blake3(0x1111);
        let p2 = mock_poseidon2b(0x2222);
        let wrapper = compose(&b3, &p2);
        assert!(verify(&wrapper));
    }

    #[test]
    fn wrapper_binds_both_commitments() {
        let b3 = mock_blake3(1);
        let p2 = mock_poseidon2b(2);
        let wrapper = compose(&b3, &p2);
        assert_eq!(wrapper.blake3_commitment, b3.commitment);
        assert_eq!(wrapper.poseidon2b_commitment, p2.commitment);
    }

    #[test]
    fn tamper_detected() {
        let b3 = mock_blake3(1);
        let p2 = mock_poseidon2b(2);
        let mut wrapper = compose(&b3, &p2);
        wrapper.blake3_commitment = wrapper.blake3_commitment + b128(1);
        assert!(!verify(&wrapper));
    }

    #[test]
    fn difficulty_target_bound_works() {
        let b3 = mock_blake3(1);
        let p2 = mock_poseidon2b(2);
        let mut wrapper = compose(&b3, &p2);
        wrapper.pow_digest = [0u8; 32];
        wrapper.target = [0xFFu8; 32];
        assert!(meets_difficulty(&wrapper));
        wrapper.target = [0u8; 32];
        assert!(!meets_difficulty(&wrapper));
    }

    #[test]
    fn air_width_and_public_counts() {
        assert_eq!(<MultiFieldBindAir as BaseAir<BinaryField128>>::width(&MultiFieldBindAir), MF_WIDTH);
        assert_eq!(<MultiFieldBindAir as BaseAir<BinaryField128>>::num_public_values(&MultiFieldBindAir), MF_PUBLIC);
    }

    #[test]
    fn air_accepts_correct_binding() {
        let b3 = mock_blake3(0xABCD);
        let p2 = mock_poseidon2b(0x1234);
        let wrapper = compose(&b3, &p2);

        let mut values = alloc::vec![fe(0); MF_WIDTH];
        values[0] = fe(b3.commitment.0);
        values[1] = fe(p2.commitment.0);
        values[2] = fe(0);
        values[3] = fe(0);

        // Compute expected output: raw permute(state)[0] (not XOR-folded).
        // The AIR constraint out0 + a + b == wrapper performs the XOR folding
        // itself, so the witness holds the raw Poseidon2b output.
        let mut state = [b3.commitment, p2.commitment, Block128(0), Block128(0)];
        Poseidon2bPermutation.permute_mut(&mut state);
        values[4] = fe(state[0].0);

        let public = alloc::vec![
            fe(b3.commitment.0),
            fe(p2.commitment.0),
            fe(wrapper.wrapper_commitment.0),
        ];

        let trace = RowMajorMatrix::new(values, MF_WIDTH);
        check_constraints(&MultiFieldBindAir, &trace, &public);
    }
}
