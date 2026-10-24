//! Poseidon2b AIR end-to-end test: trace gen + constraint check + native match.

use p3_air::{check_constraints, BaseAir};
use p3_binary_field::BinaryField128;
use p3_matrix::Matrix;
use p3_poseidon2b::{
    generate_poseidon2b_trace, poseidon2b_permutation, Poseidon2bAir,
};
use p3_poseidon2b::trace::{N_STATES, STATE_OFFSET};

type F = BinaryField128;

fn fe(v: u128) -> F {
    F::from_le_bytes(v.to_le_bytes())
}

#[test]
fn trace_matches_native_permutation() {
    let input = [fe(1), fe(2), fe(3), fe(4)];
    let trace = generate_poseidon2b_trace(input);
    let row = trace.row_slice(0).unwrap();

    let final_state = [
        row[STATE_OFFSET + (N_STATES - 1) * 4 + 0],
        row[STATE_OFFSET + (N_STATES - 1) * 4 + 1],
        row[STATE_OFFSET + (N_STATES - 1) * 4 + 2],
        row[STATE_OFFSET + (N_STATES - 1) * 4 + 3],
    ];

    let mut native = input;
    poseidon2b_permutation(&mut native);

    assert_eq!(final_state, native, "trace output != native permutation");
}

#[test]
fn trace_satisfies_air_constraints() {
    let input = [fe(0xdead), fe(0xbeef), fe(0xcafe), fe(0xf00d)];
    let trace = generate_poseidon2b_trace(input);

    let row = trace.row_slice(0).unwrap();
    let mut public = vec![F::from_le_bytes([0u8; 16]); 8];
    for i in 0..4 {
        public[i] = input[i];
        public[4 + i] = row[STATE_OFFSET + (N_STATES - 1) * 4 + i];
    }

    check_constraints(&Poseidon2bAir, &trace, &public);
}

#[test]
fn air_width_is_power_of_two() {
    let w = <Poseidon2bAir as BaseAir<F>>::width(&Poseidon2bAir);
    assert!(w.is_power_of_two());
    assert_eq!(w, 1024);
}
