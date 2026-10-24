//! FROST-GKR runtime correctness tests.
#![cfg(feature = "frost-gkr")]

use crate::frost_gkr::core::tower::Block128;
use crate::frost_gkr::core::mle::eq::eq_ind;
use crate::frost_gkr::core::field::TowerField;

#[test]
fn eq_ind_property_sum_is_one() {
    let rho = [Block128(2), Block128(3)];
    let result = eq_ind(&rho);
    assert_eq!(result.len(), 4);
    let sum = result.iter().fold(Block128::ZERO, |a, b| a + *b);
    assert_eq!(sum, Block128::ONE, "eq polynomial should sum to 1");
}
