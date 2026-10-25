//! Day 4 viability probe: does BinaryAirConstraintPlan::from_air
//! accept our custom verifier AIRs?

#![cfg(feature = "frost-gkr")]

use p3_binary_field::BinaryField128;
use p3_recursion::verifier::BinaryAirConstraintPlan;

use p3_recursion::frost_gkr::extraction_air::ExtractionAir;
use p3_recursion::frost_gkr::pcs_open_air::PcsOpenAir;
use p3_recursion::frost_gkr::verifier_air::FrostGkrVerifierAir;
use p3_recursion::frost_gkr::full_verifier_air::FrostGkrFullVerifierAir;

#[test]
fn probe_extraction_air_accepted() {
    let plan = BinaryAirConstraintPlan::<BinaryField128>::from_air(&ExtractionAir, 0);
    assert!(plan.is_ok(), "ExtractionAir rejected: {:?}", plan.err());
}

#[test]
fn probe_pcs_open_air_accepted() {
    let plan = BinaryAirConstraintPlan::<BinaryField128>::from_air(&PcsOpenAir, 0);
    assert!(plan.is_ok(), "PcsOpenAir rejected: {:?}", plan.err());
}

#[test]
fn probe_verifier_air_accepted() {
    let plan = BinaryAirConstraintPlan::<BinaryField128>::from_air(&FrostGkrVerifierAir, 0);
    assert!(plan.is_ok(), "FrostGkrVerifierAir rejected: {:?}", plan.err());
}

#[test]
fn probe_full_verifier_air_accepted() {
    let plan = BinaryAirConstraintPlan::<BinaryField128>::from_air(&FrostGkrFullVerifierAir, 0);
    assert!(plan.is_ok(), "FrostGkrFullVerifierAir rejected: {:?}", plan.err());
}
