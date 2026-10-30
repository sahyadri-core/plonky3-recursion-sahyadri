//! T1.5 probe: does Plonky3's native BinaryMultiStarkVerifier::verify
//! fit in 15GB when wrapped in a prime-field circuit?
//!
//! # Background
//! `binary_multi_stark.rs::verify` requires `CircuitBuilder<EF>` where
//! EF is prime-field extension (Goldilocks, BabyBear). This is the exact
//! A2.3e path that SIGKILL'd at 15GB for wide AIRs.
//!
//! # Probe scope
//! - Small MultiStark proof (2 rows, SC+B3 from T1.4b.2c)
//! - Wrap in CircuitBuilder<Goldilocks> (or BabyBear)
//! - Allocate proof targets
//! - Call verify()
//! - Measure peak memory + prove time
//!
//! # Decision criteria
//! PASS (< 15GB, < 30s)  -> adapt native verifier (T1.5 in 3-5 days)
//! FAIL (SIGKILL/OOM)    -> custom bus verifier AIR (T1.5 in 1-2 weeks)
//!
//! # Status: SCAFFOLD (fill after API discovery)
//!
//! This file deliberately stubs the proof-construction to avoid
//! committing half-working code. Full fill needs:
//! 1. Native MultiStark proof generation (from T1.4b.2c test)
//! 2. `allocate_native_targets` for BinaryMultiStarkProofTargets
//! 3. `BinaryMultiStarkVerifier::new(...)` — constructor discovery
//! 4. CircuitBuilder<Goldilocks> + verify call

#![allow(dead_code)]
#![allow(unused_imports)]

// Placeholder: full implementation next session after API discovery.
// This file exists to document the probe plan, not to run today.

#[test]
#[ignore]
fn probe_native_bus_verifier() {
    // TODO(next session):
    // 1. Generate MultiStarkProof (same as t1_4b2c_bus_integration)
    // 2. Wrap into prime-field CircuitBuilder
    // 3. Measure peak RSS via /proc/self/status
    // 4. Assert peak < 15 GB
    todo!("fill after BinaryMultiStarkVerifier constructor discovery");
}
