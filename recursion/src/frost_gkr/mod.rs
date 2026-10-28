//! FROST-GKR: 15-variable unified sumcheck for 64-Poseidon2b-per-batch.
//! Ported from ignotusnemo/frost-gkr (Apache-2.0).
//! Adapted for p3-binary-field and p3-poseidon2b.

pub mod core;
pub mod unified_mle;
pub mod unified_sumcheck;
pub mod shift;
pub mod e3_scale;
pub mod recursive_aggregator;
pub mod extraction_air;
pub mod full_verifier_air;
pub mod recursion_integration;
pub mod benchmarks;
pub mod pcs_open_air;
pub mod verifier_air;
pub mod sequence;
pub mod layers;

#[cfg(test)]
mod correctness_tests {
    use crate::frost_gkr::core::tower::Block128;
    use crate::frost_gkr::core::field::TowerField;
    use crate::frost_gkr::core::mle::eq::eq_ind_partial_eval;
    use crate::frost_gkr::core::mle::evaluate::evaluate_slice;
    use crate::frost_gkr::core::packed::pow7::pow7_block128;

    // Test 1: eq tensor + field axioms
    #[test]
    fn test1a_eq_ind_partial_eval_sums_to_one() {
        let rho = [Block128(2), Block128(3)];
        let result = eq_ind_partial_eval(&rho);
        assert_eq!(result.len(), 4);
        let sum = result.iter().fold(Block128::ZERO, |a, b| a + *b);
        assert_eq!(sum, Block128::ONE, "eq tensor must sum to 1");
    }

    #[test]
    fn test1b_block128_field_axioms() {
        let a = Block128(5);
        let b = Block128(7);
        assert_eq!(a + b, b + a);
        assert_eq!(a * b, b * a);
        assert_eq!(a + Block128::ZERO, a);
        assert_eq!(a * Block128::ONE, a);
    }

    // Test 2: evaluate_slice
    #[test]
    fn test2a_evaluate_slice_trivial_case() {
        let a = Block128(10);
        let b = Block128(20);
        let evals = [a, b];
        assert_eq!(evaluate_slice(&evals, &[Block128::ZERO]), a);
        assert_eq!(evaluate_slice(&evals, &[Block128::ONE]), b);
    }

    #[test]
    fn test2b_evaluate_slice_constant_poly() {
        let v = Block128(42);
        let evals = [v, v, v, v];
        let r = [Block128(3), Block128(5)];
        assert_eq!(evaluate_slice(&evals, &r), v);
    }

    // Test 3: pow7
    #[test]
    fn test3a_pow7_matches_naive() {
        for x in [Block128(0), Block128(1), Block128(2), Block128(255), Block128(u64::MAX as u128)] {
            let x2 = x * x;
            let x4 = x2 * x2;
            assert_eq!(pow7_block128(x), x * x2 * x4);
        }
    }

    #[test]
    fn test3b_pow7_zero_and_one() {
        assert_eq!(pow7_block128(Block128(0)), Block128(0));
        assert_eq!(pow7_block128(Block128(1)), Block128(1));
    }

    // Test 4: Poseidon2b permutation
    #[test]
    fn test4a_poseidon2b_permutation_is_deterministic() {
        use p3_poseidon2b::poseidon2b_permutation;
        use p3_binary_field::{BinaryField128, TowerLevel};
        let to_field = |b: Block128| BinaryField128::from_repr(b.0);
        let to_block = |f: BinaryField128| Block128(f.to_repr());
        let input = [Block128(1), Block128(2), Block128(3), Block128(4)];
        let mut fs1: [BinaryField128; 4] = core::array::from_fn(|i| to_field(input[i]));
        let mut fs2 = fs1.clone();
        poseidon2b_permutation(&mut fs1);
        poseidon2b_permutation(&mut fs2);
        let out1: [Block128; 4] = core::array::from_fn(|i| to_block(fs1[i]));
        let out2: [Block128; 4] = core::array::from_fn(|i| to_block(fs2[i]));
        assert_eq!(out1, out2);
    }

    #[test]
    fn test4b_poseidon2b_permutation_not_identity() {
        use p3_poseidon2b::poseidon2b_permutation;
        use p3_binary_field::BinaryField128;
        let input: [BinaryField128; 4] = core::array::from_fn(|i| {
            let mut bytes = [0u8; 16];
            bytes[0] = (i + 1) as u8;
            BinaryField128::from_le_bytes(bytes)
        });
        let mut state = input;
        poseidon2b_permutation(&mut state);
        assert_ne!(state, input);
    }

    // Test 5: parameters + API surface
    #[test]
    fn test5a_frost_gkr_parameters() {
        use crate::frost_gkr::unified_mle::{
            N_LANE_VARS, N_ROUND_VARS, N_SLOT_VARS, N_UNIFIED_VARS, N_UNIFIED_CELLS,
        };
        use crate::frost_gkr::unified_sumcheck::UNIFIED_ROUND_DEGREE;
        use crate::frost_gkr::sequence::N_PERMUTATIONS;
        assert_eq!(N_LANE_VARS, 2);
        assert_eq!(N_ROUND_VARS, 7);
        assert_eq!(N_SLOT_VARS, 6);
        assert_eq!(N_UNIFIED_VARS, 15);
        assert_eq!(N_UNIFIED_CELLS, 1 << 15);
        assert_eq!(UNIFIED_ROUND_DEGREE, 9);
        assert_eq!(N_PERMUTATIONS, 59);
    }

    #[test]
    fn test5b_frost_gkr_api_callable() {
        use crate::frost_gkr::unified_sumcheck::{
            prove_unified_sumcheck, verify_unified_sumcheck,
        };
        let _ = prove_unified_sumcheck::<FakeFs>;
        let _ = verify_unified_sumcheck::<FakeFs>;
    }

    // FakeFs: minimal FiatShamir for API-surface check
    struct FakeFs;
    impl crate::frost_gkr::core::transcript::FiatShamir<Block128> for FakeFs {
        fn absorb(&mut self, _elem: Block128) {}
        fn squeeze(&mut self) -> Block128 { Block128(0) }
        fn squeeze_n(&mut self, n: usize) -> alloc::vec::Vec<Block128> {
            alloc::vec![Block128(0); n]
        }
    }

    // Test 6: FROST-GKR round-trip on 59-permutation batch
    #[test]
    fn test6_full_frost_gkr_round_trip() {
        use crate::frost_gkr::core::channel::Poseidon2bChannel;
        use crate::frost_gkr::core::native::permutation::STATE_SIZE;
        use crate::frost_gkr::sequence::{evaluate_sequence, SequenceInput};
        use crate::frost_gkr::unified_mle::build_unified_mle;
        use crate::frost_gkr::unified_sumcheck::{
            prove_unified_sumcheck, verify_unified_sumcheck, prove_shift, verify_shift,
        };
        let input = SequenceInput {
            initial_state: [Block128(1), Block128(2), Block128(3), Block128(4)],
        };
        let witness = evaluate_sequence(&input);
        assert_eq!(witness.states.len(), 59);
        let slot_state_ins: alloc::vec::Vec<[Block128; STATE_SIZE]> =
            witness.states.iter().map(|(s_in, _)| *s_in).collect();
        let (mle, _) = build_unified_mle(&slot_state_ins);
        let mut prover_ch = Poseidon2bChannel::new();
        let (unified_proof, r_prime) = prove_unified_sumcheck(&mle, &mut prover_ch);
        let (shift_proof, _) = prove_shift(&mle, &r_prime, &mut prover_ch);
        let mut verifier_ch = Poseidon2bChannel::new();
        let main_red = verify_unified_sumcheck(&unified_proof, &mut verifier_ch)
            .expect("unified sumcheck verify failed");
        verify_shift(&shift_proof, &main_red, &mut verifier_ch)
            .expect("shift verify failed");
    }

    // Test 7: soundness - tampered proof fails
    #[test]
    fn test7_soundness_tampered_proof_fails() {
        use crate::frost_gkr::core::channel::Poseidon2bChannel;
        use crate::frost_gkr::core::native::permutation::STATE_SIZE;
        use crate::frost_gkr::sequence::{evaluate_sequence, SequenceInput};
        use crate::frost_gkr::unified_mle::build_unified_mle;
        use crate::frost_gkr::unified_sumcheck::{
            prove_unified_sumcheck, verify_unified_sumcheck,
        };
        let input = SequenceInput {
            initial_state: [Block128(1), Block128(2), Block128(3), Block128(4)],
        };
        let witness = evaluate_sequence(&input);
        let slot_state_ins: alloc::vec::Vec<[Block128; STATE_SIZE]> =
            witness.states.iter().map(|(s_in, _)| *s_in).collect();
        let (mle, _) = build_unified_mle(&slot_state_ins);
        let mut prover_ch = Poseidon2bChannel::new();
        let (unified_proof, _) = prove_unified_sumcheck(&mle, &mut prover_ch);
        let mut tampered = unified_proof.clone();
        tampered.s_in_dec_at_r = tampered.s_in_dec_at_r + Block128(1);
        let mut verifier_ch = Poseidon2bChannel::new();
        assert!(verify_unified_sumcheck(&tampered, &mut verifier_ch).is_none());
    }

    // Test 8: E3 minimal - three independent 59-permutation batches
    #[test]
    fn test8_e3_minimal_three_batches() {
        use crate::frost_gkr::e3_scale::{prove_batch_chain, verify_batch_chain};
        let chain = prove_batch_chain(1, 3);
        assert_eq!(chain.n_batches, 3);
        assert_eq!(chain.n_permutations, 3 * 59);
        assert!(verify_batch_chain(&chain, 1));
    }

    // Test 9: E3 chain tampering detected
    #[test]
    fn test9_e3_chain_tampering_rejected() {
        use crate::frost_gkr::e3_scale::{prove_batch_chain, verify_batch_chain};
        let mut chain = prove_batch_chain(1, 3);
        chain.batch_commitments[1] = chain.batch_commitments[1] + Block128(1);
        assert!(!verify_batch_chain(&chain, 1));
    }

    // Test 10: E3 medium scale - 10 batches = 590 permutations
    #[test]
    fn test10_e3_medium_scale_10_batches() {
        use crate::frost_gkr::e3_scale::{prove_batch_chain, verify_batch_chain};
        let chain = prove_batch_chain(1, 10);
        assert_eq!(chain.n_batches, 10);
        assert_eq!(chain.n_permutations, 10 * 59);
        assert!(verify_batch_chain(&chain, 1));
    }

    // Test 11: Benchmark - measure single-batch prove time
    #[test]
    fn test11_benchmark_single_batch() {
        use crate::frost_gkr::e3_scale::bench_single_batch;
        // Warm up
        let _ = bench_single_batch(1);
        // Measure 3 runs
        let mut times = alloc::vec::Vec::new();
        for i in 0..3u128 {
            times.push(bench_single_batch(i + 1));
        }
        let avg = times.iter().sum::<core::time::Duration>() / 3;
        std::println!(
            "Single batch (59 perms): {:?}  [runs: {:?}, {:?}, {:?}]",
            avg, times[0], times[1], times[2]
        );
    }

    // Test 12: Benchmark - extrapolate to 262K
    #[test]
    fn test12_benchmark_extrapolate_262k() {
        use crate::frost_gkr::e3_scale::{bench_n_batches, batches_for_permutations};
        let n_batches = batches_for_permutations(262_144);
        // Measure 10-batch baseline
        let t10 = bench_n_batches(1, 10);
        let per_batch = t10 / 10;
        let extrapolated = per_batch * n_batches as u32;
        std::println!(
            "10 batches: {:?}  |  per batch: {:?}  |  {} batches (262K): ~{:?}",
            t10, per_batch, n_batches, extrapolated
        );
    }

    // Test 13: 500-batch scale smoke test (~2 min)
    #[test]
    fn test13_scale_500_batches() {
        use crate::frost_gkr::e3_scale::{prove_batch_chain, verify_batch_chain, permutations_for_batches};
        let target_batches = 500;
        let start = std::time::Instant::now();
        let chain = prove_batch_chain(1, target_batches);
        let prove_time = start.elapsed();
        assert_eq!(chain.n_batches, target_batches);
        assert_eq!(chain.n_permutations, permutations_for_batches(target_batches));

        let start = std::time::Instant::now();
        let ok = verify_batch_chain(&chain, 1);
        let verify_time = start.elapsed();
        assert!(ok, "500-batch chain must verify");

        std::println!(
            "500 batches ({} perms): prove={:?} verify={:?}",
            target_batches * 59, prove_time, verify_time
        );
    }

    // Test 14: Full 262K end-to-end (marked #[ignore], ~20 min)
    #[test]
    #[ignore]
    fn test14_full_262k_end_to_end() {
        use crate::frost_gkr::e3_scale::{prove_batch_chain, verify_batch_chain, batches_for_permutations};
        let target_perms = 262_144usize;
        let n_batches = batches_for_permutations(target_perms);
        std::println!(
            "262K proof: {} batches * 59 perms = {} perms (target {})",
            n_batches, n_batches * 59, target_perms
        );

        let start = std::time::Instant::now();
        let chain = prove_batch_chain(1, n_batches);
        let prove_time = start.elapsed();
        assert_eq!(chain.n_batches, n_batches);
        assert_eq!(chain.batch_commitments.len(), n_batches);

        let start = std::time::Instant::now();
        let ok = verify_batch_chain(&chain, 1);
        let verify_time = start.elapsed();
        assert!(ok, "262K chain must verify");

        std::println!(
            "262K end-to-end: prove={:?} verify={:?} total={:?}",
            prove_time, verify_time, prove_time + verify_time
        );
    }

    // Test 15: Parallel 500-batch (compare to test13 sequential)
    #[test]
    fn test15_parallel_500_batches() {
        use crate::frost_gkr::e3_scale::{
            prove_batch_chain_parallel, verify_batch_chain_parallel,
        };
        let start = std::time::Instant::now();
        let chain = prove_batch_chain_parallel(1, 500);
        let prove_time = start.elapsed();
        assert_eq!(chain.n_batches, 500);

        let start = std::time::Instant::now();
        let ok = verify_batch_chain_parallel(&chain, 1);
        let verify_time = start.elapsed();
        assert!(ok);

        std::println!(
            "500 batches parallel: prove={:?} verify={:?}",
            prove_time, verify_time
        );
    }

    // Test 16: Parallel 4444-batch (full 262K)
    #[test]
    #[ignore]
    fn test16_parallel_full_262k() {
        use crate::frost_gkr::e3_scale::{
            prove_batch_chain_parallel, verify_batch_chain_parallel, batches_for_permutations,
        };
        let n_batches = batches_for_permutations(262_144);
        std::println!("Parallel 262K: {} batches", n_batches);
        let start = std::time::Instant::now();
        let chain = prove_batch_chain_parallel(1, n_batches);
        let prove_time = start.elapsed();
        let start = std::time::Instant::now();
        let ok = verify_batch_chain_parallel(&chain, 1);
        let verify_time = start.elapsed();
        assert!(ok);
        std::println!(
            "Parallel 262K: prove={:?} verify={:?} total={:?}",
            prove_time, verify_time, prove_time + verify_time
        );
    }
}
pub mod blake3_multi_stark;
pub mod poseidon2b_bus_air;
pub mod combined_air;
pub mod binary_aggregation_air;
pub mod binary_verifier_air;
pub mod fri_verifier_air_v2;
pub mod blake3_bridge;
