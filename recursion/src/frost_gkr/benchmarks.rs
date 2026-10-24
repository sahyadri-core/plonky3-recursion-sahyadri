//! Millisecond-level timing for FROST-GKR primitives.
//!
//! Run: cargo test -p p3-recursion --features frost-gkr,parallel --release
//!       --lib -- frost_gkr::benchmarks --ignored --nocapture

#[cfg(test)]
mod tests {
    use super::super::core::channel::Poseidon2bChannel;
    use super::super::core::native::permutation::STATE_SIZE;
    use super::super::core::tower::Block128;
    use super::super::e3_scale::{prove_batch_chain, prove_batch_chain_parallel, verify_batch_chain_parallel};
    use super::super::sequence::{evaluate_sequence, SequenceInput};
    use super::super::unified_mle::build_unified_mle;
    use super::super::unified_sumcheck::{prove_unified_sumcheck, verify_unified_sumcheck, prove_shift, verify_shift};

    fn ms(d: core::time::Duration) -> f64 {
        d.as_secs_f64() * 1000.0
    }

    #[test]
    #[ignore]
    fn bench_single_batch_breakdown() {
        use std::time::Instant;

        let input = SequenceInput {
            initial_state: [Block128(1), Block128(2), Block128(3), Block128(4)],
        };

        let t0 = Instant::now();
        let witness = evaluate_sequence(&input);
        let t_seq = t0.elapsed();

        let slot_state_ins: alloc::vec::Vec<[Block128; STATE_SIZE]> =
            witness.states.iter().map(|(s_in, _)| *s_in).collect();

        let t0 = Instant::now();
        let (mle, _) = build_unified_mle(&slot_state_ins);
        let t_mle = t0.elapsed();

        let mut ch = Poseidon2bChannel::new();
        let t0 = Instant::now();
        let (unified_proof, r_prime) = prove_unified_sumcheck(&mle, &mut ch);
        let t_prove_unified = t0.elapsed();

        let t0 = Instant::now();
        let (shift_proof, _) = prove_shift(&mle, &r_prime, &mut ch);
        let t_prove_shift = t0.elapsed();

        let mut vch = Poseidon2bChannel::new();
        let t0 = Instant::now();
        let main_red = verify_unified_sumcheck(&unified_proof, &mut vch).expect("verify_unified");
        let t_verify_unified = t0.elapsed();

        let t0 = Instant::now();
        let _ = verify_shift(&shift_proof, &main_red, &mut vch).expect("verify_shift");
        let t_verify_shift = t0.elapsed();

        println!("SINGLE BATCH (59 perms):");
        println!("  evaluate_sequence    {:>8.2} ms", ms(t_seq));
        println!("  build_unified_mle    {:>8.2} ms", ms(t_mle));
        println!("  prove_unified_sumcheck {:>6.2} ms", ms(t_prove_unified));
        println!("  prove_shift          {:>8.2} ms", ms(t_prove_shift));
        println!("  verify_unified_sumcheck {:>4.2} ms", ms(t_verify_unified));
        println!("  verify_shift         {:>8.2} ms", ms(t_verify_shift));
        println!("  total prove          {:>8.2} ms", ms(t_mle + t_prove_unified + t_prove_shift));
        println!("  total verify         {:>8.2} ms", ms(t_verify_unified + t_verify_shift));
    }

    #[test]
    #[ignore]
    fn bench_chain_scaling() {
        use std::time::Instant;
        for n in [10usize, 100, 500, 1000] {
            let t0 = Instant::now();
            let chain = prove_batch_chain(1, n);
            let seq = t0.elapsed();
            let t0 = Instant::now();
            let ok = super::super::e3_scale::verify_batch_chain(&chain, 1);
            let seq_verify = t0.elapsed();
            assert!(ok);
            println!(
                "N={:>5}  prove={:>10.2} ms ({:>6.2} ms/batch)  verify={:>10.2} ms",
                n,
                ms(seq),
                ms(seq) / n as f64,
                ms(seq_verify)
            );
        }
    }

    #[test]
    #[ignore]
    fn bench_chain_parallel() {
        use std::time::Instant;
        for n in [100usize, 500, 2000] {
            let t0 = Instant::now();
            let chain = prove_batch_chain_parallel(1, n);
            let par = t0.elapsed();
            let t0 = Instant::now();
            let ok = verify_batch_chain_parallel(&chain, 1);
            let par_verify = t0.elapsed();
            assert!(ok);
            println!(
                "N={:>5}  prove={:>10.2} ms ({:>6.2} ms/batch)  verify={:>10.2} ms",
                n,
                ms(par),
                ms(par) / n as f64,
                ms(par_verify)
            );
        }
    }

    #[test]
    #[ignore]
    fn bench_262k_full() {
        use std::time::Instant;
        let n = 4444usize;
        let t0 = Instant::now();
        let chain = prove_batch_chain_parallel(1, n);
        let prove = t0.elapsed();
        let t0 = Instant::now();
        let ok = verify_batch_chain_parallel(&chain, 1);
        let verify = t0.elapsed();
        assert!(ok);
        println!(
            "262K (4444 batches, parallel): prove={:.2} ms  verify={:.2} ms  total={:.2} ms ({:.2} s)",
            ms(prove),
            ms(verify),
            ms(prove) + ms(verify),
            (prove + verify).as_secs_f64()
        );
    }
}
