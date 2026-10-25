//! Path C probe: can BinaryField128 be its own extension field?
//!
//! MultiStarkConfig requires Challenge: ExtensionField<Val>.
//! If Val=Challenge=BF128 satisfies that trait, 3E needs no field work.

#![allow(clippy::too_many_arguments)]

use p3_binary_field::BinaryField128;
use p3_binary_pcs::{BinaryPcs, BinaryPcsConfig, BinaryPcsParams, GroupedCodewordMmcs};
use p3_multi_stark::config::MultiStarkConfig;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_test_utils::binary_field_params::blake3;

type F = BinaryField128;
type E = BinaryField128; // <-- the probe: Val == Challenge
type Tree = blake3::LevelMmcs<F>;
type RoundTree = blake3::LevelMmcs<E>;
type M = GroupedCodewordMmcs<Tree>;
type ME = GroupedCodewordMmcs<RoundTree>;
type Ch = blake3::LevelChallenger<F>;

struct ProbeConfig {
    pcs: BinaryPcs<F, E, M, ME>,
}

impl MultiStarkConfig for ProbeConfig {
    type Val = F;
    type Challenge = E;
    type Challenger = Ch;
    type Pcs = BinaryPcs<F, E, M, ME>;
    fn pcs(&self) -> &Self::Pcs { &self.pcs }
    fn min_num_variables(&self) -> usize { 1 }
    fn build_witness(&self, tables: Vec<Table<F>>) -> p3_sumcheck::layout::Witness<F> {
        SuffixProver::<F, E>::new_witness(tables, 0)
    }
    fn committed_table<'a>(
        &self,
        data: &'a p3_binary_pcs::BinaryPcsProverData<F, E, M>,
        index: usize,
    ) -> &'a Table<F> {
        data.table(index)
    }
}

#[test]
fn probe_bf128_as_own_challenge() {
    let cfg = BinaryPcsConfig::try_new::<F, E>(
        10,
        BinaryPcsParams { log_inv_rate: 2, pow_bits: 0, security_level: 40 },
    ).unwrap();
    let mmcs = Tree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()), 0,
    );
    let round = RoundTree::new(
        blake3::FieldHash::new(blake3::byte_hash()),
        blake3::Compress::new(blake3::byte_hash()), 0,
    );
    let _config = ProbeConfig {
        pcs: BinaryPcs::new(cfg, M::new(mmcs, 8), ME::for_folding(round, &cfg)).unwrap(),
    };
    println!("PROBE PASSED: BF128 works as Val AND Challenge");
}
