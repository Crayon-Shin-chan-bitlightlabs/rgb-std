#![cfg(not(target_arch = "wasm32"))]

#[macro_use]
extern crate amplify;
#[macro_use]
extern crate strict_types;

mod utils;

use std::collections::BTreeSet;
use std::num::NonZeroU64;

use bp::seals::TxoSeal;
use bp::Tx;
use rgb::{Contract, WitnessStatus};
use rgb_persist_fs::{PileFs, StockFs};
use rgbcore::ContractApi;
use single_use_seals::SealWitness;
use strict_encoding::StrictDumb;

use crate::utils::setup;

/// After a `sync`, the incrementally-maintained `valid_cache` (observed through `is_known`) must
/// match a full rebuild from the ledger (`valid_opids`), restricted to the contract's operation
/// universe. This guards the incremental `apply_valid_cache_delta` path used by `sync` against
/// drift over the descendant closure.
fn assert_valid_cache_matches_full_rebuild(contract: &mut Contract<StockFs, PileFs<TxoSeal>>) {
    let opids = contract
        .operations()
        .into_iter()
        .map(|(opid, _, _)| opid)
        .collect::<Vec<_>>();
    let incremental = opids
        .iter()
        .copied()
        .filter(|opid| contract.is_known(*opid))
        .collect::<BTreeSet<_>>();
    let full_all = contract.valid_opids().into_iter().collect::<BTreeSet<_>>();
    let full = opids
        .iter()
        .copied()
        .filter(|opid| full_all.contains(opid))
        .collect::<BTreeSet<_>>();
    assert_eq!(incremental, full, "incremental valid_cache diverged from full rebuild after sync");
}

#[test]
fn no_reorgs() { setup("NoReorgs"); }

#[test]
fn single_rollback() {
    let mut contract = setup("SingleRollback");
    let wid = contract.witness_ids().into_iter().nth(50).unwrap();
    contract.sync([(wid, WitnessStatus::Archived)]).unwrap();
    // Idempotence
    contract.sync([(wid, WitnessStatus::Archived)]).unwrap();
    assert_valid_cache_matches_full_rebuild(&mut contract);
}

#[test]
fn double_rollback() {
    let mut contract = setup("DoubleRollback");
    let wid1 = contract.witness_ids().into_iter().nth(50).unwrap();
    let wid2 = contract.witness_ids().into_iter().nth(60).unwrap();
    contract
        .sync([(wid1, WitnessStatus::Archived), (wid2, WitnessStatus::Archived)])
        .unwrap();
    assert_valid_cache_matches_full_rebuild(&mut contract);
}

#[test]
fn rollback_forward() {
    let mut contract = setup("RollbackForward");
    let wid = contract.witness_ids().into_iter().nth(50).unwrap();
    contract.sync([(wid, WitnessStatus::Archived)]).unwrap();
    contract.sync([(wid, WitnessStatus::Offchain)]).unwrap();
    // Idempotence
    contract
        .sync([(wid, WitnessStatus::Archived), (wid, WitnessStatus::Offchain)])
        .unwrap();
    assert_valid_cache_matches_full_rebuild(&mut contract);
}

#[test]
fn rbf() {
    let mut contract = setup("Rbf");

    let old_txid = contract.witness_ids().into_iter().nth(50).unwrap();
    let opid = contract
        .ops_by_witness_id(old_txid)
        .into_iter()
        .next()
        .unwrap();

    let warmed_seals = contract.known_resolved_seals();
    let (addr, old_resolved_seal) = warmed_seals
        .into_iter()
        .find(|(addr, _)| addr.opid == opid)
        .expect("target op should have a known resolved seal");

    let tx = Tx::strict_dumb();
    let rbf_txid = tx.txid();
    contract.apply_witness(opid, SealWitness::new(tx, strict_dumb!()));

    contract
        .sync([
            (old_txid, WitnessStatus::Archived),
            (rbf_txid, WitnessStatus::Mined(NonZeroU64::new(100).unwrap())),
        ])
        .unwrap();

    let (_, new_resolved_seal) = contract
        .known_resolved_seals()
        .into_iter()
        .find(|(known_addr, _)| *known_addr == addr)
        .expect("target seal should remain known after RBF sync");
    assert_ne!(old_resolved_seal, new_resolved_seal);
}
