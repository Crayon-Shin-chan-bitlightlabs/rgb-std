#![cfg(not(target_arch = "wasm32"))]

#[macro_use]
extern crate amplify;
#[macro_use]
extern crate strict_types;

mod utils;

use std::collections::BTreeSet;

use amplify::confinement::Confined;
use bp::seals::{Anchor, TxoSeal, WTxoSeal};
use bp::{LockTime, Tx};
use commit_verify::{Digest, DigestExt, Sha256};
use hypersonic::{CallParams, CellAddr};
use rgb::{take_last_known_resolvable_boundary_phase_stats, CoreParams, NamedState, Outpoint};
use rgbcore::{ContractApi, RgbSealDef};
use single_use_seals::SealWitness;
use strict_encoding::{vname, StrictDumb};

use crate::utils::setup;

/// `owned_seals()` is the batched, status-free replacement for deriving seal membership out of
/// `state()`; the two must agree cell-for-cell on both direct (external-outpoint) and
/// witness-relative seal definitions.
#[test]
fn owned_seals_matches_state() {
    let mut contract = setup("OwnedSeals");

    // The fixture produces witness-relative seals only; append one more transfer whose outputs
    // mix a direct (external-outpoint) seal with a witness-relative one so both `to_src()`
    // branches are exercised.
    let prev = contract
        .full_state()
        .main
        .owned
        .get("amount")
        .unwrap()
        .keys()
        .copied()
        .collect::<Vec<_>>();

    let mut noise_engine = Sha256::new();
    noise_engine.input_raw(b"owned-seals");
    let direct = WTxoSeal::no_fallback(Outpoint::strict_dumb(), noise_engine.clone(), 1);
    let relative = WTxoSeal::vout_no_fallback(1u32.into(), noise_engine, 2);

    let mut params = CallParams {
        core: CoreParams { method: vname!("transfer"), global: none!(), owned: none!() },
        using: none!(),
        reading: none!(),
    };
    params.using.insert(prev[0], None);
    params.using.insert(prev[1], None);
    let seals = small_bmap![0 => direct, 1 => relative];
    params
        .core
        .owned
        .push(NamedState::new_unlocked("amount", seals[&0].auth_token(), 90u64));
    params
        .core
        .owned
        .push(NamedState::new_unlocked("amount", seals[&1].auth_token(), 90u64));
    let op = contract.call(params, seals).unwrap();
    let tx = Tx {
        version: default!(),
        inputs: Confined::from_checked(vec![]),
        outputs: Confined::from_checked(vec![]),
        lock_time: LockTime::from_consensus_u32(u16::MAX as u32),
    };
    contract.apply_witness(op.opid(), SealWitness::new(tx, Anchor::strict_dumb()));

    let expected = contract
        .state()
        .owned
        .values()
        .flatten()
        .map(|state| state.assignment.seal)
        .collect::<BTreeSet<TxoSeal>>();
    let got = contract.owned_seals().into_iter().collect::<BTreeSet<TxoSeal>>();

    assert!(!got.is_empty());
    assert_eq!(got, expected);
}

/// The combined receiver-boundary traversal must be exactly equivalent to the established
/// two-call path, while the established API must continue filtering arbitrary non-member cells.
#[test]
fn known_resolvable_boundary_matches_membership_checked_path() {
    let mut contract = setup("KnownResolvableBoundary");

    // Add an operation whose complete output set uses direct seals. The setup fixture uses only
    // witness-relative tentative seals, which are intentionally excluded from a stable receiver
    // boundary until mined.
    let prev = contract
        .full_state()
        .main
        .owned
        .get("amount")
        .unwrap()
        .keys()
        .copied()
        .collect::<Vec<_>>();
    let mut noise_engine = Sha256::new();
    noise_engine.input_raw(b"known-resolvable-boundary");
    let first = WTxoSeal::no_fallback(Outpoint::strict_dumb(), noise_engine.clone(), 1);
    let second = WTxoSeal::no_fallback(Outpoint::strict_dumb(), noise_engine, 2);
    let mut params = CallParams {
        core: CoreParams { method: vname!("transfer"), global: none!(), owned: none!() },
        using: none!(),
        reading: none!(),
    };
    params.using.insert(prev[0], None);
    params.using.insert(prev[1], None);
    let seals = small_bmap![0 => first, 1 => second];
    params
        .core
        .owned
        .push(NamedState::new_unlocked("amount", seals[&0].auth_token(), 90u64));
    params
        .core
        .owned
        .push(NamedState::new_unlocked("amount", seals[&1].auth_token(), 90u64));
    let op = contract.call(params, seals).unwrap();
    let tx = Tx {
        version: default!(),
        inputs: Confined::from_checked(vec![]),
        outputs: Confined::from_checked(vec![]),
        lock_time: LockTime::from_consensus_u32(u16::MAX as u32),
    };
    contract.apply_witness(op.opid(), SealWitness::new(tx, Anchor::strict_dumb()));

    let expected_cells = contract.known_resolvable_seal_cells();
    let expected_opids = contract.boundary_opids_for_known_cells(expected_cells.iter().copied());
    let _ = take_last_known_resolvable_boundary_phase_stats();
    let boundary = contract.known_resolvable_boundary();
    let phase_stats = take_last_known_resolvable_boundary_phase_stats();

    assert!(!expected_opids.is_empty());
    assert!(phase_stats.recorded);
    assert_eq!(phase_stats.boundary_cells, boundary.cells.len());
    assert_eq!(phase_stats.boundary_opids, boundary.opids.len());
    assert_eq!(phase_stats.operation_output_counts, contract.operation_output_counts().len());
    assert_eq!(
        take_last_known_resolvable_boundary_phase_stats(),
        Default::default(),
        "taking request-local boundary stats must clear the previous traversal"
    );
    assert_eq!(
        boundary.cells.into_iter().collect::<BTreeSet<_>>(),
        expected_cells.iter().copied().collect::<BTreeSet<_>>()
    );
    assert_eq!(
        boundary.opids.into_iter().collect::<BTreeSet<_>>(),
        expected_opids.iter().copied().collect::<BTreeSet<_>>()
    );

    let known_opid = expected_cells
        .first()
        .expect("fixture must contain a known seal cell")
        .opid;
    let unknown = CellAddr { opid: known_opid, pos: u16::MAX };
    let with_unknown =
        contract.boundary_opids_for_known_cells(expected_cells.iter().copied().chain([unknown]));
    assert_eq!(
        with_unknown.into_iter().collect::<BTreeSet<_>>(),
        expected_opids.into_iter().collect::<BTreeSet<_>>()
    );
}
