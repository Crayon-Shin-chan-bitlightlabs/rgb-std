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
use hypersonic::CallParams;
use rgb::{CoreParams, NamedState, Outpoint};
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
