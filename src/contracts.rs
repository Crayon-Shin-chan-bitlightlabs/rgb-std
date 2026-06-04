// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0
//
// Designed in 2019-2025 by Dr Maxim Orlovsky <orlovsky@lnp-bp.org>
// Written in 2024-2025 by Dr Maxim Orlovsky <orlovsky@lnp-bp.org>
//
// Copyright (C) 2019-2024 LNP/BP Standards Association, Switzerland.
// Copyright (C) 2024-2025 LNP/BP Laboratories,
//                         Institute for Distributed and Cognitive Systems (InDCS), Switzerland.
// Copyright (C) 2025 RGB Consortium, Switzerland.
// Copyright (C) 2019-2025 Dr Maxim Orlovsky.
// All rights under the above copyrights are reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

use alloc::collections::BTreeMap;
use core::borrow::Borrow;
use core::cell::RefCell;
#[cfg(feature = "async")]
use core::future::Future;
use std::collections::{HashMap, HashSet};
use std::io;
#[cfg(feature = "async")]
use std::time::{Duration, Instant};

use amplify::confinement::{KeyedCollection, SmallOrdMap};
use amplify::MultiError;
use commit_verify::StrictHash;
#[cfg(feature = "async")]
use futures_util::{stream, StreamExt, TryStreamExt};
use hypersonic::{
    AcceptError, AuthToken, CallParams, CellAddr, CodexId, ContractId, ContractName, Opid, Stock,
};
use indexmap::{IndexMap, IndexSet};
use rgb::RgbSeal;
#[cfg(feature = "async")]
use single_use_seals::PublishedWitness;
use strict_encoding::{
    ReadRaw, StrictDecode, StrictDumb, StrictEncode, StrictReader, StrictWriter, WriteRaw,
};
use strict_types::StrictVal;

use crate::{
    parse_consignment, Articles, Assignment, Consensus, Consignment, ConsumeError, Contract,
    ContractRef, ContractState, CreateParams, Identity, ImmutableState, Issuer, Operation,
    OwnedState, Pile, SigBlob, StateName, Stockpile, WitnessStatus,
};

#[cfg(feature = "async")]
const RGB_STD_SLOW_STAGE_THRESHOLD: Duration = Duration::from_millis(500);

#[cfg(feature = "async")]
fn slow_rgb_stage_elapsed(started_at: Instant) -> Option<u128> {
    let elapsed = started_at.elapsed();
    (elapsed >= RGB_STD_SLOW_STAGE_THRESHOLD).then_some(elapsed.as_millis())
}

#[cfg(feature = "async")]
fn witness_status_is_mature(
    status: WitnessStatus,
    last_block_height: u64,
    min_conformations: u32,
) -> bool {
    matches!(
        status,
        WitnessStatus::Mined(height)
            if last_block_height.saturating_sub(height.get()) > min_conformations as u64
    )
}

#[cfg(feature = "async")]
pub trait TxidResolver<Sp: Stockpile, E: core::error::Error> {
    async fn resolve(
        &self,
        witness_id: <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId,
    ) -> Result<WitnessStatus, E>;
}

pub const CONSIGN_VERSION: u16 = 0;
#[cfg(feature = "async")]
const RESOLVER_CONCURRENCY_LIMIT: usize = 16;
#[cfg(feature = "binfile")]
pub use _fs::CONSIGN_MAGIC_NUMBER;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Display)]
#[display("{contract_id}/{state_name}")]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(rename_all = "camelCase"))]
pub struct ContractStateName {
    pub contract_id: ContractId,
    pub state_name: StateName,
}

impl ContractStateName {
    pub fn new(contract_id: ContractId, state_name: StateName) -> Self {
        ContractStateName { contract_id, state_name }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(
        rename_all = "camelCase",
        bound = "Seal: serde::Serialize + for<'d> serde::Deserialize<'d>"
    )
)]
pub struct WalletState<Seal> {
    pub immutable: BTreeMap<ContractStateName, Vec<ImmutableState>>,
    pub owned: BTreeMap<ContractStateName, Vec<OwnedState<Seal>>>,
    pub aggregated: BTreeMap<ContractStateName, StrictVal>,
}

impl<Seal> Default for WalletState<Seal> {
    fn default() -> Self { Self { immutable: bmap! {}, owned: bmap! {}, aggregated: bmap! {} } }
}

impl<Seal> WalletState<Seal> {
    pub fn from_contracts_state(
        contracts: impl IntoIterator<Item = (ContractId, ContractState<Seal>)>,
    ) -> Self {
        let mut wallet_state = WalletState::default();
        for (contract_id, contract_state) in contracts {
            for (state_name, state) in contract_state.immutable {
                wallet_state
                    .immutable
                    .insert(ContractStateName::new(contract_id, state_name), state);
            }
            for (state_name, state) in contract_state.owned {
                wallet_state
                    .owned
                    .insert(ContractStateName::new(contract_id, state_name), state);
            }
            for (state_name, state) in contract_state.aggregated {
                wallet_state
                    .aggregated
                    .insert(ContractStateName::new(contract_id, state_name), state);
            }
        }
        wallet_state
    }
}

/// Collection of RGB smart contracts and contract issuers, which can be cached in memory.
///
/// # Generics
///
/// - `S` provides a specific cache implementation for an in-mem copy of issuers,
/// - `C` provides a specific cache implementation for an in-mem copy of contracts.
#[derive(Clone, Debug)]
pub struct Contracts<
    Sp,
    // TODO: Use IndexMap instead to be no_std-compatible
    S = HashMap<CodexId, Issuer>,
    C = HashMap<ContractId, Contract<<Sp as Stockpile>::Stock, <Sp as Stockpile>::Pile>>,
> where
    Sp: Stockpile,
    S: KeyedCollection<Key = CodexId, Value = Issuer>,
    C: KeyedCollection<Key = ContractId, Value = Contract<Sp::Stock, Sp::Pile>>,
{
    issuers: RefCell<S>,
    contracts: RefCell<C>,
    #[cfg(feature = "async")]
    witness_update_candidates: RefCell<
        HashMap<(ContractId, u32), IndexSet<<<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId>>,
    >,
    persistence: Sp,
}

impl<Sp, S, C> Contracts<Sp, S, C>
where
    Sp: Stockpile,
    S: KeyedCollection<Key = CodexId, Value = Issuer>,
    C: KeyedCollection<Key = ContractId, Value = Contract<Sp::Stock, Sp::Pile>>,
{
    pub fn load(persistence: Sp) -> Self
    where
        S: Default,
        C: Default,
    {
        Self {
            issuers: none!(),
            contracts: none!(),
            #[cfg(feature = "async")]
            witness_update_candidates: none!(),
            persistence,
        }
    }

    #[cfg(feature = "async")]
    pub fn witness_update_candidates(
        &self,
        contract_id: ContractId,
        min_conformations: u32,
    ) -> Option<Vec<<<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId>> {
        self.witness_update_candidates
            .borrow()
            .get(&(contract_id, min_conformations))
            .map(|candidates| candidates.iter().copied().collect())
    }

    #[cfg(feature = "async")]
    pub fn set_witness_update_candidates(
        &mut self,
        contract_id: ContractId,
        min_conformations: u32,
        candidates: impl IntoIterator<Item = <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId>,
    ) {
        self.witness_update_candidates
            .borrow_mut()
            .insert((contract_id, min_conformations), candidates.into_iter().collect());
    }

    #[allow(dead_code)]
    fn with_contract<R>(
        &self,
        id: ContractId,
        f: impl FnOnce(&Contract<Sp::Stock, Sp::Pile>) -> R,
        or: Option<R>,
    ) -> R {
        // We need this bullshit due to a failed rust `RefCell` implementation which panics if we do
        // this block any other way.
        if self.contracts.borrow().contains_key(&id) {
            return f(self.contracts.borrow().get(&id).unwrap());
        }
        if let Some(contract) = self.persistence.contract(id) {
            let res = f(&contract);
            self.contracts.borrow_mut().insert(id, contract);
            res
        } else if let Some(or) = or {
            or
        } else {
            panic!("Contract {id} not found")
        }
    }

    fn with_contract_mut<R>(
        &mut self,
        id: ContractId,
        f: impl FnOnce(&mut Contract<Sp::Stock, Sp::Pile>) -> R,
    ) -> R {
        // We need this bullshit due to a failed rust `RefCell` implementation which panics if we do
        // this block any other way.
        if self.contracts.borrow().contains_key(&id) {
            return f(self.contracts.borrow_mut().get_mut(&id).unwrap());
        }
        if let Some(mut contract) = self.persistence.contract(id) {
            let res = f(&mut contract);
            self.contracts.borrow_mut().insert(id, contract);
            res
        } else {
            panic!("Contract {id} not found")
        }
    }
}

impl<Sp, S, C> Contracts<Sp, S, C>
where
    Sp: Stockpile,
    S: KeyedCollection<Key = CodexId, Value = Issuer>,
    C: KeyedCollection<Key = ContractId, Value = Contract<Sp::Stock, Sp::Pile>>,
{
    pub fn codex_ids(&self) -> impl Iterator<Item = CodexId> + use<'_, Sp, S, C> {
        self.persistence.codex_ids()
    }

    pub fn issuers_count(&self) -> usize { self.persistence.issuers_count() }

    pub fn has_issuer(&self, codex_id: CodexId) -> bool { self.persistence.has_issuer(codex_id) }

    pub fn issuers(&self) -> impl Iterator<Item = (CodexId, Issuer)> + use<'_, Sp, S, C> {
        self.persistence
            .codex_ids()
            .filter_map(|codex_id| self.issuer(codex_id).map(|schema| (codex_id, schema)))
    }

    pub fn issuer(&self, codex_id: CodexId) -> Option<Issuer> {
        if let Some(issuer) = self.issuers.borrow().get(&codex_id) {
            return Some(issuer.clone());
        };
        let issuer = self.persistence.issuer(codex_id)?;
        self.issuers.borrow_mut().insert(codex_id, issuer.clone());
        Some(issuer)
    }

    pub fn contracts_count(&self) -> usize { self.persistence.contracts_count() }

    pub fn has_contract(&self, contract_id: ContractId) -> bool {
        self.persistence.has_contract(contract_id)
    }

    pub fn contract_ids(&self) -> impl Iterator<Item = ContractId> + use<'_, Sp, S, C> {
        self.persistence.contract_ids()
    }

    pub fn contract_witness_ids(
        &mut self,
        contract_id: ContractId,
    ) -> Vec<<<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId> {
        self.with_contract_mut(contract_id, |contract| contract.witness_ids())
    }

    /// Get the contract state.
    ///
    /// The call does not recompute the contract state, but does a seal resolution,
    /// taking into account the status of the witnesses in the whole history.
    ///
    /// # Panics
    ///
    /// If the contract id is not known.
    pub fn contract_state(
        &mut self,
        contract_id: ContractId,
    ) -> ContractState<<Sp::Pile as Pile>::Seal> {
        self.with_contract_mut(contract_id, |contract| contract.state())
            .into()
    }

    pub fn contract_owned_state_entries(
        &mut self,
        contract_id: ContractId,
        state_name: &StateName,
    ) -> Vec<(CellAddr, <Sp::Pile as Pile>::Seal, StrictVal)>
    where
        <Sp::Pile as Pile>::Seal: Clone,
    {
        self.with_contract_mut(contract_id, |contract| contract.owned_state_entries(state_name))
            .into()
    }

    pub fn contract_resolved_owned_state_entries(
        &mut self,
        contract_id: ContractId,
        state_name: &StateName,
    ) -> Vec<OwnedState<<Sp::Pile as Pile>::Seal>>
    where
        <Sp::Pile as Pile>::Seal: Clone,
    {
        self.with_contract_mut(contract_id, |contract| {
            contract.resolved_owned_state_entries(state_name)
        })
        .into()
    }

    pub fn contract_resolved_owned_assignments(
        &mut self,
        contract_id: ContractId,
        state_name: &StateName,
    ) -> Vec<(CellAddr, Assignment<<Sp::Pile as Pile>::Seal>)>
    where
        <Sp::Pile as Pile>::Seal: Clone,
    {
        self.with_contract_mut(contract_id, |contract| {
            contract.resolved_owned_assignments(state_name)
        })
        .into()
    }

    pub fn contract_articles(&mut self, contract_id: ContractId) -> Articles {
        self.with_contract_mut(contract_id, |contract| contract.articles().clone())
            .into()
    }

    pub fn find_contract_id(&self, r: impl Into<ContractRef>) -> Option<ContractId> {
        match r.into() {
            ContractRef::Id(id) if self.has_contract(id) => Some(id),
            ContractRef::Id(_) => None,
            ContractRef::Name(name) => {
                let name = ContractName::Named(name);
                if let Some(id) = self
                    .contracts
                    .borrow()
                    .iter()
                    .find(|(_, contract)| contract.articles().issue().meta.name == name)
                    .map(|(id, _)| *id)
                {
                    return Some(id);
                }
                self.persistence
                    .contract_ids()
                    .filter_map(|id| self.persistence.contract(id))
                    .find(|contract| contract.articles().issue().meta.name == name)
                    .map(|contract| contract.contract_id())
            }
        }
    }

    pub fn import_issuer(&mut self, issuer: Issuer) -> Result<CodexId, Sp::Error> {
        let codex_id = issuer.codex_id();
        let schema = self.persistence.import_issuer(issuer)?;
        self.issuers.borrow_mut().insert(codex_id, schema);
        Ok(codex_id)
    }

    fn check_layer1(
        &self,
        consensus: Consensus,
        testnet: bool,
    ) -> Result<(), MultiError<IssuerError, <Sp::Stock as Stock>::Error, <Sp::Pile as Pile>::Error>>
    {
        if consensus != self.persistence.consensus() {
            return Err(MultiError::A(IssuerError::ConsensusMismatch));
        }
        if testnet != self.persistence.is_testnet() {
            Err(if testnet {
                MultiError::A(IssuerError::TestnetMismatch)
            } else {
                MultiError::A(IssuerError::MainnetMismatch)
            })
        } else {
            Ok(())
        }
    }

    pub fn issue(
        &mut self,
        params: CreateParams<<<Sp::Pile as Pile>::Seal as RgbSeal>::Definition>,
    ) -> Result<
        ContractId,
        MultiError<IssuerError, <Sp::Stock as Stock>::Error, <Sp::Pile as Pile>::Error>,
    > {
        self.check_layer1(params.consensus, params.testnet)?;
        let contract = self.persistence.issue(params)?;
        let id = contract.contract_id();
        self.contracts.borrow_mut().insert(id, contract);
        Ok(id)
    }

    /// Do a call to the contract method, creating and operation.
    ///
    /// The operation is automatically included in the contract history.
    ///
    /// The state of the contract is not automatically updated, but on the next update it will
    /// reflect the call results.
    ///
    /// # Panics
    ///
    /// If the contract id is not known.
    pub fn contract_call(
        &mut self,
        contract_id: ContractId,
        call: CallParams,
        seals: SmallOrdMap<u16, <<Sp::Pile as Pile>::Seal as RgbSeal>::Definition>,
    ) -> Result<Operation, MultiError<AcceptError, <Sp::Stock as Stock>::Error>> {
        self.with_contract_mut(contract_id, |contract| contract.call(call, seals))
    }

    #[cfg(not(feature = "async"))]
    /// Update the status of all witnesses and single-use seal definitions.
    ///
    /// Applies rollbacks or forwards if required and recomputes the state of the affected
    /// contracts.
    pub fn update_witnesses<E: core::error::Error>(
        &mut self,
        resolver: impl Fn(<<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId) -> Result<WitnessStatus, E>,
        last_block_height: u64,
        min_conformations: u32,
    ) -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
        let mut changed_statuses = IndexMap::<_, WitnessStatus>::new();
        let contract_ids = self.persistence.contract_ids().collect::<IndexSet<_>>();
        for contract_id in contract_ids {
            self.with_contract_mut(
                contract_id,
                |contract| -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
                    for witness_id in contract.witness_ids() {
                        let old_status = contract.witness_status(witness_id);
                        if matches!(old_status, WitnessStatus::Mined(height) if last_block_height - height.get() > min_conformations as u64) {
                            continue;
                        }
                        let new_status = match changed_statuses.get(&witness_id) {
                            None => resolver(witness_id)
                                .map_err(SyncError::Status)
                                .map_err(MultiError::A),
                            Some(witness_id) => Ok(*witness_id),
                        }?;
                        if new_status != old_status {
                            changed_statuses.insert(witness_id, new_status);
                        }
                    }
                    contract
                        .sync(changed_statuses.iter().map(|(id, status)| (*id, *status)))
                        .map_err(MultiError::from_other_a)?;
                    Ok(())
                },
            )?;
        }
        Ok(())
    }

    #[cfg(feature = "async")]
    /// Update the status of all witnesses and single-use seal definitions.
    ///
    /// Applies rollbacks or forwards if required and recomputes the state of the affected
    /// contracts.
    pub async fn update_witnesses_async<E: core::error::Error>(
        &mut self,
        resolver: impl AsyncFn(
            <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId,
        ) -> Result<WitnessStatus, E>,
        last_block_height: u64,
        min_conformations: u32,
    ) -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
        let mut resolved_statuses = IndexMap::<_, WitnessStatus>::new();
        let contract_ids = self.persistence.contract_ids().collect::<IndexSet<_>>();
        for contract_id in contract_ids {
            let witnesses = self.with_contract_mut(contract_id, |contract| {
                let ids = contract.witness_ids();
                ids.into_iter()
                    .map(|wid| {
                        let status = contract.witness_status(wid);
                        (wid, status)
                    })
                    .collect::<Vec<_>>()
            });

            let mut changed_statuses = IndexMap::<_, WitnessStatus>::new();
            for (witness_id, old_status) in witnesses {
                if matches!(old_status, WitnessStatus::Mined(height) if last_block_height - height.get() > min_conformations as u64)
                {
                    continue;
                }
                let new_status = match resolved_statuses.get(&witness_id) {
                    Some(status) => *status,
                    None => {
                        let status = resolver(witness_id)
                            .await
                            .map_err(SyncError::Status)
                            .map_err(MultiError::A)?;
                        resolved_statuses.insert(witness_id, status);
                        status
                    }
                };
                if new_status != old_status {
                    changed_statuses.insert(witness_id, new_status);
                }
            }

            self.with_contract_mut(
                contract_id,
                |contract| -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
                    contract
                        .sync(changed_statuses.iter().map(|(id, status)| (*id, *status)))
                        .map_err(MultiError::from_other_a)?;
                    Ok(())
                },
            )?;
        }
        Ok(())
    }

    #[cfg(feature = "async")]
    /// Update the status of all witnesses and single-use seal definitions.
    ///
    /// Applies rollbacks or forwards if required and recomputes the state of the affected
    /// contracts.
    pub async fn update_contract_witnesses_async<E: core::error::Error>(
        &mut self,
        contract_id: Option<ContractId>,
        resolver: impl TxidResolver<Sp, E>,
        last_block_height: u64,
        min_conformations: u32,
    ) -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
        let mut resolved_statuses = IndexMap::<_, WitnessStatus>::new();
        let contract_ids = match contract_id {
            Some(contract_id) => {
                if !self.has_contract(contract_id) {
                    return Err(MultiError::A(SyncError::ContractNotFound(contract_id)));
                }
                IndexSet::from([contract_id])
            }
            _ => self.contract_ids().collect::<IndexSet<_>>(),
        };

        for contract_id in contract_ids {
            let witnesses = self.with_contract_mut(contract_id, |contract| {
                let ids = contract.witness_ids();
                ids.into_iter()
                    .map(|wid| {
                        let status = contract.witness_status(wid);
                        (wid, status)
                    })
                    .collect::<Vec<_>>()
            });

            let mut changed_statuses = IndexMap::<_, WitnessStatus>::new();
            for (witness_id, old_status) in witnesses {
                if matches!(old_status, WitnessStatus::Mined(height) if last_block_height - height.get() > min_conformations as u64)
                {
                    continue;
                }
                let new_status = match resolved_statuses.get(&witness_id) {
                    Some(status) => *status,
                    None => {
                        let status = resolver
                            .resolve(witness_id)
                            .await
                            .map_err(SyncError::Status)
                            .map_err(MultiError::A)?;
                        resolved_statuses.insert(witness_id, status);
                        status
                    }
                };
                if new_status != old_status {
                    changed_statuses.insert(witness_id, new_status);
                }
            }

            self.with_contract_mut(
                contract_id,
                |contract| -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
                    contract
                        .sync(changed_statuses.iter().map(|(id, status)| (*id, *status)))
                        .map_err(MultiError::from_other_a)?;
                    Ok(())
                },
            )?;
        }

        Ok(())
    }

    #[cfg(feature = "async")]
    /// Concurrent + Send-friendly witness update helper.
    pub async fn update_contract_witnesses_async_send<E, R, Fut>(
        &mut self,
        contract_id: Option<ContractId>,
        resolver: R,
        last_block_height: u64,
        min_conformations: u32,
    ) -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>>
    where
        E: core::error::Error,
        R: Fn(<<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId) -> Fut + Sync,
        Fut: Future<Output = Result<WitnessStatus, E>> + Send,
    {
        let total_started_at = Instant::now();
        let mut resolved_statuses = IndexMap::<_, WitnessStatus>::new();
        let contract_ids = match contract_id {
            Some(contract_id) => {
                if !self.has_contract(contract_id) {
                    return Err(MultiError::A(SyncError::ContractNotFound(contract_id)));
                }
                IndexSet::from([contract_id])
            }
            _ => self.contract_ids().collect::<IndexSet<_>>(),
        };
        let contract_count = contract_ids.len();

        let mut witness_ids = IndexSet::new();
        let mut contract_witnesses = IndexMap::new();
        let mut next_candidates = IndexMap::new();
        let collect_started_at = Instant::now();
        let mut scanned_witnesses = 0usize;
        let mut skipped_mature_mined = 0usize;
        let mut cache_hits = 0usize;
        let mut cache_misses = 0usize;
        for contract_id in contract_ids.iter().copied() {
            let cached_candidates = self
                .witness_update_candidates
                .borrow()
                .get(&(contract_id, min_conformations))
                .cloned();

            let candidates = self.with_contract_mut(contract_id, |contract| {
                if let Some(candidates) = cached_candidates {
                    cache_hits += 1;
                    candidates.into_iter().collect::<Vec<_>>()
                } else {
                    cache_misses += 1;
                    contract.witness_ids()
                }
            });

            self.with_contract_mut(contract_id, |contract| {
                let mut pending_witnesses = Vec::with_capacity(candidates.len());
                for witness_id in candidates {
                    scanned_witnesses += 1;
                    let old_status = contract.witness_status(witness_id);
                    if witness_status_is_mature(old_status, last_block_height, min_conformations) {
                        skipped_mature_mined += 1;
                        continue;
                    }
                    witness_ids.insert(witness_id);
                    pending_witnesses.push((witness_id, old_status));
                }
                contract_witnesses.insert(contract_id, pending_witnesses);
            });
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(collect_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "update_witnesses_collect",
                elapsed_ms,
                requested_contract = ?contract_id,
                contract_count,
                scanned_witnesses,
                unique_witnesses = witness_ids.len(),
                skipped_mature_mined,
                cache_hits,
                cache_misses,
                last_block_height,
                min_conformations,
                "Slow rgb-std stage"
            );
        }

        let resolver = &resolver;
        let resolve_started_at = Instant::now();
        let unique_witnesses = witness_ids.len();
        let resolved = stream::iter(witness_ids.into_iter().map(|witness_id| {
            let resolver = resolver;
            async move {
                let status = resolver(witness_id)
                    .await
                    .map_err(SyncError::Status)
                    .map_err(MultiError::A)?;
                Ok::<_, MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>>((witness_id, status))
            }
        }))
        .buffer_unordered(RESOLVER_CONCURRENCY_LIMIT)
        .try_collect::<Vec<_>>()
        .await?;
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(resolve_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "update_witnesses_resolve",
                elapsed_ms,
                requested_contract = ?contract_id,
                contract_count,
                unique_witnesses,
                resolved = resolved.len(),
                resolver_concurrency = RESOLVER_CONCURRENCY_LIMIT,
                "Slow rgb-std stage"
            );
        }

        resolved_statuses.extend(resolved);

        let sync_started_at = Instant::now();
        let mut sync_scanned_witnesses = 0usize;
        let mut changed_statuses_total = 0usize;
        let mut synced_contracts = 0usize;
        for contract_id in contract_ids {
            let witnesses = contract_witnesses
                .shift_remove(&contract_id)
                .unwrap_or_default();
            let mut next_contract_candidates = IndexSet::new();
            self.with_contract_mut(
                contract_id,
                |contract| -> Result<(), MultiError<SyncError<E>, <Sp::Stock as Stock>::Error>> {
                    let mut changed_statuses = IndexMap::<_, WitnessStatus>::new();
                    for (witness_id, old_status) in witnesses {
                        sync_scanned_witnesses += 1;
                        let new_status = resolved_statuses
                            .get(&witness_id)
                            .copied()
                            .unwrap_or(old_status);
                        if !witness_status_is_mature(
                            new_status,
                            last_block_height,
                            min_conformations,
                        ) {
                            next_contract_candidates.insert(witness_id);
                        }
                        if new_status != old_status {
                            changed_statuses.insert(witness_id, new_status);
                        }
                    }
                    changed_statuses_total += changed_statuses.len();
                    if !changed_statuses.is_empty() {
                        synced_contracts += 1;
                        contract
                            .sync(changed_statuses.iter().map(|(id, status)| (*id, *status)))
                            .map_err(MultiError::from_other_a)?;
                    }
                    Ok(())
                },
            )?;
            next_candidates.insert((contract_id, min_conformations), next_contract_candidates);
        }
        {
            let mut witness_update_candidates = self.witness_update_candidates.borrow_mut();
            for (key, candidates) in next_candidates {
                witness_update_candidates.insert(key, candidates);
            }
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(sync_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "update_witnesses_sync",
                elapsed_ms,
                requested_contract = ?contract_id,
                contract_count,
                sync_scanned_witnesses,
                changed_statuses_total,
                synced_contracts,
                cache_hits,
                cache_misses,
                "Slow rgb-std stage"
            );
        }

        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(total_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "update_witnesses_total",
                elapsed_ms,
                requested_contract = ?contract_id,
                contract_count,
                scanned_witnesses,
                unique_witnesses,
                changed_statuses_total,
                synced_contracts,
                cache_hits,
                cache_misses,
                "Slow rgb-std stage"
            );
        }

        Ok(())
    }

    /// Include an operation and its witness to the history of known operations and the contract
    /// state.
    ///
    /// # Panics
    ///
    /// If the contract id is not known.
    pub fn include(
        &mut self,
        contract_id: ContractId,
        opid: Opid,
        pub_witness: &<<Sp::Pile as Pile>::Seal as RgbSeal>::Published,
        anchor: <<Sp::Pile as Pile>::Seal as RgbSeal>::Client,
    ) {
        self.include_uncommitted(contract_id, opid, pub_witness, anchor);
        self.commit_contract_pile(contract_id);
    }

    pub(crate) fn include_uncommitted(
        &mut self,
        contract_id: ContractId,
        opid: Opid,
        pub_witness: &<<Sp::Pile as Pile>::Seal as RgbSeal>::Published,
        anchor: <<Sp::Pile as Pile>::Seal as RgbSeal>::Client,
    ) {
        #[cfg(feature = "async")]
        {
            let witness_id = pub_witness.pub_id();
            for ((cached_contract_id, _), candidates) in
                self.witness_update_candidates.borrow_mut().iter_mut()
            {
                if *cached_contract_id == contract_id {
                    candidates.insert(witness_id);
                }
            }
        }
        self.with_contract_mut(contract_id, |contract| contract.include(opid, anchor, pub_witness))
    }

    pub(crate) fn commit_contract_pile(&mut self, contract_id: ContractId) {
        self.with_contract_mut(contract_id, Contract::commit_pile_transaction)
    }

    /// Export a contract to a strictly encoded stream.
    ///
    /// # Panics
    ///
    /// If the contract id is not known.
    ///
    /// # Errors
    ///
    /// If the output stream failures, like when the stream cannot accept more data or got
    /// disconnected.
    pub fn export(
        &mut self,
        contract_id: ContractId,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        self.with_contract_mut(contract_id, |contract| contract.export(writer))
            .into()
    }

    /// Purge a contract from the system.
    pub fn purge(&mut self, contract_id: ContractId) -> Result<(), Sp::Error> {
        self.contracts.borrow_mut().remove(&contract_id);
        self.persistence.purge(contract_id)?;
        Ok(())
    }

    /// Create a consignment with a history from the genesis to each of the `terminals`, and
    /// serialize it to a strictly encoded stream `writer`.
    ///
    /// # Panics
    ///
    /// If the contract id is not known.
    ///
    /// # Errors
    ///
    /// If the output stream failures, like when the stream cannot accept more data or got
    /// disconnected.
    pub fn consign(
        &mut self,
        contract_id: ContractId,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        self.with_contract_mut(contract_id, |contract| contract.consign(terminals, writer))
    }

    pub fn consign_by_addrs(
        &mut self,
        contract_id: ContractId,
        terminals: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        self.with_contract_mut(contract_id, |contract| {
            let addresses = terminals
                .into_iter()
                .map(|addr| *addr.borrow())
                .collect::<HashSet<_>>();
            let auths = contract
                .full_state()
                .raw
                .auth
                .iter()
                .filter(|(_, addr)| addresses.contains(addr))
                .map(|(auth, _)| *auth)
                .collect::<Vec<_>>();
            contract.consign(auths, writer)
        })
    }

    pub fn resolve_addrs(
        &self,
        contract_id: ContractId,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
    ) -> HashSet<CellAddr> {
        self.with_contract(
            contract_id,
            |contract| {
                terminals
                    .into_iter()
                    .filter_map(|auth| contract.full_state().raw.auth.get(auth.borrow()).copied())
                    .collect()
            },
            Some(HashSet::new()),
        )
    }

    pub fn resolved_owned_state_entries_filtered(
        &mut self,
        contract_id: ContractId,
        name: &StateName,
        predicate: impl FnMut(&<Sp::Pile as Pile>::Seal) -> bool,
    ) -> Vec<OwnedState<<Sp::Pile as Pile>::Seal>>
    where
        <Sp::Pile as Pile>::Seal: Clone,
    {
        self.with_contract_mut(contract_id, |contract| {
            contract.resolved_owned_state_entries_filtered(name, predicate)
        })
    }

    /// Consume a consignment stream.
    ///
    /// The method:
    /// - validates the consignment;
    /// - resolves auth tokens into seal definitions known to the current wallet (i.e., coming from
    ///   the invoices produced by the wallet);
    /// - checks the signature of the issuer over the contract articles;
    ///
    /// # Arguments
    ///
    /// - `allow_unknown`: allows importing a contract which was not known to the system;
    /// - `reader`: the input stream;
    /// - `seal_resolver`: lambda which knows about the seal definitions from the wallet-generated
    ///   invoices;
    /// - `sig_validator`: a validator for the signature of the issuer over the contract articles.
    pub fn consume<E>(
        &mut self,
        allow_unknown: bool,
        reader: &mut StrictReader<impl ReadRaw>,
        seal_resolver: impl FnMut(
            &Operation,
        )
            -> BTreeMap<u16, <<Sp::Pile as Pile>::Seal as RgbSeal>::Definition>,
        sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
    ) -> Result<
        (),
        MultiError<
            ConsumeError<<<Sp::Pile as Pile>::Seal as RgbSeal>::Definition>,
            <Sp::Stock as Stock>::Error,
            <Sp::Pile as Pile>::Error,
        >,
    >
    where
        <Sp::Pile as Pile>::Conf: From<<Sp::Stock as Stock>::Conf>,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDecode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDecode,
        <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictDecode,
    {
        // Checking version and getting contract id
        let contract_id = parse_consignment(reader).map_err(MultiError::from_a)?;
        if !self.has_contract(contract_id) {
            if allow_unknown {
                let consignment = Consignment::strict_decode(reader).map_err(MultiError::from_a)?;
                // Here we do not check for the end of the stream,
                // so in the future we can have arbitrary extensions
                // put here with no backward compatibility issues.

                let articles = consignment
                    .articles(sig_validator)
                    .map_err(MultiError::from_a)?;
                self.check_layer1(
                    articles.contract_meta().consensus,
                    articles.contract_meta().testnet,
                )
                .map_err(MultiError::from_other_a)?;

                let contract = self.persistence.import_contract(articles, consignment)?;
                self.contracts.borrow_mut().insert(contract_id, contract);
                #[cfg(feature = "async")]
                {
                    self.witness_update_candidates
                        .borrow_mut()
                        .retain(|(cached_contract_id, _), _| *cached_contract_id != contract_id);
                }
                Ok(())
            } else {
                Err(MultiError::A(ConsumeError::UnknownContract(contract_id)))
            }
        } else {
            let result = self.with_contract_mut(contract_id, |contract| {
                contract.consume_internal(reader, seal_resolver, sig_validator)
            });
            if result.is_ok() {
                #[cfg(feature = "async")]
                {
                    self.witness_update_candidates
                        .borrow_mut()
                        .retain(|(cached_contract_id, _), _| *cached_contract_id != contract_id);
                }
            }
            result.map_err(|err| match err {
                MultiError::A(a) => MultiError::A(a),
                MultiError::B(b) => MultiError::B(b),
                MultiError::C(_) => unreachable!(),
            })
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Display, Error, From)]
#[display(doc_comments)]
pub enum IssuerError {
    /// the issuer version does not match the required one.
    IssuerMismatch,
    /// proof of publication layer mismatch.
    ConsensusMismatch,
    /// unable to consume a testnet contract for mainnet.
    TestnetMismatch,
    /// unable to consume a mainnet contract for testnet.
    MainnetMismatch,
    /// unknown codex for contract issue {0}.
    UnknownCodex(CodexId),

    #[from]
    #[display(inner)]
    Inner(hypersonic::IssueError),
}

#[cfg(feature = "binfile")]
mod _fs {
    use std::path::Path;

    use binfile::BinFile;
    use strict_encoding::StreamReader;

    use super::*;

    pub const CONSIGN_MAGIC_NUMBER: u64 = u64::from_be_bytes(*b"RGBCNSGN");

    impl<Sp, S, C> Contracts<Sp, S, C>
    where
        Sp: Stockpile,
        S: KeyedCollection<Key = CodexId, Value = Issuer>,
        C: KeyedCollection<Key = ContractId, Value = Contract<Sp::Stock, Sp::Pile>>,
    {
        /// Export a contract to a file at `path`.
        ///
        /// # Panics
        ///
        /// If the contract id is not known.
        ///
        /// # Errors
        ///
        /// If writing to the file failures, like when the file already exists, there is no write
        /// access to it, or no sufficient disk space.
        pub fn export_to_file(
            &mut self,
            path: impl AsRef<Path>,
            contract_id: ContractId,
        ) -> io::Result<()>
        where
            <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictEncode,
        {
            self.with_contract_mut(contract_id, |contract| contract.export_to_file(path))
                .into()
        }

        /// Create a consignment with a history from the genesis to each of the `terminals`, and
        /// serialize it to a `file`.
        ///
        /// # Panics
        ///
        /// If the contract id is not known.
        ///
        /// # Errors
        ///
        /// If writing to the file failures, like when the file already exists, there is no write
        /// access to it, or no sufficient disk space.
        pub fn consign_to_file(
            &mut self,
            path: impl AsRef<Path>,
            contract_id: ContractId,
            terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        ) -> io::Result<()>
        where
            <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictEncode,
        {
            self.with_contract_mut(contract_id, |contract| {
                contract.consign_to_file(path, terminals)
            })
            .into()
        }

        /// Consume a consignment from a `file`.
        ///
        /// The method:
        /// - validates the consignment;
        /// - resolves auth tokens into seal definitions known to the current wallet (i.e., coming
        ///   from the invoices produced by the wallet);
        /// - checks the signature of the issuer over the contract articles;
        ///
        /// # Arguments
        ///
        /// - `allow_unknown`: allows importing a contract which was not known to the system;
        /// - `reader`: the input stream;
        /// - `seal_resolver`: lambda which knows about the seal definitions from the
        ///   wallet-generated invoices;
        /// - `sig_validator`: a validator for the signature of the issuer over the contract
        ///   articles.
        pub fn consume_from_file<E>(
            &mut self,
            allow_unknown: bool,
            path: impl AsRef<Path>,
            seal_resolver: impl FnMut(
                &Operation,
            ) -> BTreeMap<
                u16,
                <<Sp::Pile as Pile>::Seal as RgbSeal>::Definition,
            >,
            sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
        ) -> Result<
            (),
            MultiError<
                ConsumeError<<<Sp::Pile as Pile>::Seal as RgbSeal>::Definition>,
                <Sp::Stock as Stock>::Error,
                <Sp::Pile as Pile>::Error,
            >,
        >
        where
            <Sp::Pile as Pile>::Conf: From<<Sp::Stock as Stock>::Conf>,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::Client: StrictDecode,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::Published: StrictDecode,
            <<Sp::Pile as Pile>::Seal as RgbSeal>::WitnessId: StrictDecode,
        {
            let file = BinFile::<CONSIGN_MAGIC_NUMBER, CONSIGN_VERSION>::open(path)
                .map_err(MultiError::from_a)?;
            let mut reader = StrictReader::with(StreamReader::new::<{ usize::MAX }>(file));
            self.consume(allow_unknown, &mut reader, seal_resolver, sig_validator)
        }
    }
}

#[derive(Debug, Display, Error, From)]
#[display(doc_comments)]
pub enum SyncError<E: core::error::Error> {
    ContractNotFound(ContractId),
    /// unable to synchronize wallet. Details: {0}
    Wallet(E),

    /// unable to retrieve the status of a witness id. Details: {0}
    Status(E),

    #[from]
    #[display(inner)]
    Forward(AcceptError),
}
