// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0

use alloc::collections::BTreeMap;
use core::borrow::Borrow;
use core::error::Error;
use core::marker::PhantomData;
use std::collections::{HashMap, HashSet};
use std::io;
use std::time::{Duration, Instant};

use amplify::confinement::SmallOrdMap;
use amplify::{IoError, MultiError};
use chrono::{DateTime, Utc};
use commit_verify::{ReservedBytes, StrictHash};
use hypersonic::{
    AcceptError, Articles, AuthToken, CallParams, CellAddr, Codex, Consensus, ContractId,
    CoreParams, DataCell, EffectiveState, IssueError, IssueParams, Ledger, LibRepo, Memory,
    MethodName, NamedState, Operation, Opid, SemanticError, Semantics, SigBlob, StateAtom,
    StateName, Stock, StockSession, Transition,
};
use indexmap::{IndexMap, IndexSet};
use rgb::{
    ContractApi, ContractVerify, OperationSeals, ReadOperation, RgbSeal, RgbSealDef,
    VerificationError,
};
use single_use_seals::{ClientSideWitness, PublishedWitness, SealWitness};
use strict_encoding::{
    DecodeError, ReadRaw, StreamWriter, StrictDecode, StrictDumb, StrictEncode, StrictReader,
    StrictWriter, TypeName, TypedRead, TypedWrite, WriteRaw,
};
use strict_types::StrictVal;

use crate::{
    parse_consignment, Consignment, ContractMeta, Identity, Issue, Issuer, IssuerError, IssuerSpec,
    OpRels, Pile, PileSession, VerifiedOperation, Witness, WitnessStatus,
};

const RGB_STD_SLOW_STAGE_THRESHOLD: Duration = Duration::from_millis(500);

fn slow_rgb_stage_elapsed(started_at: Instant) -> Option<u128> {
    let elapsed = started_at.elapsed();
    (elapsed >= RGB_STD_SLOW_STAGE_THRESHOLD).then_some(elapsed.as_millis())
}
#[derive(Copy, Clone, PartialEq, Eq, Debug, From)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(untagged, bound = "Seal: serde::Serialize + for<'d> serde::Deserialize<'d>")
)]
pub enum EitherSeal<Seal> {
    Alt(Seal),
    #[from]
    Token(AuthToken),
}

impl<Seal> EitherSeal<Seal> {
    pub fn auth_token(&self) -> AuthToken
    where Seal: RgbSealDef {
        match self {
            EitherSeal::Alt(seal) => seal.auth_token(),
            EitherSeal::Token(auth) => *auth,
        }
    }
    pub fn to_explicit(&self) -> Option<Seal>
    where Seal: Clone {
        match self {
            EitherSeal::Alt(seal) => Some(seal.clone()),
            EitherSeal::Token(_) => None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound = "Seal: serde::Serialize + for<'d> serde::Deserialize<'d>")
)]
pub struct Assignment<Seal> {
    pub seal: Seal,
    pub data: StrictVal,
}
impl<Seal> Assignment<Seal> {
    pub fn new(seal: Seal, data: impl Into<StrictVal>) -> Self { Self { seal, data: data.into() } }
}
impl<Seal> Assignment<EitherSeal<Seal>> {
    pub fn new_external(auth: AuthToken, data: impl Into<StrictVal>) -> Self {
        Self { seal: EitherSeal::Token(auth), data: data.into() }
    }
    pub fn new_internal(seal: Seal, data: impl Into<StrictVal>) -> Self {
        Self { seal: EitherSeal::Alt(seal), data: data.into() }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(bound = "Seal: serde::Serialize + for<'d> serde::Deserialize<'d>")
)]
pub struct OwnedState<Seal> {
    pub addr: CellAddr,
    #[cfg_attr(feature = "serde", serde(flatten))]
    pub assignment: Assignment<Seal>,
    pub status: WitnessStatus,
}

type ResolvedOwnedEntry<Seal> = (CellAddr, Assignment<Seal>);

#[derive(Clone, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ImmutableState {
    pub addr: CellAddr,
    #[cfg_attr(feature = "serde", serde(flatten))]
    pub data: StateAtom,
    pub status: WitnessStatus,
}

#[derive(Clone, Eq, PartialEq, Debug, Default)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(
        rename_all = "camelCase",
        bound = "Seal: serde::Serialize + for<'d> serde::Deserialize<'d>"
    )
)]
pub struct ContractState<Seal> {
    pub immutable: BTreeMap<StateName, Vec<ImmutableState>>,
    pub owned: BTreeMap<StateName, Vec<OwnedState<Seal>>>,
    pub aggregated: BTreeMap<StateName, StrictVal>,
}

impl<Seal> ContractState<Seal> {
    pub fn map<To>(self, f: impl Fn(Seal) -> To) -> ContractState<To> {
        ContractState {
            immutable: self.immutable,
            owned: self
                .owned
                .into_iter()
                .map(|(name, v)| {
                    (
                        name,
                        v.into_iter()
                            .map(|o| OwnedState {
                                addr: o.addr,
                                assignment: Assignment {
                                    seal: f(o.assignment.seal),
                                    data: o.assignment.data,
                                },
                                status: o.status,
                            })
                            .collect(),
                    )
                })
                .collect(),
            aggregated: self.aggregated,
        }
    }

    pub fn filter_map<To>(self, f: impl Fn(Seal) -> Option<To>) -> ContractState<To> {
        ContractState {
            immutable: self.immutable,
            owned: self
                .owned
                .into_iter()
                .map(|(name, v)| {
                    (
                        name,
                        v.into_iter()
                            .filter_map(|o| {
                                Some(OwnedState {
                                    addr: o.addr,
                                    assignment: Assignment {
                                        seal: f(o.assignment.seal)?,
                                        data: o.assignment.data,
                                    },
                                    status: o.status,
                                })
                            })
                            .collect(),
                    )
                })
                .collect(),
            aggregated: self.aggregated,
        }
    }
}

#[derive(Clone, Debug)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(
        rename_all = "camelCase",
        bound = "Seal: serde::Serialize + for<'d> serde::Deserialize<'d>"
    )
)]
pub struct CreateParams<Seal: Clone> {
    pub issuer: IssuerSpec,
    pub consensus: Consensus,
    pub testnet: bool,
    pub method: MethodName,
    pub name: TypeName,
    pub timestamp: Option<DateTime<Utc>>,
    pub global: Vec<NamedState<StateAtom>>,
    pub owned: Vec<NamedState<Assignment<EitherSeal<Seal>>>>,
}

impl<Seal: Clone> CreateParams<Seal> {
    pub fn new_testnet(
        issuer: impl Into<IssuerSpec>,
        consensus: Consensus,
        name: impl Into<TypeName>,
    ) -> Self {
        Self {
            issuer: issuer.into(),
            consensus,
            testnet: true,
            method: vname!("issue"),
            name: name.into(),
            timestamp: None,
            global: none![],
            owned: none![],
        }
    }
    pub fn with_global_verified(
        mut self,
        name: impl Into<StateName>,
        data: impl Into<StrictVal>,
    ) -> Self {
        self.global
            .push(NamedState { name: name.into(), state: StateAtom::new_verified(data) });
        self
    }
    pub fn push_owned_unlocked(
        &mut self,
        name: impl Into<StateName>,
        assignment: Assignment<EitherSeal<Seal>>,
    ) {
        self.owned
            .push(NamedState { name: name.into(), state: assignment });
    }
}

#[derive(Clone, Debug)]
pub struct Contract<S: Stock, P: Pile> {
    contract_id: ContractId,
    ledger: Ledger<S>,
    pile: P,
    /// In-memory cache of valid opids for `ContractApi::is_known(&self)` which requires &self.
    valid_cache: HashSet<Opid>,
    aux_cache: HashMap<Opid, Vec<u8>>,
}

impl<S: Stock, P: Pile> Contract<S, P> {
    fn refresh_valid_cache(&mut self) {
        let genesis_opid = self.ledger.articles().genesis_opid();
        let valid_cache = self
            .ledger
            .with_session(|session| {
                let mut valid = HashSet::new();
                if session.is_valid(genesis_opid) {
                    valid.insert(genesis_opid);
                }
                let opids = session
                    .operations()
                    .map(|(opid, _)| opid)
                    .collect::<Vec<_>>();
                for opid in opids {
                    if session.is_valid(opid) {
                        valid.insert(opid);
                    }
                }
                Ok::<_, core::convert::Infallible>(valid)
            })
            .expect("infallible valid cache refresh");
        self.valid_cache = valid_cache;
    }

    pub fn with(
        articles: Articles,
        consignment: Consignment<P::Seal>,
        conf: S::Conf,
    ) -> Result<Self, MultiError<ConsumeError<<P::Seal as RgbSeal>::Definition>, S::Error, P::Error>>
    where
        P::Conf: From<S::Conf>,
        <P::Seal as RgbSeal>::Client: StrictDecode,
        <P::Seal as RgbSeal>::Published: StrictDecode,
        <P::Seal as RgbSeal>::WitnessId: StrictDecode,
    {
        let contract_id = articles.contract_id();
        let genesis_opid = articles.genesis_opid();
        let ledger = Ledger::new(articles, conf)
            .map_err(MultiError::with_third)
            .map_err(MultiError::from_other_a)?;
        let conf: S::Conf = ledger.config();
        let mut pile = P::new(conf.into()).map_err(MultiError::C)?;
        pile.session().add_seals(genesis_opid, none!());
        let mut contract = Self {
            ledger,
            pile,
            contract_id,
            valid_cache: HashSet::from([genesis_opid]),
            aux_cache: HashMap::new(),
        };
        contract
            .evaluate_commit(consignment.into_operations())
            .map_err(MultiError::from_a)?;
        Ok(contract)
    }

    pub fn issue(
        issuer: Issuer,
        params: CreateParams<<P::Seal as RgbSeal>::Definition>,
        conf: impl FnOnce(&Articles) -> Result<S::Conf, S::Error>,
    ) -> Result<Self, MultiError<IssuerError, S::Error, P::Error>>
    where
        P::Conf: From<S::Conf>,
    {
        if !params.issuer.check(issuer.issuer_id()) {
            return Err(MultiError::A(IssuerError::IssuerMismatch));
        }
        let seals =
            SmallOrdMap::try_from_iter(
                params.owned.iter().enumerate().filter_map(|(pos, a)| {
                    a.state.seal.to_explicit().map(|seal| (pos as u16, seal))
                }),
            )
            .expect("too many outputs");
        let params = IssueParams {
            issuer: params.issuer,
            name: params.name,
            consensus: params.consensus,
            testnet: params.testnet,
            timestamp: params.timestamp,
            core: CoreParams {
                method: params.method,
                global: params.global,
                owned: params
                    .owned
                    .into_iter()
                    .map(|a| NamedState {
                        name: a.name,
                        state: DataCell {
                            auth: a.state.seal.auth_token(),
                            data: a.state.data,
                            lock: None,
                        },
                    })
                    .collect(),
            },
        };
        let articles = issuer.issue(params);
        let conf = conf(&articles).map_err(MultiError::B)?;
        let ledger = Ledger::new(articles, conf)
            .map_err(MultiError::with_third)
            .map_err(MultiError::from_other_a)?;
        let conf: S::Conf = ledger.config();
        let contract_id = ledger.contract_id();
        let genesis_opid = ledger.articles().genesis_opid();
        let mut pile = P::new(conf.into()).map_err(MultiError::C)?;
        pile.session()
            .add_seals(ledger.articles().genesis_opid(), seals);
        Ok(Self {
            ledger,
            pile,
            contract_id,
            valid_cache: HashSet::from([genesis_opid]),
            aux_cache: HashMap::new(),
        })
    }

    pub fn load(
        stock_conf: S::Conf,
        pile_conf: P::Conf,
    ) -> Result<Self, MultiError<S::Error, P::Error>> {
        let ledger = Ledger::load(stock_conf).map_err(MultiError::A)?;
        let contract_id = ledger.contract_id();
        let pile = P::load(pile_conf).map_err(MultiError::B)?;
        let mut contract = Self {
            ledger,
            pile,
            contract_id,
            valid_cache: HashSet::new(),
            aux_cache: HashMap::new(),
        };
        contract.refresh_valid_cache();
        Ok(contract)
    }

    pub fn contract_id(&self) -> ContractId { self.contract_id }
    pub fn articles(&self) -> &Articles { self.ledger.articles() }
    pub fn full_state(&self) -> &EffectiveState { self.ledger.state() }

    fn best_op_status(&mut self, opid: Opid) -> WitnessStatus {
        let wids: Vec<_> = self.pile.session().op_witness_ids(opid).collect();
        wids.into_iter()
            .map(|wid| self.pile.session().witness_status(wid))
            .reduce(|best, other| best.best(other))
            .unwrap_or(WitnessStatus::Genesis)
    }

    fn retrieve(&mut self, opid: Opid) -> Option<SealWitness<P::Seal>> {
        let wids: Vec<_> = self.pile.session().op_witness_ids(opid).collect();
        let (status, wid) = wids
            .into_iter()
            .map(|wid| (self.pile.session().witness_status(wid), wid))
            .reduce(|best, other| if best.0.is_better(other.0) { best } else { other })?;
        if !status.is_valid() {
            return None;
        }
        let mut ps = self.pile.session();
        let client = ps.cli_witness(wid);
        let published = ps.pub_witness(wid);
        Some(SealWitness::new(published, client))
    }

    /// Operations with their pile relations — returns collected Vec to avoid borrow conflicts.
    pub fn operations(&mut self) -> Vec<(Opid, Operation, OpRels<P::Seal>)> {
        self.ledger
            .operations()
            .map(|(opid, op)| {
                let up_to = op.destructible_out.len_u16();
                let rels = self.pile.session().op_relations(opid, up_to);
                (opid, op, rels)
            })
            .collect()
    }

    pub fn trace_ops(&mut self) -> Vec<(Opid, Transition)> { self.ledger.trace_iter().collect() }

    pub fn witness_ids(&mut self) -> Vec<<P::Seal as RgbSeal>::WitnessId> {
        self.pile.session().witness_ids().collect()
    }

    pub fn witnesses(&mut self) -> Vec<Witness<P::Seal>> {
        self.pile.session().witnesses().collect()
    }

    pub fn witness_status(&mut self, wid: <P::Seal as RgbSeal>::WitnessId) -> WitnessStatus {
        self.pile.session().witness_status(wid)
    }

    pub fn ops_by_witness_id(&mut self, wid: <P::Seal as RgbSeal>::WitnessId) -> Vec<Opid> {
        self.pile.session().ops_by_witness_id(wid).collect()
    }

    pub fn op_seals(&mut self, opid: Opid, up_to: u16) -> OpRels<P::Seal> {
        self.pile.session().op_relations(opid, up_to)
    }

    pub fn seal(&self, seal: &<P::Seal as RgbSeal>::Definition) -> Option<CellAddr> {
        let auth = seal.auth_token();
        self.ledger.state().raw.auth.get(&auth).copied()
    }

    pub fn owned_state_entries(&mut self, name: &StateName) -> Vec<(CellAddr, P::Seal, StrictVal)>
    where P::Seal: Clone {
        let Some(states) = self.ledger.state().main.owned.get(name) else {
            return vec![];
        };

        let mut entries = Vec::with_capacity(states.len());
        let mut session = self.pile.session();
        for (addr, data) in states {
            let Some(seal) = session.seal(*addr) else {
                continue;
            };
            if let Some(seal) = seal.to_src() {
                entries.push((*addr, seal, data.clone()));
            }
        }
        entries
    }

    pub fn resolved_owned_state_entries(&mut self, name: &StateName) -> Vec<OwnedState<P::Seal>>
    where P::Seal: Clone {
        self.state().owned.remove(name).unwrap_or_default()
    }

    pub fn resolved_owned_assignments(
        &mut self,
        name: &StateName,
    ) -> Vec<ResolvedOwnedEntry<P::Seal>>
    where
        P::Seal: Clone,
    {
        self.resolved_owned_state_entries(name)
            .into_iter()
            .map(|owned| (owned.addr, owned.assignment))
            .collect()
    }

    fn op_status_with_ancestors(&mut self, opid: Opid, direct: WitnessStatus) -> WitnessStatus {
        self.ledger
            .ancestors([opid])
            .collect::<Vec<_>>()
            .into_iter()
            .map(|ancestor| self.best_op_status(ancestor))
            .fold(WitnessStatus::Genesis, |worst, other| worst.worst(other))
            .worst(direct)
    }

    pub fn resolved_owned_state_entries_filtered(
        &mut self,
        name: &StateName,
        mut predicate: impl FnMut(&P::Seal) -> bool,
    ) -> Vec<OwnedState<P::Seal>>
    where
        P::Seal: Clone,
    {
        let Some(states) = self.ledger.state().main.owned.get(name) else {
            return vec![];
        };

        let mut selected = Vec::new();
        let mut unresolved = Vec::new();
        {
            let mut session = self.pile.session();
            for (addr, data) in states {
                let Some(seal) = session.seal(*addr) else {
                    continue;
                };
                if let Some(seal_src) = seal.to_src() {
                    if predicate(&seal_src) {
                        selected.push((*addr, seal_src, data.clone()));
                    }
                } else {
                    let wids = session.op_witness_ids(addr.opid).collect::<Vec<_>>();
                    unresolved.push((*addr, seal, data.clone(), wids));
                }
            }
        }

        let mut result = selected
            .into_iter()
            .map(|(addr, seal, data)| {
                let direct = self.best_op_status(addr.opid);
                let status = self.op_status_with_ancestors(addr.opid, direct);
                OwnedState { addr, assignment: Assignment { seal, data }, status }
            })
            .collect::<Vec<_>>();

        for (addr, seal, data, wids) in unresolved {
            for wid in wids {
                let seal = seal.resolve(wid);
                if !predicate(&seal) {
                    continue;
                }
                let direct = self.pile.session().witness_status(wid);
                let status = self.op_status_with_ancestors(addr.opid, direct);
                result.push(OwnedState {
                    addr,
                    assignment: Assignment { seal, data: data.clone() },
                    status,
                });
            }
        }

        result
    }

    pub fn state(&mut self) -> ContractState<P::Seal> {
        let main = self.ledger.state().main.clone();
        let genesis_opid = self.ledger.articles().genesis_opid();
        let all_ops: BTreeMap<Opid, Operation> = self.ledger.operations().collect();
        let (all_op_witness_ids, witness_statuses) = {
            let mut session = self.pile.session();
            let mut op_witness_ids = BTreeMap::new();
            let mut statuses = BTreeMap::new();
            for opid in all_ops.keys().copied().chain([genesis_opid]) {
                let wids: Vec<_> = session.op_witness_ids(opid).collect();
                for wid in &wids {
                    statuses
                        .entry(*wid)
                        .or_insert_with(|| session.witness_status(*wid));
                }
                op_witness_ids.insert(opid, wids);
            }
            (op_witness_ids, statuses)
        };

        let mut best_status_cache: BTreeMap<Opid, WitnessStatus> = BTreeMap::new();
        let mut ancestor_cache: BTreeMap<Opid, WitnessStatus> = BTreeMap::new();
        let best_op_status =
            |opid: Opid,
             op_witness_ids: &BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>>,
             statuses: &BTreeMap<<P::Seal as RgbSeal>::WitnessId, WitnessStatus>,
             cache: &mut BTreeMap<Opid, WitnessStatus>| {
                *cache.entry(opid).or_insert_with(|| {
                    op_witness_ids
                        .get(&opid)
                        .into_iter()
                        .flatten()
                        .filter_map(|wid| statuses.get(wid).copied())
                        .reduce(|best, other| best.best(other))
                        .unwrap_or(WitnessStatus::Genesis)
                })
            };
        let ancestors_from_cache = |start: Opid, ops: &BTreeMap<Opid, Operation>| {
            let mut chain = IndexSet::new();
            chain.insert(start);
            let mut index = 0usize;
            while let Some(&opid) = chain.get_index(index) {
                if opid != genesis_opid {
                    if let Some(op) = ops.get(&opid) {
                        for inp in &op.immutable_in {
                            chain.insert(inp.opid);
                        }
                        for inp in &op.destructible_in {
                            chain.insert(inp.addr.opid);
                        }
                    }
                }
                index += 1;
            }
            chain
        };
        let get_status = |opid: Opid,
                          direct: WitnessStatus,
                          ops: &BTreeMap<Opid, Operation>,
                          op_witness_ids: &BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>>,
                          statuses: &BTreeMap<<P::Seal as RgbSeal>::WitnessId, WitnessStatus>,
                          best_cache: &mut BTreeMap<Opid, WitnessStatus>,
                          anc_cache: &mut BTreeMap<Opid, WitnessStatus>| {
            let ancestor_status = *anc_cache.entry(opid).or_insert_with(|| {
                ancestors_from_cache(opid, ops)
                    .iter()
                    .map(|&anc| best_op_status(anc, op_witness_ids, statuses, best_cache))
                    .fold(WitnessStatus::Genesis, |worst, other| worst.worst(other))
            });
            ancestor_status.worst(direct)
        };

        let mut owned = BTreeMap::new();
        for (name, map) in main.owned {
            let mut state = vec![];
            for (addr, data) in map {
                let Some(seal) = self.pile.session().seal(addr) else {
                    continue;
                };
                if let Some(seal_src) = seal.to_src() {
                    let direct = best_op_status(
                        addr.opid,
                        &all_op_witness_ids,
                        &witness_statuses,
                        &mut best_status_cache,
                    );
                    let status = get_status(
                        addr.opid,
                        direct,
                        &all_ops,
                        &all_op_witness_ids,
                        &witness_statuses,
                        &mut best_status_cache,
                        &mut ancestor_cache,
                    );
                    state.push(OwnedState {
                        addr,
                        assignment: Assignment { seal: seal_src, data },
                        status,
                    });
                } else {
                    for wid in all_op_witness_ids
                        .get(&addr.opid)
                        .into_iter()
                        .flatten()
                        .copied()
                    {
                        let direct = witness_statuses
                            .get(&wid)
                            .copied()
                            .unwrap_or(WitnessStatus::Genesis);
                        let status = get_status(
                            addr.opid,
                            direct,
                            &all_ops,
                            &all_op_witness_ids,
                            &witness_statuses,
                            &mut best_status_cache,
                            &mut ancestor_cache,
                        );
                        state.push(OwnedState {
                            addr,
                            assignment: Assignment { seal: seal.resolve(wid), data: data.clone() },
                            status,
                        });
                    }
                }
            }
            owned.insert(name, state);
        }

        let mut immutable = BTreeMap::new();
        for (name, map) in main.global {
            let mut state = vec![];
            for (addr, data) in map {
                let direct = best_op_status(
                    addr.opid,
                    &all_op_witness_ids,
                    &witness_statuses,
                    &mut best_status_cache,
                );
                let status = get_status(
                    addr.opid,
                    direct,
                    &all_ops,
                    &all_op_witness_ids,
                    &witness_statuses,
                    &mut best_status_cache,
                    &mut ancestor_cache,
                );
                state.push(ImmutableState { addr, data, status });
            }
            immutable.insert(name, state);
        }
        ContractState { immutable, owned, aggregated: main.aggregated }
    }

    pub fn sync(
        &mut self,
        changed: impl IntoIterator<Item = (<P::Seal as RgbSeal>::WitnessId, WitnessStatus)>,
    ) -> Result<(), MultiError<AcceptError, S::Error>> {
        // Step 1-2: collect reads
        let mut affected_wids = IndexMap::new();
        for (wid, status) in changed {
            if !self.pile.session().has_witness(wid) {
                continue;
            }
            let prev = self.pile.session().witness_status(wid);
            if status == prev {
                continue;
            }
            let old = affected_wids.insert(wid, status);
            debug_assert!(old.is_none() || old == Some(status));
        }

        let mut affected_ops = IndexMap::new();
        // Collect opids first, then compute status separately to avoid borrow conflict
        let opids_per_wid: Vec<Vec<Opid>> = affected_wids
            .keys()
            .copied()
            .map(|wid| {
                self.pile
                    .session()
                    .ops_by_witness_id(wid)
                    .collect::<Vec<_>>()
            })
            .collect();
        for opids in opids_per_wid {
            for opid in opids {
                let op_status = self.best_op_status(opid);
                let old = affected_ops.insert(opid, op_status);
                debug_assert!(old.is_none() || old == Some(op_status));
            }
        }

        // Step 3: write pile status updates
        {
            let mut ps = self.pile.session();
            for (wid, status) in &affected_wids {
                ps.update_witness_status(*wid, *status);
            }
        }

        // Step 4: filter changed op statuses
        let mut roll_back = IndexSet::new();
        let mut forward = IndexSet::new();
        for (opid, old_status) in affected_ops {
            self.aux_cache.remove(&opid);
            let new_status = self.best_op_status(opid);
            if old_status.is_valid() == new_status.is_valid() {
                continue;
            }
            if new_status.is_valid() {
                forward.insert(opid);
            } else {
                roll_back.insert(opid);
            }
        }
        debug_assert_eq!(forward.intersection(&roll_back).count(), 0);

        // Step 5: ledger rollback/forward
        self.ledger.rollback(roll_back).map_err(MultiError::B)?;
        self.pile.session().commit_transaction();
        self.ledger.forward(forward)?;
        self.pile.session().commit_transaction();
        self.refresh_valid_cache();
        Ok(())
    }

    pub fn call(
        &mut self,
        call: CallParams,
        seals: SmallOrdMap<u16, <P::Seal as RgbSeal>::Definition>,
    ) -> Result<Operation, MultiError<AcceptError, S::Error>> {
        let opid = self.ledger.call(call)?;
        let operation = self.ledger.operation(opid);
        debug_assert_eq!(operation.opid(), opid);
        self.pile.session().add_seals(opid, seals);
        self.valid_cache.insert(opid);
        self.aux_cache.remove(&opid);
        debug_assert_eq!(operation.contract_id, self.contract_id());
        Ok(operation)
    }

    pub fn include(
        &mut self,
        opid: Opid,
        anchor: <P::Seal as RgbSeal>::Client,
        published: &<P::Seal as RgbSeal>::Published,
    ) {
        let wid = published.pub_id();
        let anchor = if self.pile.session().has_witness(wid) {
            let mut prev = self.pile.session().cli_witness(wid);
            if prev != anchor {
                prev.merge(anchor)
                    .expect("incompatible anchors — storage corrupted");
            }
            prev
        } else {
            anchor
        };
        let mut ps = self.pile.session();
        ps.add_witness(opid, wid, published, &anchor, WitnessStatus::Tentative);
        ps.include_commit_transaction();
        self.aux_cache.remove(&opid);
    }

    pub(crate) fn commit_pile_transaction(&mut self) { self.pile.session().commit_transaction(); }

    fn aux<W: WriteRaw>(
        &mut self,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>> {
        let seals = self
            .pile
            .session()
            .seals(opid, op.destructible_out.len_u16());
        writer = seals.strict_encode(writer)?;
        let witness = self.retrieve(opid);
        writer = witness.is_some().strict_encode(writer)?;
        if let Some(w) = witness {
            writer = w.strict_encode(writer)?;
        }
        Ok(writer)
    }

    fn aux_cached<W: WriteRaw>(
        &mut self,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>> {
        if let Some(bytes) = self.aux_cache.get(&opid) {
            unsafe {
                writer.raw_writer().write_raw::<{ usize::MAX }>(bytes)?;
            }
            return Ok(writer);
        }

        let mem_writer = StrictWriter::with(StreamWriter::in_memory::<{ usize::MAX }>());
        let bytes = self.aux(opid, op, mem_writer)?.unbox().unconfine();
        unsafe {
            writer.raw_writer().write_raw::<{ usize::MAX }>(&bytes)?;
        }
        self.aux_cache.insert(opid, bytes);
        Ok(writer)
    }

    pub fn export(&mut self, writer: StrictWriter<impl WriteRaw>) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        // Collect ops first to avoid borrow conflict with aux()
        let ops: Vec<(Opid, Operation)> = self.ledger.operations().collect();
        let count = ops.len() as u32;
        let contract_id = self.contract_id;
        // Encode articles section before calling self.aux (which borrows self.pile)
        let genesis_opid = self.ledger.articles().genesis_opid();
        let genesis_op = self.ledger.articles().genesis().to_operation(contract_id);
        let mut w = writer;
        w = 0u8.strict_encode(w)?; // DEEDS_VERSION = 0
        w = contract_id.strict_encode(w)?;
        w = 0u8.strict_encode(w)?;
        w = self.ledger.articles().strict_encode(w)?;
        w = self.aux_cached(genesis_opid, &genesis_op, w)?;
        w = count.strict_encode(w)?;
        for (opid, op) in ops {
            w = op.strict_encode(w)?;
            w = self.aux_cached(opid, &op, w)?;
        }
        Ok(())
    }

    pub fn consign(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let total_started_at = Instant::now();
        // Warm up witness-backed storage so per-op witness reads during export avoid repeated
        // cold I/O penalties on backends that lazily page witness records.
        let witnesses_started_at = Instant::now();
        let _ = self.witnesses();
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(witnesses_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_witnesses_warmup",
                elapsed_ms,
                contract_id = ?self.contract_id,
                "Slow rgb-std stage"
            );
        }

        // Collect terminal opids
        let terminal_started_at = Instant::now();
        let terminal_opids: Vec<Opid> = terminals
            .into_iter()
            .map(|t| self.ledger.state().addr(*t.borrow()).opid)
            .collect();
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(terminal_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_collect_terminals",
                elapsed_ms,
                contract_id = ?self.contract_id,
                terminals = terminal_opids.len(),
                "Slow rgb-std stage"
            );
        }
        // Collect ops reachable from terminals (ancestors)
        let ancestors_started_at = Instant::now();
        let needed: std::collections::BTreeSet<Opid> = terminal_opids.into_iter().collect();
        let all_needed: std::collections::BTreeSet<Opid> = self
            .ledger
            .ancestors(needed.iter().copied().collect::<Vec<_>>())
            .collect();
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(ancestors_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_collect_ancestors",
                elapsed_ms,
                contract_id = ?self.contract_id,
                terminal_ops = needed.len(),
                ancestor_ops = all_needed.len(),
                "Slow rgb-std stage"
            );
        }
        let load_ops_started_at = Instant::now();
        let genesis_opid = self.ledger.articles().genesis_opid();
        let mut ops = Vec::with_capacity(all_needed.len());
        for opid in all_needed.iter().rev().copied() {
            if opid == genesis_opid {
                continue;
            }
            ops.push((opid, self.ledger.operation(opid)));
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(load_ops_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_load_operations",
                elapsed_ms,
                contract_id = ?self.contract_id,
                selected_ops = ops.len(),
                ancestor_ops = all_needed.len(),
                "Slow rgb-std stage"
            );
        }
        let count = ops.len() as u32;
        let contract_id = self.contract_id;
        let mut writer = writer;
        let write_started_at = Instant::now();
        let genesis_op = self.ledger.articles().genesis().to_operation(contract_id);
        writer = 0u8.strict_encode(writer)?; // DEEDS_VERSION = 0
        writer = contract_id.strict_encode(writer)?;
        writer = 0u8.strict_encode(writer)?;
        writer = self.ledger.articles().strict_encode(writer)?;
        writer = self.aux_cached(genesis_opid, &genesis_op, writer)?;
        writer = count.strict_encode(writer)?;
        for (opid, op) in ops {
            writer = op.strict_encode(writer)?;
            writer = self.aux_cached(opid, &op, writer)?;
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(write_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_write_operations",
                elapsed_ms,
                ?contract_id,
                ancestor_ops = all_needed.len(),
                selected_ops = count,
                "Slow rgb-std stage"
            );
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(total_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_total",
                elapsed_ms,
                ?contract_id,
                ancestor_ops = all_needed.len(),
                selected_ops = count,
                "Slow rgb-std stage"
            );
        }
        Ok(())
    }

    pub fn consume<E>(
        &mut self,
        reader: &mut StrictReader<impl ReadRaw>,
        seal_resolver: impl FnMut(&Operation) -> BTreeMap<u16, <P::Seal as RgbSeal>::Definition>,
        sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
    ) -> Result<(), MultiError<ConsumeError<<P::Seal as RgbSeal>::Definition>, S::Error>>
    where
        <P::Seal as RgbSeal>::Client: StrictDecode,
        <P::Seal as RgbSeal>::Published: StrictDecode,
        <P::Seal as RgbSeal>::WitnessId: StrictDecode,
    {
        let contract_id = parse_consignment(reader).map_err(MultiError::from_a)?;
        if contract_id != self.contract_id() {
            return Err(MultiError::A(ConsumeError::UnknownContract(contract_id)));
        }
        self.consume_internal(reader, seal_resolver, sig_validator)
    }

    pub(crate) fn consume_internal<E>(
        &mut self,
        reader: &mut StrictReader<impl ReadRaw>,
        seal_resolver: impl FnMut(&Operation) -> BTreeMap<u16, <P::Seal as RgbSeal>::Definition>,
        sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
    ) -> Result<(), MultiError<ConsumeError<<P::Seal as RgbSeal>::Definition>, S::Error>>
    where
        <P::Seal as RgbSeal>::Client: StrictDecode,
        <P::Seal as RgbSeal>::Published: StrictDecode,
        <P::Seal as RgbSeal>::WitnessId: StrictDecode,
    {
        let articles = (|| -> Result<Articles, ConsumeError<_>> {
            let ext_blocks = u8::strict_decode(reader)?;
            for _ in 0..ext_blocks {
                let len = u16::strict_decode(reader)?;
                let r = unsafe { reader.raw_reader() };
                let _ = r.read_raw::<{ u16::MAX as usize }>(len as usize)?;
            }
            let semantics = Semantics::strict_decode(reader)?;
            let sig = Option::<SigBlob>::strict_decode(reader)?;
            let issue_version = ReservedBytes::<1>::strict_decode(reader)?;
            let meta = ContractMeta::strict_decode(reader)?;
            let codex = Codex::strict_decode(reader)?;
            let op_reader = OpReader {
                stream: reader,
                seal_resolver,
                count: u32::MAX,
                _phantom: PhantomData,
            };
            self.evaluate_commit(op_reader)?;
            let genesis = self.ledger.articles().genesis().clone();
            let issue = Issue { version: issue_version, meta, codex, genesis };
            Ok(Articles::with(semantics, issue, sig, sig_validator)?)
        })()
        .map_err(MultiError::A)?;

        self.ledger
            .upgrade_apis(articles)
            .map_err(MultiError::from_other_a)?;
        Ok(())
    }

    pub(crate) fn evaluate_commit<R: ReadOperation<Seal = P::Seal>>(
        &mut self,
        reader: R,
    ) -> Result<(), VerificationError<P::Seal>>
    where
        <P::Seal as RgbSeal>::Client: StrictDecode,
        <P::Seal as RgbSeal>::Published: StrictDecode,
        <P::Seal as RgbSeal>::WitnessId: StrictDecode,
    {
        self.evaluate(reader)?;
        if let Err(err) = self.ledger.commit_transaction() {
            panic!("ledger commit_transaction failed: {err}");
        }
        self.pile.session().commit_transaction();
        Ok(())
    }
}

pub struct OpReader<
    'r,
    Seal: RgbSeal,
    R: ReadRaw,
    F: FnMut(&Operation) -> BTreeMap<u16, Seal::Definition>,
> {
    stream: &'r mut StrictReader<R>,
    count: u32,
    seal_resolver: F,
    _phantom: PhantomData<Seal>,
}

impl<'r, Seal: RgbSeal, R: ReadRaw, F: FnMut(&Operation) -> BTreeMap<u16, Seal::Definition>>
    ReadOperation for OpReader<'r, Seal, R, F>
{
    type Seal = Seal;
    fn read_operation(
        &mut self,
    ) -> Result<Option<OperationSeals<Self::Seal>>, impl Error + 'static> {
        if self.count == 0 {
            return Result::<_, DecodeError>::Ok(None);
        }
        let operation = Operation::strict_decode(self.stream)?;
        let mut defined_seals = SmallOrdMap::strict_decode(self.stream)?;
        defined_seals
            .extend((self.seal_resolver)(&operation))
            .map_err(|_| {
                DecodeError::DataIntegrityError(format!("too many seals for {}", operation.opid()))
            })?;
        let witness = Option::<SealWitness<Seal>>::strict_decode(self.stream)?;
        if self.count == u32::MAX {
            self.count = u32::strict_decode(self.stream)?;
        } else {
            self.count -= 1;
        }
        Ok(Some(OperationSeals { operation, defined_seals, witness }))
    }
}

impl<S: Stock, P: Pile> ContractApi<P::Seal> for Contract<S, P> {
    fn contract_id(&self) -> ContractId { self.ledger.contract_id() }
    fn codex(&self) -> &Codex { self.ledger.articles().codex() }
    fn repo(&self) -> &impl LibRepo { self.ledger.articles() }
    fn memory(&self) -> &impl Memory { &self.ledger.state().raw }
    fn is_known(&self, opid: Opid) -> bool { self.valid_cache.contains(&opid) }

    fn apply_operation(&mut self, op: VerifiedOperation) {
        let opid = op.opid();
        self.ledger.apply(op).expect("unable to apply operation");
        self.valid_cache.insert(opid);
        self.aux_cache.remove(&opid);
    }

    fn apply_seals(
        &mut self,
        opid: Opid,
        seals: SmallOrdMap<u16, <P::Seal as RgbSeal>::Definition>,
    ) {
        self.pile.session().add_seals(opid, seals);
        self.aux_cache.remove(&opid);
    }

    fn apply_witness(&mut self, opid: Opid, witness: SealWitness<P::Seal>) {
        self.aux_cache.remove(&opid);
        self.include(opid, witness.client, &witness.published)
    }
}

#[derive(Debug, Display, Error, From)]
#[display(inner)]
pub enum ConsumeError<Seal: RgbSealDef> {
    #[from]
    #[from(io::Error)]
    Io(IoError),
    /// unknown {0} can't be consumed; please import contract articles first.
    #[display(doc_comments)]
    UnknownContract(ContractId),
    #[from]
    Semantics(SemanticError),
    #[from]
    Decode(DecodeError),
    #[from]
    Verify(VerificationError<Seal::Src>),
    #[from]
    #[from(IssueError)]
    // FIXME
    Issue(IssuerError),
}

#[cfg(feature = "binfile")]
mod fs {
    use std::path::Path;

    use binfile::BinFile;
    use strict_encoding::{StreamWriter, StrictDumb, StrictEncode};

    use super::*;
    use crate::{CONSIGN_MAGIC_NUMBER, CONSIGN_VERSION};

    impl<S: Stock, P: Pile> Contract<S, P> {
        pub fn export_to_file(&mut self, path: impl AsRef<Path>) -> io::Result<()>
        where
            <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
            <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
            <P::Seal as RgbSeal>::WitnessId: StrictEncode,
        {
            let file = BinFile::<CONSIGN_MAGIC_NUMBER, CONSIGN_VERSION>::create_new(path)?;
            self.export(StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file)))
        }

        pub fn consign_to_file(
            &mut self,
            path: impl AsRef<Path>,
            terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        ) -> io::Result<()>
        where
            <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
            <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
            <P::Seal as RgbSeal>::WitnessId: StrictEncode,
        {
            let file = BinFile::<CONSIGN_MAGIC_NUMBER, CONSIGN_VERSION>::create_new(path)?;
            self.consign(terminals, StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file)))
        }
    }
}
