// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0

use alloc::collections::{BTreeMap, BTreeSet};
use core::borrow::Borrow;
use core::cell::RefCell;
use core::error::Error;
use core::hash::Hash;
use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::io;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use amplify::confinement::SmallOrdMap;
use amplify::{IoError, MultiError};
use chrono::{DateTime, Utc};
use commit_verify::{ReservedBytes, StrictHash};
use hypersonic::{
    AcceptError, Api, Articles, AuthToken, CallParams, CellAddr, Codex, Consensus, ContractId,
    CoreParams, DataCell, EffectiveState, IssueError, IssueParams, Ledger, LibRepo, Memory,
    MethodName, NamedState, Operation, Opid, ProcessedState, SemanticError, Semantics, SigBlob,
    StateAtom, StateName, Stock, StockSession, Transition,
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
    OpRels, Pile, PileSession, VerifiedOperation, Witness, WitnessStatus, MAX_CONSIGNMENT_OPS,
};

const RGB_STD_SLOW_STAGE_THRESHOLD: Duration = Duration::from_millis(500);
const OP_AUX_CACHE_DEFAULT_MAX_BYTES: usize = 3 * 1024 * 1024;
const OP_AUX_CACHE_HARD_MAX_BYTES: usize = 64 * 1024 * 1024;
const CONTRACT_CACHE_DEFAULT_MAX_ENTRIES: usize = 50_000;
const CONTRACT_CACHE_HARD_MAX_ENTRIES: usize = 250_000;
const SEALS_KNOWN_BATCH_UP_TO_MAX: u16 = 2048;
const OWNED_STATE_STATUS_CACHE_TTL: Duration = Duration::from_secs(10 * 60);
const OWNED_STATE_STATUS_CACHE_MAX_OPS: usize = 50_000;
const OWNED_STATE_STATUS_CACHE_MAX_WITNESSES: usize = 50_000;

fn slow_rgb_stage_elapsed(started_at: Instant) -> Option<u128> {
    let elapsed = started_at.elapsed();
    (elapsed >= RGB_STD_SLOW_STAGE_THRESHOLD).then_some(elapsed.as_millis())
}

fn op_aux_cache_max_bytes() -> usize {
    static MAX_BYTES: OnceLock<usize> = OnceLock::new();
    *MAX_BYTES.get_or_init(|| {
        env::var("RGB_STD_OP_AUX_CACHE_MAX_BYTES")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|value| *value > 0)
            .map(|value| value.min(OP_AUX_CACHE_HARD_MAX_BYTES))
            .unwrap_or(OP_AUX_CACHE_DEFAULT_MAX_BYTES)
    })
}

fn contract_cache_max_entries() -> usize {
    static MAX_ENTRIES: OnceLock<usize> = OnceLock::new();
    *MAX_ENTRIES.get_or_init(|| {
        env::var("RGB_STD_CONTRACT_CACHE_MAX_ENTRIES")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|value| *value > 0)
            .map(|value| value.min(CONTRACT_CACHE_HARD_MAX_ENTRIES))
            .unwrap_or(CONTRACT_CACHE_DEFAULT_MAX_ENTRIES)
    })
}

fn prune_hashset_to<K>(cache: &mut HashSet<K>, max_entries: usize)
where
    K: Copy + Eq + Hash,
{
    if cache.len() <= max_entries {
        return;
    }
    let remove_count = cache.len().saturating_sub(max_entries);
    let keys = cache.iter().take(remove_count).copied().collect::<Vec<_>>();
    for key in keys {
        cache.remove(&key);
    }
}

fn prune_hashmap_to<K, V>(cache: &mut HashMap<K, V>, max_entries: usize)
where
    K: Copy + Eq + Hash,
{
    if cache.len() <= max_entries {
        return;
    }
    let remove_count = cache.len().saturating_sub(max_entries);
    let keys = cache.keys().take(remove_count).copied().collect::<Vec<_>>();
    for key in keys {
        cache.remove(&key);
    }
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
    where
        Seal: RgbSealDef,
    {
        match self {
            EitherSeal::Alt(seal) => seal.auth_token(),
            EitherSeal::Token(auth) => *auth,
        }
    }
    pub fn to_explicit(&self) -> Option<Seal>
    where
        Seal: Clone,
    {
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
    pub fn new(seal: Seal, data: impl Into<StrictVal>) -> Self {
        Self { seal, data: data.into() }
    }
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

#[derive(Clone, Debug)]
struct OwnedStateStatusCache<Wid> {
    genesis_opid: Option<Opid>,
    parent_ops: BTreeMap<Opid, Vec<Opid>>,
    op_witness_ids: BTreeMap<Opid, Vec<Wid>>,
    witness_statuses: BTreeMap<Wid, WitnessStatus>,
    best_statuses: BTreeMap<Opid, WitnessStatus>,
    ancestor_statuses: BTreeMap<Opid, WitnessStatus>,
    touched_at: Instant,
}

impl<Wid> Default for OwnedStateStatusCache<Wid> {
    fn default() -> Self {
        Self {
            genesis_opid: None,
            parent_ops: BTreeMap::new(),
            op_witness_ids: BTreeMap::new(),
            witness_statuses: BTreeMap::new(),
            best_statuses: BTreeMap::new(),
            ancestor_statuses: BTreeMap::new(),
            touched_at: Instant::now(),
        }
    }
}

impl<Wid> OwnedStateStatusCache<Wid> {
    fn is_warm(&self) -> bool {
        self.genesis_opid.is_some()
    }

    fn clear(&mut self) {
        *self = Self::default();
    }
}

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
    seal_def_cache: HashMap<CellAddr, <P::Seal as RgbSeal>::Definition>,
    resolved_seal_cache: HashMap<CellAddr, P::Seal>,
    external_seal_def_cache: Arc<HashMap<CellAddr, <P::Seal as RgbSeal>::Definition>>,
    external_resolved_seal_cache: Arc<HashMap<CellAddr, P::Seal>>,
    duplicate_seal_def_cache: HashSet<CellAddr>,
    duplicate_witness_cache: HashSet<(Opid, <P::Seal as RgbSeal>::WitnessId)>,
    op_aux_cache: HashMap<Opid, Vec<u8>>,
    op_aux_cache_order: VecDeque<Opid>,
    op_aux_cache_bytes: usize,
    owned_state_status_cache: OwnedStateStatusCache<<P::Seal as RgbSeal>::WitnessId>,
}

#[derive(Debug, Default)]
struct ConsumeStats {
    decoded_ops: usize,
    known_ops: usize,
    new_ops: usize,
    witness_known_cache_hits: usize,
    witness_known_db_checks: usize,
    witness_known_db_elapsed_ms: u128,
    known_seal_cache_hits: usize,
    known_seal_external_hits: usize,
    known_seal_db_checks: usize,
    known_seal_db_elapsed_ms: u128,
    seals_known_cache_hits: usize,
    seals_known_external_hits: usize,
    seals_known_db_checks: usize,
    seals_known_db_elapsed_ms: u128,
    seal_updates_empty: usize,
    seal_updates_non_empty: usize,
    duplicate_seal_updates: usize,
    witness_updates: usize,
    duplicate_witness_updates: usize,
    known_materialized_skips: usize,
}

thread_local! {
    static CONSUME_STATS: RefCell<Option<ConsumeStats>> = const { RefCell::new(None) };
}

fn with_consume_stats(update: impl FnOnce(&mut ConsumeStats)) {
    CONSUME_STATS.with(|stats| {
        if let Some(stats) = stats.borrow_mut().as_mut() {
            update(stats);
        }
    });
}

impl<S: Stock, P: Pile> Contract<S, P> {
    fn prune_contract_caches(&mut self) {
        let max_entries = contract_cache_max_entries();
        prune_hashmap_to(&mut self.seal_def_cache, max_entries);
        prune_hashmap_to(&mut self.resolved_seal_cache, max_entries);
        prune_hashset_to(&mut self.duplicate_seal_def_cache, max_entries);
        prune_hashset_to(&mut self.duplicate_witness_cache, max_entries);
    }

    fn refresh_valid_cache(&mut self) {
        let genesis_opid = self.ledger.articles().genesis_opid();
        let valid_cache = self
            .ledger
            .with_session(|session| {
                let mut valid = HashSet::new();
                if session.is_valid(genesis_opid) {
                    valid.insert(genesis_opid);
                }
                for opid in session.valid_opids() {
                    valid.insert(opid);
                }
                Ok::<_, core::convert::Infallible>(valid)
            })
            .expect("infallible valid cache refresh");
        self.valid_cache = valid_cache;
    }

    fn prewarm_known_operation_duplicate_caches(&mut self, operations: &[OperationSeals<P::Seal>]) {
        let known_ops = operations
            .iter()
            .filter(|op| self.valid_cache.contains(&op.operation.opid()))
            .collect::<Vec<_>>();
        if known_ops.is_empty() {
            return;
        }

        let mut session = self.pile.session();
        for op in known_ops {
            let opid = op.operation.opid();

            if !op.defined_seals.is_empty() {
                let seals_match = if let Some(up_to) = op
                    .defined_seals
                    .keys()
                    .next_back()
                    .and_then(|no| no.checked_add(1))
                    .filter(|up_to| *up_to <= SEALS_KNOWN_BATCH_UP_TO_MAX)
                {
                    let stored = session.seals(opid, up_to);
                    op.defined_seals.iter().all(|(no, seal)| {
                        stored.get(no).is_some_and(|stored_seal| stored_seal == seal)
                    })
                } else {
                    op.defined_seals.iter().all(|(no, seal)| {
                        let addr = CellAddr::new(opid, *no);
                        session.seal(addr).is_some_and(|stored| stored == *seal)
                    })
                };

                if seals_match {
                    for (no, seal) in &op.defined_seals {
                        let addr = CellAddr::new(opid, *no);
                        self.seal_def_cache.insert(addr, seal.clone());
                        self.duplicate_seal_def_cache.insert(addr);
                    }
                }
            }

            if let Some(witness) = &op.witness {
                let wid = witness.published.pub_id();
                let witness_matches = session.has_witness(wid)
                    && session.cli_witness(wid) == witness.client
                    && session.ops_by_witness_id(wid).any(|stored| stored == opid);
                if witness_matches {
                    self.duplicate_witness_cache.insert((opid, wid));
                }
            }
        }

        drop(session);
        self.prune_contract_caches();
    }

    fn clear_owned_state_status_cache(&mut self) {
        self.owned_state_status_cache.clear();
    }

    fn ensure_owned_state_status_cache(
        &mut self,
        cache: &mut OwnedStateStatusCache<<P::Seal as RgbSeal>::WitnessId>,
    ) {
        if cache.is_warm() && cache.touched_at.elapsed() < OWNED_STATE_STATUS_CACHE_TTL {
            cache.touched_at = Instant::now();
            return;
        }
        cache.clear();

        let genesis_opid = self.ledger.articles().genesis_opid();
        let parent_ops: BTreeMap<Opid, Vec<Opid>> = self.ledger.operation_parent_ops().collect();

        if parent_ops.len() > OWNED_STATE_STATUS_CACHE_MAX_OPS {
            return;
        }

        let mut op_witness_ids = BTreeMap::new();
        let mut witness_statuses = BTreeMap::new();
        {
            let mut session = self.pile.session();
            for opid in parent_ops.keys().copied().chain([genesis_opid]) {
                let wids = session.op_witness_ids(opid).collect::<Vec<_>>();
                for wid in &wids {
                    witness_statuses
                        .entry(*wid)
                        .or_insert_with(|| session.witness_status(*wid));
                    if witness_statuses.len() > OWNED_STATE_STATUS_CACHE_MAX_WITNESSES {
                        return;
                    }
                }
                op_witness_ids.insert(opid, wids);
            }
        }

        cache.genesis_opid = Some(genesis_opid);
        cache.parent_ops = parent_ops;
        cache.op_witness_ids = op_witness_ids;
        cache.witness_statuses = witness_statuses;
        cache.best_statuses.clear();
        cache.ancestor_statuses.clear();
        cache.touched_at = Instant::now();
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
            seal_def_cache: HashMap::new(),
            resolved_seal_cache: HashMap::new(),
            external_seal_def_cache: Arc::new(HashMap::new()),
            external_resolved_seal_cache: Arc::new(HashMap::new()),
            duplicate_seal_def_cache: HashSet::new(),
            duplicate_witness_cache: HashSet::new(),
            op_aux_cache: HashMap::new(),
            op_aux_cache_order: VecDeque::new(),
            op_aux_cache_bytes: 0,
            owned_state_status_cache: OwnedStateStatusCache::default(),
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
            seal_def_cache: HashMap::new(),
            resolved_seal_cache: HashMap::new(),
            external_seal_def_cache: Arc::new(HashMap::new()),
            external_resolved_seal_cache: Arc::new(HashMap::new()),
            duplicate_seal_def_cache: HashSet::new(),
            duplicate_witness_cache: HashSet::new(),
            op_aux_cache: HashMap::new(),
            op_aux_cache_order: VecDeque::new(),
            op_aux_cache_bytes: 0,
            owned_state_status_cache: OwnedStateStatusCache::default(),
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
            seal_def_cache: HashMap::new(),
            resolved_seal_cache: HashMap::new(),
            external_seal_def_cache: Arc::new(HashMap::new()),
            external_resolved_seal_cache: Arc::new(HashMap::new()),
            duplicate_seal_def_cache: HashSet::new(),
            duplicate_witness_cache: HashSet::new(),
            op_aux_cache: HashMap::new(),
            op_aux_cache_order: VecDeque::new(),
            op_aux_cache_bytes: 0,
            owned_state_status_cache: OwnedStateStatusCache::default(),
        };
        contract.refresh_valid_cache();
        Ok(contract)
    }

    pub fn contract_id(&self) -> ContractId {
        self.contract_id
    }
    pub fn articles(&self) -> &Articles {
        self.ledger.articles()
    }
    pub fn full_state(&self) -> &EffectiveState {
        self.ledger.state()
    }

    fn best_op_status(&mut self, opid: Opid) -> WitnessStatus {
        let wids: Vec<_> = self.pile.session().op_witness_ids(opid).collect();
        wids.into_iter()
            .map(|wid| self.pile.session().witness_status(wid))
            .reduce(|best, other| best.best(other))
            .unwrap_or(WitnessStatus::Genesis)
    }

    fn best_op_status_cached(
        &mut self,
        opid: Opid,
        op_witness_ids_cache: &mut BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>>,
        witness_status_cache: &mut BTreeMap<<P::Seal as RgbSeal>::WitnessId, WitnessStatus>,
        best_status_cache: &mut BTreeMap<Opid, WitnessStatus>,
    ) -> WitnessStatus
    where
        <P::Seal as RgbSeal>::WitnessId: Copy + Ord,
    {
        *best_status_cache.entry(opid).or_insert_with(|| {
            let wids = op_witness_ids_cache
                .entry(opid)
                .or_insert_with(|| self.pile.session().op_witness_ids(opid).collect::<Vec<_>>());
            wids.iter()
                .copied()
                .map(|wid| {
                    *witness_status_cache
                        .entry(wid)
                        .or_insert_with(|| self.pile.session().witness_status(wid))
                })
                .reduce(|best, other| best.best(other))
                .unwrap_or(WitnessStatus::Genesis)
        })
    }

    fn ancestor_status_cached(
        &mut self,
        start: Opid,
        genesis_opid: Opid,
        parent_ops: &BTreeMap<Opid, Vec<Opid>>,
        op_witness_ids_cache: &mut BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>>,
        witness_status_cache: &mut BTreeMap<<P::Seal as RgbSeal>::WitnessId, WitnessStatus>,
        best_status_cache: &mut BTreeMap<Opid, WitnessStatus>,
        ancestor_cache: &mut BTreeMap<Opid, WitnessStatus>,
    ) -> WitnessStatus
    where
        <P::Seal as RgbSeal>::WitnessId: Copy + Ord,
    {
        *ancestor_cache.entry(start).or_insert_with(|| {
            let mut chain = IndexSet::new();
            chain.insert(start);
            let mut index = 0usize;
            while let Some(&opid) = chain.get_index(index) {
                if opid != genesis_opid {
                    if let Some(parents) = parent_ops.get(&opid) {
                        for parent in parents {
                            chain.insert(*parent);
                        }
                    }
                }
                index += 1;
            }

            chain
                .iter()
                .map(|&opid| {
                    self.best_op_status_cached(
                        opid,
                        op_witness_ids_cache,
                        witness_status_cache,
                        best_status_cache,
                    )
                })
                .fold(WitnessStatus::Genesis, |worst, other| worst.worst(other))
        })
    }

    fn retrieve_with_session<PS>(ps: &mut PS, opid: Opid) -> Option<SealWitness<P::Seal>>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let wids: Vec<_> = ps.op_witness_ids(opid).collect();
        let (status, wid) = wids
            .into_iter()
            .map(|wid| (ps.witness_status(wid), wid))
            .reduce(|best, other| if best.0.is_better(other.0) { best } else { other })?;
        if !status.is_valid() {
            return None;
        }
        let client = ps.cli_witness(wid);
        let published = ps.pub_witness(wid);
        Some(SealWitness::new(published, client))
    }

    fn retrieve(&mut self, opid: Opid) -> Option<SealWitness<P::Seal>> {
        let mut ps = self.pile.session();
        Self::retrieve_with_session(&mut ps, opid)
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

    pub fn trace_ops(&mut self) -> Vec<(Opid, Transition)> {
        self.ledger.trace_iter().collect()
    }

    pub fn known_seal_cells(&mut self) -> Vec<CellAddr> {
        self.pile.session().known_seal_cells().collect()
    }

    pub fn known_resolved_seals(&mut self) -> Vec<(CellAddr, P::Seal)> {
        self.known_seal_cells()
            .into_iter()
            .filter_map(|addr| self.known_seal(addr).map(|seal| (addr, seal)))
            .collect()
    }

    pub fn extend_external_resolved_seals(
        &mut self,
        seals: impl IntoIterator<Item = (CellAddr, P::Seal)>,
    ) {
        Arc::make_mut(&mut self.external_resolved_seal_cache).extend(seals);
    }

    pub fn set_external_resolved_seals(&mut self, seals: Arc<HashMap<CellAddr, P::Seal>>) {
        self.external_resolved_seal_cache = seals;
    }

    pub fn extend_external_seal_definitions(
        &mut self,
        seals: impl IntoIterator<Item = (CellAddr, <P::Seal as RgbSeal>::Definition)>,
    ) {
        let cache = Arc::make_mut(&mut self.external_seal_def_cache);
        cache.extend(seals);
        prune_hashmap_to(cache, contract_cache_max_entries());
    }

    pub fn set_external_seal_definitions(
        &mut self,
        seals: Arc<HashMap<CellAddr, <P::Seal as RgbSeal>::Definition>>,
    ) {
        let max_entries = contract_cache_max_entries();
        self.external_seal_def_cache = if seals.len() <= max_entries {
            seals
        } else {
            Arc::new(
                seals
                    .iter()
                    .take(max_entries)
                    .map(|(addr, seal)| (*addr, seal.clone()))
                    .collect(),
            )
        };
    }

    pub fn boundary_opids_for_known_cells(
        &mut self,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
    ) -> Vec<Opid> {
        let known_cells = known_cells
            .into_iter()
            .map(|cell| *cell.borrow())
            .collect::<HashSet<_>>();
        if known_cells.is_empty() {
            return vec![];
        }

        let mut pile_session = self.pile.session();
        let known_seal_cells = pile_session
            .known_seal_cells()
            .filter(|cell| known_cells.contains(cell));
        let mut known_positions_by_opid = HashMap::<Opid, HashSet<u16>>::new();
        for cell in known_seal_cells {
            known_positions_by_opid
                .entry(cell.opid)
                .or_default()
                .insert(cell.pos);
        }

        self.ledger
            .operation_output_counts()
            .filter_map(|(opid, count)| {
                let known_positions = known_positions_by_opid.get(&opid)?;
                (known_positions.len() == count as usize
                    && (0..count).all(|pos| known_positions.contains(&pos)))
                .then_some(opid)
            })
            .collect()
    }

    pub fn witness_ids(&mut self) -> Vec<<P::Seal as RgbSeal>::WitnessId> {
        self.pile.session().witness_ids().collect()
    }

    pub fn witness_statuses(&mut self) -> Vec<(<P::Seal as RgbSeal>::WitnessId, WitnessStatus)> {
        self.pile.session().witness_statuses()
    }

    pub fn witness_statuses_requiring_update(
        &mut self,
        last_block_height: u64,
        min_confirmations: u32,
    ) -> Vec<(<P::Seal as RgbSeal>::WitnessId, WitnessStatus)> {
        self.pile
            .session()
            .witness_statuses_requiring_update(last_block_height, min_confirmations)
    }

    pub fn witnesses(&mut self) -> Vec<Witness<P::Seal>> {
        self.pile.session().witnesses().collect()
    }

    pub fn witness_status(&mut self, wid: <P::Seal as RgbSeal>::WitnessId) -> WitnessStatus {
        self.pile.session().witness_status(wid)
    }

    pub fn witness_statuses_for(
        &mut self,
        witness_ids: impl IntoIterator<Item = <P::Seal as RgbSeal>::WitnessId>,
    ) -> Vec<(<P::Seal as RgbSeal>::WitnessId, WitnessStatus)> {
        self.pile.session().witness_statuses_for(witness_ids)
    }

    pub fn has_witness(&mut self, wid: <P::Seal as RgbSeal>::WitnessId) -> bool {
        self.pile.session().has_witness(wid)
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
    where
        P::Seal: Clone,
    {
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
    where
        P::Seal: Clone,
    {
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

    pub fn resolved_owned_state_entries_filtered(
        &mut self,
        name: &StateName,
        predicate: impl FnMut(&P::Seal) -> bool,
    ) -> Vec<OwnedState<P::Seal>>
    where
        P::Seal: Clone,
    {
        self.resolved_owned_state_entries_filtered_take(name, predicate, None)
    }

    pub fn resolved_owned_state_entries_filtered_take(
        &mut self,
        name: &StateName,
        mut predicate: impl FnMut(&P::Seal) -> bool,
        limit: Option<usize>,
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
                        if limit.is_some_and(|limit| selected.len() >= limit) {
                            break;
                        }
                    }
                } else {
                    let wids = session.op_witness_ids(addr.opid).collect::<Vec<_>>();
                    unresolved.push((*addr, seal, data.clone(), wids));
                }
            }
        }

        if selected.is_empty() && unresolved.is_empty() {
            return vec![];
        }

        let mut status_cache = core::mem::take(&mut self.owned_state_status_cache);
        self.ensure_owned_state_status_cache(&mut status_cache);
        let fallback_parent_ops;
        let (genesis_opid, parent_ops) = if let Some(genesis_opid) = status_cache.genesis_opid {
            (genesis_opid, &status_cache.parent_ops)
        } else {
            let genesis_opid = self.ledger.articles().genesis_opid();
            fallback_parent_ops = self.ledger.operation_parent_ops().collect();
            (genesis_opid, &fallback_parent_ops)
        };
        let mut op_witness_ids_cache = core::mem::take(&mut status_cache.op_witness_ids);
        let mut witness_status_cache = core::mem::take(&mut status_cache.witness_statuses);
        let mut best_status_cache = core::mem::take(&mut status_cache.best_statuses);
        let mut ancestor_cache = core::mem::take(&mut status_cache.ancestor_statuses);

        let mut result = selected
            .into_iter()
            .map(|(addr, seal, data)| {
                let direct = self.best_op_status_cached(
                    addr.opid,
                    &mut op_witness_ids_cache,
                    &mut witness_status_cache,
                    &mut best_status_cache,
                );
                let status = self
                    .ancestor_status_cached(
                        addr.opid,
                        genesis_opid,
                        parent_ops,
                        &mut op_witness_ids_cache,
                        &mut witness_status_cache,
                        &mut best_status_cache,
                        &mut ancestor_cache,
                    )
                    .worst(direct);
                OwnedState { addr, assignment: Assignment { seal, data }, status }
            })
            .collect::<Vec<_>>();

        for (addr, seal, data, wids) in unresolved {
            for wid in wids {
                let seal = seal.resolve(wid);
                if !predicate(&seal) {
                    continue;
                }
                let direct = *witness_status_cache
                    .entry(wid)
                    .or_insert_with(|| self.pile.session().witness_status(wid));
                let status = self
                    .ancestor_status_cached(
                        addr.opid,
                        genesis_opid,
                        parent_ops,
                        &mut op_witness_ids_cache,
                        &mut witness_status_cache,
                        &mut best_status_cache,
                        &mut ancestor_cache,
                    )
                    .worst(direct);
                result.push(OwnedState {
                    addr,
                    assignment: Assignment { seal, data: data.clone() },
                    status,
                });
                if limit.is_some_and(|limit| result.len() >= limit) {
                    break;
                }
            }
        }

        if status_cache.genesis_opid.is_some() {
            status_cache.op_witness_ids = op_witness_ids_cache;
            status_cache.witness_statuses = witness_status_cache;
            status_cache.best_statuses = best_status_cache;
            status_cache.ancestor_statuses = ancestor_cache;
            status_cache.touched_at = Instant::now();
            self.owned_state_status_cache = status_cache;
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
        let status_changed = !affected_wids.is_empty();

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
            self.remove_op_aux_cache_entry(opid);
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
        if status_changed {
            self.clear_owned_state_status_cache();
        }
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
        for (no, seal) in &seals {
            self.seal_def_cache
                .insert(CellAddr::new(opid, *no), seal.clone());
        }
        self.pile.session().add_seals(opid, seals);
        self.valid_cache.insert(opid);
        self.remove_op_aux_cache_entry(opid);
        self.clear_owned_state_status_cache();
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
            if prev == anchor
                && self
                    .pile
                    .session()
                    .ops_by_witness_id(wid)
                    .any(|op| op == opid)
            {
                with_consume_stats(|stats| stats.duplicate_witness_updates += 1);
                return;
            }
            if prev != anchor {
                prev.merge(anchor)
                    .expect("incompatible anchors — storage corrupted");
            }
            prev
        } else {
            anchor
        };
        {
            let mut ps = self.pile.session();
            ps.add_witness(opid, wid, published, &anchor, WitnessStatus::Tentative);
            ps.include_commit_transaction();
        }
        self.remove_op_aux_cache_entry(opid);
        self.clear_owned_state_status_cache();
    }

    pub(crate) fn commit_pile_transaction(&mut self) {
        self.pile.session().commit_transaction();
    }

    fn aux_with_session<W: WriteRaw, PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let seals = ps.seals(opid, op.destructible_out.len_u16());
        writer = seals.strict_encode(writer)?;
        let witness = Self::retrieve_with_session(ps, opid);
        writer = witness.is_some().strict_encode(writer)?;
        if let Some(w) = witness {
            writer = w.strict_encode(writer)?;
        }
        Ok(writer)
    }

    fn remove_op_aux_cache_entry(&mut self, opid: Opid) {
        if let Some(bytes) = self.op_aux_cache.remove(&opid) {
            self.op_aux_cache_bytes = self.op_aux_cache_bytes.saturating_sub(bytes.len());
        }
        self.op_aux_cache_order.retain(|cached| *cached != opid);
    }

    fn touch_op_aux_cache_entry(&mut self, opid: Opid) {
        self.op_aux_cache_order.retain(|cached| *cached != opid);
        self.op_aux_cache_order.push_back(opid);
    }

    fn insert_op_aux_cache_entry(&mut self, opid: Opid, bytes: Vec<u8>) {
        let max_bytes = op_aux_cache_max_bytes();
        let bytes_len = bytes.len();
        if bytes_len > max_bytes {
            return;
        }

        if let Some(old_bytes) = self.op_aux_cache.remove(&opid) {
            self.op_aux_cache_bytes = self.op_aux_cache_bytes.saturating_sub(old_bytes.len());
        }
        self.op_aux_cache_order.retain(|cached| *cached != opid);

        while self.op_aux_cache_bytes.saturating_add(bytes_len) > max_bytes {
            let Some(oldest) = self.op_aux_cache_order.pop_front() else {
                break;
            };
            if let Some(old_bytes) = self.op_aux_cache.remove(&oldest) {
                self.op_aux_cache_bytes = self.op_aux_cache_bytes.saturating_sub(old_bytes.len());
            }
        }

        self.op_aux_cache.insert(opid, bytes);
        self.op_aux_cache_order.push_back(opid);
        self.op_aux_cache_bytes = self.op_aux_cache_bytes.saturating_add(bytes_len);
    }

    fn build_op_aux_cache_entry(&mut self, opid: Opid, op: &Operation) -> io::Result<Vec<u8>> {
        let mut ps = self.pile.session();
        Self::build_op_aux_cache_entry_with_session(&mut ps, opid, op)
    }

    fn build_op_aux_cache_entry_with_session<PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
    ) -> io::Result<Vec<u8>>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let mem_writer = StrictWriter::with(StreamWriter::in_memory::<{ usize::MAX }>());
        let mem_writer = op.strict_encode(mem_writer)?;
        Ok(Self::aux_with_session(ps, opid, op, mem_writer)?
            .unbox()
            .unconfine())
    }

    fn op_aux_cached<W: WriteRaw>(
        &mut self,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>> {
        if let Some(bytes) = self.op_aux_cache.get(&opid) {
            let bytes = bytes.clone();
            self.touch_op_aux_cache_entry(opid);
            unsafe {
                writer.raw_writer().write_raw::<{ usize::MAX }>(&bytes)?;
            }
            return Ok(writer);
        }

        let bytes = self.build_op_aux_cache_entry(opid, op)?;
        unsafe {
            writer.raw_writer().write_raw::<{ usize::MAX }>(&bytes)?;
        }
        self.insert_op_aux_cache_entry(opid, bytes);
        Ok(writer)
    }

    fn prewarm_op_aux_cache(
        &mut self,
        ops: &[(Opid, Operation)],
        contract_id: ContractId,
    ) -> io::Result<usize> {
        let prewarm_started_at = Instant::now();
        let mut encoded = 0usize;
        let mut pending = Vec::new();
        for (idx, (opid, op)) in ops.iter().enumerate() {
            if self.op_aux_cache.contains_key(opid) {
                self.touch_op_aux_cache_entry(*opid);
                continue;
            }
            pending.push((idx, *opid, op));
        }

        let mut warmed = Vec::with_capacity(pending.len());
        {
            let mut ps = self.pile.session();
            let preload_ops = pending
                .iter()
                .map(|(_, opid, op)| (*opid, op.destructible_out.len_u16()));
            ps.preload_aux_reads(preload_ops);
            for (idx, opid, op) in pending {
                let op_started_at = Instant::now();
                let bytes = Self::build_op_aux_cache_entry_with_session(&mut ps, opid, op)?;
                let elapsed_ms = slow_rgb_stage_elapsed(op_started_at);
                warmed.push((idx, opid, bytes, elapsed_ms));
            }
        }

        for (idx, opid, bytes, elapsed_ms) in warmed {
            let bytes_len = bytes.len();
            self.insert_op_aux_cache_entry(opid, bytes);
            encoded += 1;
            if let Some(elapsed_ms) = elapsed_ms {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consign_prewarm_operation",
                    elapsed_ms,
                    ?contract_id,
                    opid = ?opid,
                    idx,
                    total_ops = ops.len(),
                    bytes = bytes_len,
                    cache_bytes = self.op_aux_cache_bytes,
                    cache_entries = self.op_aux_cache.len(),
                    "Slow rgb-std stage"
                );
            }
        }
        if encoded > 0 {
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(prewarm_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consign_prewarm_operations",
                    elapsed_ms,
                    ?contract_id,
                    selected_ops = ops.len(),
                    encoded_ops = encoded,
                    cache_bytes = self.op_aux_cache_bytes,
                    cache_entries = self.op_aux_cache.len(),
                    "Slow rgb-std stage"
                );
            }
        }
        Ok(encoded)
    }

    fn aux_uncached<W: WriteRaw>(
        &mut self,
        opid: Opid,
        op: &Operation,
        writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>> {
        let mut ps = self.pile.session();
        Self::aux_with_session(&mut ps, opid, op, writer)
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
        w = self.aux_uncached(genesis_opid, &genesis_op, w)?;
        w = count.strict_encode(w)?;
        for (opid, op) in ops {
            w = self.op_aux_cached(opid, &op, w)?;
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
        self.consign_with_known_opids(terminals, std::iter::empty::<Opid>(), writer)
    }

    pub fn consign_with_known_opids(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let known_opids = known_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();
        self.consign_with_known_boundaries(terminals, known_opids, HashSet::new(), false, writer)
    }

    pub fn consign_with_known_cells(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let known_cells = known_cells
            .into_iter()
            .map(|cell| *cell.borrow())
            .collect::<HashSet<_>>();
        self.consign_with_known_boundaries(terminals, HashSet::new(), known_cells, false, writer)
    }

    pub fn consign_with_known_cells_and_opids(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let known_cells = known_cells
            .into_iter()
            .map(|cell| *cell.borrow())
            .collect::<HashSet<_>>();
        let known_opids = known_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();
        self.consign_with_known_boundaries(terminals, known_opids, known_cells, false, writer)
    }

    pub fn consign_with_trusted_known_cells_and_opids(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let known_cells = known_cells
            .into_iter()
            .map(|cell| *cell.borrow())
            .collect::<HashSet<_>>();
        let known_opids = known_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();
        self.consign_with_known_boundaries(terminals, known_opids, known_cells, true, writer)
    }

    fn consign_with_known_boundaries(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_opids: HashSet<Opid>,
        known_cells: HashSet<CellAddr>,
        trust_known_opids: bool,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let total_started_at = Instant::now();
        let raw_known_opids = known_opids.len();
        let known_opids = if trust_known_opids {
            known_opids
        } else {
            self.known_boundary_opids_by_cells(known_opids, &known_cells)
        };
        // Collect terminal opids
        let terminal_started_at = Instant::now();
        let terminal_opids: BTreeSet<Opid> = terminals
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
        // Match Ledger::export_aux semantics: follow destroyed cells backwards from
        // terminals and include published global-state definitions required by validation.
        let genesis_opid = self.ledger.articles().genesis_opid();
        let mut published_roots = BTreeSet::new();
        {
            let articles = self.ledger.articles();
            let state = self.ledger.state();
            let mut collect_published_roots = |api: &Api, state: &ProcessedState| {
                for (state_name, owned) in &api.global {
                    if !owned.published {
                        continue;
                    }
                    let Some(cells) = state.global.get(state_name) else {
                        continue;
                    };
                    published_roots.extend(
                        cells
                            .keys()
                            .map(|addr| addr.opid)
                            .filter(|opid| *opid != genesis_opid),
                    );
                }
            };
            collect_published_roots(&articles.semantics().default, &state.main);
            for (api_name, api) in &articles.semantics().custom {
                let Some(state) = state.aux.get(api_name) else {
                    continue;
                };
                collect_published_roots(api, state);
            }
        }
        let published_ops_added = published_roots.len();
        tracing::warn!(
            operation = "rgb_std",
            stage = "consign_select_start",
            contract_id = ?self.contract_id,
            terminal_ops = terminal_opids.len(),
            known_ops = known_opids.len(),
            raw_known_ops = raw_known_opids,
            known_cells = known_cells.len(),
            trust_known_opids,
            published_ops_added,
            "Starting rgb-std consignment operation selection"
        );
        let (_, ops) = self
            .ledger
            .with_session(|session| -> io::Result<_> {
                let select_ops_started_at = Instant::now();
                let mut selected_opids = HashSet::new();
                let mut pending_opids = HashSet::new();
                let mut ordered_opids = Vec::new();
                macro_rules! include_op_with_dependencies {
                    ($root:expr) => {{
                        let root = $root;
                        if root != genesis_opid
                            && !known_opids.contains(&root)
                            && !selected_opids.contains(&root)
                            && pending_opids.insert(root)
                        {
                            let mut stack = vec![(root, false)];
                            while let Some((opid, expanded)) = stack.pop() {
                                if opid == genesis_opid
                                    || known_opids.contains(&opid)
                                    || selected_opids.contains(&opid)
                                {
                                    continue;
                                }
                                if expanded {
                                    pending_opids.remove(&opid);
                                    if selected_opids.insert(opid) {
                                        ordered_opids.push(opid);
                                    }
                                    continue;
                                }

                                stack.push((opid, true));
                                let op = session.operation(opid);
                                for input in &op.immutable_in {
                                    let prev = input.opid;
                                    if prev != genesis_opid
                                        && !known_opids.contains(&prev)
                                        && !selected_opids.contains(&prev)
                                    {
                                        pending_opids.insert(prev);
                                        stack.push((prev, false));
                                    }
                                }
                                for input in &op.destructible_in {
                                    let prev = input.addr.opid;
                                    if prev != genesis_opid
                                        && !known_opids.contains(&prev)
                                        && !selected_opids.contains(&prev)
                                    {
                                        pending_opids.insert(prev);
                                        stack.push((prev, false));
                                    }
                                }
                                let st = session.transition(opid);
                                for addr in st.destroyed.into_keys() {
                                    let prev = addr.opid;
                                    if prev != genesis_opid
                                        && !known_opids.contains(&prev)
                                        && !selected_opids.contains(&prev)
                                    {
                                        pending_opids.insert(prev);
                                        stack.push((prev, false));
                                    }
                                }
                            }
                        }
                    }};
                }

                for opid in terminal_opids.iter().copied() {
                    include_op_with_dependencies!(opid);
                }
                for opid in published_roots {
                    include_op_with_dependencies!(opid);
                }

                if let Some(elapsed_ms) = slow_rgb_stage_elapsed(select_ops_started_at) {
                    tracing::warn!(
                        operation = "rgb_std",
                        stage = "consign_select_operations",
                        elapsed_ms,
                        contract_id = ?self.contract_id,
                        terminal_ops = terminal_opids.len(),
                        selected_ops = selected_opids.len(),
                        known_ops = known_opids.len(),
                        raw_known_ops = raw_known_opids,
                        known_cells = known_cells.len(),
                        trust_known_opids,
                        published_ops_added,
                        "Slow rgb-std stage"
                    );
                }
                let filter_ops_started_at = Instant::now();
                let ops = ordered_opids
                    .into_iter()
                    .map(|opid| (opid, session.operation(opid)))
                    .collect::<Vec<_>>();
                if let Some(elapsed_ms) = slow_rgb_stage_elapsed(filter_ops_started_at) {
                    tracing::warn!(
                        operation = "rgb_std",
                        stage = "consign_filter_operations",
                        elapsed_ms,
                        contract_id = ?self.contract_id,
                        selected_ops = ops.len(),
                        terminal_ops = terminal_opids.len(),
                        known_ops = known_opids.len(),
                        raw_known_ops = raw_known_opids,
                        known_cells = known_cells.len(),
                        trust_known_opids,
                        published_ops_added,
                        "Slow rgb-std stage"
                    );
                }

                Ok((selected_opids.len(), ops))
            })
            .map_err(|err| io::Error::other(err.to_string()))?;
        let count = ops.len() as u32;
        let contract_id = self.contract_id;
        let prewarmed_ops = self.prewarm_op_aux_cache(&ops, contract_id)?;
        let mut writer = writer;
        let write_started_at = Instant::now();
        let genesis_op = self.ledger.articles().genesis().to_operation(contract_id);
        writer = 0u8.strict_encode(writer)?; // DEEDS_VERSION = 0
        writer = contract_id.strict_encode(writer)?;
        writer = 0u8.strict_encode(writer)?;
        writer = self.ledger.articles().strict_encode(writer)?;
        writer = self.aux_uncached(genesis_opid, &genesis_op, writer)?;
        writer = count.strict_encode(writer)?;
        for (opid, op) in ops {
            writer = self.op_aux_cached(opid, &op, writer)?;
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(write_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_write_operations",
                elapsed_ms,
                ?contract_id,
                selected_ops = count,
                known_ops = known_opids.len(),
                raw_known_ops = raw_known_opids,
                known_cells = known_cells.len(),
                trust_known_opids,
                prewarmed_ops,
                "Slow rgb-std stage"
            );
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(total_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_total",
                elapsed_ms,
                ?contract_id,
                selected_ops = count,
                known_ops = known_opids.len(),
                raw_known_ops = raw_known_opids,
                known_cells = known_cells.len(),
                trust_known_opids,
                "Slow rgb-std stage"
            );
        }
        Ok(())
    }

    fn known_boundary_opids_by_cells(
        &mut self,
        known_opids: HashSet<Opid>,
        known_cells: &HashSet<CellAddr>,
    ) -> HashSet<Opid> {
        if known_opids.is_empty() || known_cells.is_empty() {
            return HashSet::new();
        }

        let started_at = Instant::now();
        let raw_known_opids = known_opids.len();
        let output_counts = self
            .ledger
            .operation_output_counts()
            .collect::<HashMap<_, _>>();
        let output_count_entries = output_counts.len();
        let mut operation_decode_fallbacks = 0usize;
        let mut missing_operations = 0usize;
        let candidates = known_opids
            .into_iter()
            .filter_map(|opid| {
                if let Some(count) = output_counts.get(&opid).copied() {
                    return Some((opid, count));
                }

                if !self.ledger.has_operation(opid) {
                    missing_operations = missing_operations.saturating_add(1);
                    return None;
                }

                operation_decode_fallbacks = operation_decode_fallbacks.saturating_add(1);
                let op = self.ledger.operation(opid);
                Some((opid, op.destructible_out.len_u16()))
            })
            .collect::<Vec<_>>();

        let known_opids = self
            .pile
            .session()
            .known_boundary_opids_by_cells(candidates.iter().copied(), known_cells);

        if missing_operations > 0 {
            tracing::debug!(
                operation = "rgb_std",
                stage = "known_boundary_missing_operations",
                contract_id = ?self.contract_id,
                raw_known_ops = raw_known_opids,
                missing_operations,
                operation_decode_fallbacks,
                known_cells = known_cells.len(),
                "Ignoring known opid boundaries missing from stock session"
            );
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "known_boundary_filter_opids",
                elapsed_ms,
                contract_id = ?self.contract_id,
                raw_known_ops = raw_known_opids,
                candidate_ops = candidates.len(),
                accepted_ops = known_opids.len(),
                missing_operations,
                operation_decode_fallbacks,
                output_count_entries,
                known_cells = known_cells.len(),
                "Slow rgb-std stage"
            );
        }

        known_opids
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
            let evaluate_started_at = Instant::now();
            let previous_stats =
                CONSUME_STATS.with(|stats| stats.replace(Some(ConsumeStats::default())));
            let predecode_started_at = Instant::now();
            let operations = decode_consignment_operations(reader, seal_resolver)?;
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(predecode_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consume_predecode_operations",
                    elapsed_ms,
                    contract_id = ?self.contract_id,
                    operations = operations.len(),
                    "Slow rgb-std stage"
                );
            }

            let preload_started_at = Instant::now();
            {
                let preload_ops = operations
                    .iter()
                    .map(|op| (op.operation.opid(), op.operation.destructible_out.len_u16()));
                self.pile.session().preload_aux_reads(preload_ops);
            }
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(preload_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consume_prewarm_aux_reads",
                    elapsed_ms,
                    contract_id = ?self.contract_id,
                    operations = operations.len(),
                    "Slow rgb-std stage"
                );
            }

            let duplicate_cache_started_at = Instant::now();
            self.prewarm_known_operation_duplicate_caches(&operations);
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(duplicate_cache_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consume_prewarm_duplicate_caches",
                    elapsed_ms,
                    contract_id = ?self.contract_id,
                    operations = operations.len(),
                    duplicate_seal_def_cache_entries = self.duplicate_seal_def_cache.len(),
                    duplicate_witness_cache_entries = self.duplicate_witness_cache.len(),
                    "Slow rgb-std stage"
                );
            }

            let op_reader = PredecodedOpReader(VecDeque::from(operations));
            let evaluate_result = self.evaluate_commit(op_reader);
            let stats = CONSUME_STATS
                .with(|stats| stats.replace(previous_stats))
                .unwrap_or_default();
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(evaluate_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consume_evaluate",
                    elapsed_ms,
                    contract_id = ?self.contract_id,
                    decoded_ops = stats.decoded_ops,
                    known_ops = stats.known_ops,
                    new_ops = stats.new_ops,
                    witness_known_cache_hits = stats.witness_known_cache_hits,
                    witness_known_db_checks = stats.witness_known_db_checks,
                    witness_known_db_elapsed_ms = stats.witness_known_db_elapsed_ms,
                    known_seal_cache_hits = stats.known_seal_cache_hits,
                    known_seal_external_hits = stats.known_seal_external_hits,
                    known_seal_db_checks = stats.known_seal_db_checks,
                    known_seal_db_elapsed_ms = stats.known_seal_db_elapsed_ms,
                    seals_known_cache_hits = stats.seals_known_cache_hits,
                    seals_known_external_hits = stats.seals_known_external_hits,
                    seals_known_db_checks = stats.seals_known_db_checks,
                    seals_known_db_elapsed_ms = stats.seals_known_db_elapsed_ms,
                    seal_updates_empty = stats.seal_updates_empty,
                    seal_updates_non_empty = stats.seal_updates_non_empty,
                    duplicate_seal_updates = stats.duplicate_seal_updates,
                    witness_updates = stats.witness_updates,
                    duplicate_witness_updates = stats.duplicate_witness_updates,
                    known_materialized_skips = stats.known_materialized_skips,
                    seal_def_cache_entries = self.seal_def_cache.len(),
                    resolved_seal_cache_entries = self.resolved_seal_cache.len(),
                    duplicate_seal_def_cache_entries = self.duplicate_seal_def_cache.len(),
                    duplicate_witness_cache_entries = self.duplicate_witness_cache.len(),
                    contract_cache_max_entries = contract_cache_max_entries(),
                    "Slow rgb-std stage"
                );
            }
            evaluate_result?;
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

impl<S: Stock, P: Pile> ContractApi<P::Seal> for Contract<S, P> {
    fn contract_id(&self) -> ContractId {
        self.ledger.contract_id()
    }
    fn codex(&self) -> &Codex {
        self.ledger.articles().codex()
    }
    fn repo(&self) -> &impl LibRepo {
        self.ledger.articles()
    }
    fn memory(&self) -> &impl Memory {
        &self.ledger.state().raw
    }
    fn is_known(&self, opid: Opid) -> bool {
        let known = self.valid_cache.contains(&opid);
        with_consume_stats(|stats| {
            if known {
                stats.known_ops += 1;
            } else {
                stats.new_ops += 1;
            }
        });
        known
    }

    fn is_witness_known(&mut self, opid: Opid, witness: &SealWitness<P::Seal>) -> bool {
        let wid = witness.published.pub_id();
        if self.duplicate_witness_cache.contains(&(opid, wid)) {
            with_consume_stats(|stats| {
                stats.witness_known_cache_hits += 1;
                stats.duplicate_witness_updates += 1;
            });
            return true;
        }

        let db_started_at = Instant::now();
        let mut ps = self.pile.session();
        let known = ps.has_witness(wid)
            && ps.cli_witness(wid) == witness.client
            && ps.ops_by_witness_id(wid).any(|op| op == opid);
        let db_elapsed_ms = db_started_at.elapsed().as_millis();
        drop(ps);
        with_consume_stats(|stats| {
            stats.witness_known_db_checks += 1;
            stats.witness_known_db_elapsed_ms += db_elapsed_ms;
        });
        if known {
            self.duplicate_witness_cache.insert((opid, wid));
            self.prune_contract_caches();
            with_consume_stats(|stats| stats.duplicate_witness_updates += 1);
        }
        known
    }

    fn known_seal(&mut self, addr: CellAddr) -> Option<P::Seal> {
        if let Some(seal) = self.resolved_seal_cache.get(&addr) {
            with_consume_stats(|stats| stats.known_seal_cache_hits += 1);
            return Some(seal.clone());
        }

        let definition = if let Some(definition) = self.seal_def_cache.get(&addr) {
            definition.clone()
        } else if let Some(definition) = self.external_seal_def_cache.get(&addr) {
            let definition = definition.clone();
            self.seal_def_cache.insert(addr, definition.clone());
            self.prune_contract_caches();
            with_consume_stats(|stats| {
                stats.seals_known_external_hits += 1;
            });
            definition
        } else {
            let db_started_at = Instant::now();
            let seal = self.pile.session().seal(addr);
            let db_elapsed_ms = db_started_at.elapsed().as_millis();
            with_consume_stats(|stats| {
                stats.known_seal_db_checks += 1;
                stats.known_seal_db_elapsed_ms += db_elapsed_ms;
            });
            match seal {
                Some(definition) => {
                    self.seal_def_cache.insert(addr, definition.clone());
                    self.prune_contract_caches();
                    definition
                }
                None => {
                    let seal = self.external_resolved_seal_cache.get(&addr).cloned();
                    if seal.is_some() {
                        with_consume_stats(|stats| stats.known_seal_external_hits += 1);
                    }
                    return seal;
                }
            }
        };
        if let Some(seal) = definition.to_src() {
            self.resolved_seal_cache.insert(addr, seal.clone());
            self.prune_contract_caches();
            return Some(seal);
        }
        let Some(witness) = self.retrieve(addr.opid) else {
            let seal = self.external_resolved_seal_cache.get(&addr).cloned();
            if seal.is_some() {
                with_consume_stats(|stats| stats.known_seal_external_hits += 1);
            }
            return seal;
        };
        let seal = definition.resolve(witness.published.pub_id());
        self.resolved_seal_cache.insert(addr, seal.clone());
        self.prune_contract_caches();
        Some(seal)
    }

    fn are_seals_known(
        &mut self,
        opid: Opid,
        seals: &SmallOrdMap<u16, <P::Seal as RgbSeal>::Definition>,
    ) -> bool {
        if seals.is_empty() {
            with_consume_stats(|stats| stats.known_materialized_skips += 1);
            return true;
        }

        let cached = seals.iter().all(|(no, seal)| {
            let addr = CellAddr::new(opid, *no);
            self.seal_def_cache
                .get(&addr)
                .is_some_and(|stored| stored == seal)
        });
        if cached {
            with_consume_stats(|stats| {
                stats.seals_known_cache_hits += 1;
                stats.duplicate_seal_updates += 1;
                stats.known_materialized_skips += 1;
            });
            return true;
        }

        let external_cached = seals.iter().all(|(no, seal)| {
            let addr = CellAddr::new(opid, *no);
            self.seal_def_cache
                .get(&addr)
                .or_else(|| self.external_seal_def_cache.get(&addr))
                .is_some_and(|stored| stored == seal)
        });
        if external_cached {
            self.seal_def_cache.extend(seals.iter().map(|(no, seal)| {
                let addr = CellAddr::new(opid, *no);
                let seal = self
                    .external_seal_def_cache
                    .get(&addr)
                    .cloned()
                    .unwrap_or_else(|| seal.clone());
                (addr, seal)
            }));
            self.prune_contract_caches();
            self.duplicate_seal_def_cache
                .extend(seals.keys().map(|no| CellAddr::new(opid, *no)));
            self.prune_contract_caches();
            with_consume_stats(|stats| {
                stats.seals_known_external_hits += 1;
                stats.duplicate_seal_updates += 1;
                stats.known_materialized_skips += 1;
            });
            return true;
        }

        let missing = seals
            .iter()
            .filter_map(|(no, seal)| {
                let addr = CellAddr::new(opid, *no);
                if self
                    .seal_def_cache
                    .get(&addr)
                    .is_some_and(|stored| stored == seal)
                {
                    return None;
                }
                if let Some(stored) = self.external_seal_def_cache.get(&addr) {
                    if stored == seal {
                        self.seal_def_cache.insert(addr, stored.clone());
                        return None;
                    }
                }
                Some((*no, seal.clone()))
            })
            .collect::<Vec<_>>();

        let db_started_at = Instant::now();
        let mut ps = self.pile.session();
        let known = if let Some(up_to) = seals
            .keys()
            .next_back()
            .and_then(|no| no.checked_add(1))
            .filter(|up_to| *up_to <= SEALS_KNOWN_BATCH_UP_TO_MAX)
        {
            let stored = ps.seals(opid, up_to);
            missing.into_iter().all(|(no, seal)| {
                let Some(stored_seal) = stored.get(&no) else {
                    return false;
                };
                if *stored_seal != seal {
                    return false;
                }
                self.seal_def_cache
                    .insert(CellAddr::new(opid, no), stored_seal.clone());
                true
            })
        } else {
            missing.into_iter().all(|(no, seal)| {
                let addr = CellAddr::new(opid, no);
                let Some(stored) = ps.seal(addr) else {
                    return false;
                };
                if stored != seal {
                    return false;
                }
                self.seal_def_cache.insert(addr, stored);
                true
            })
        };
        drop(ps);
        let db_elapsed_ms = db_started_at.elapsed().as_millis();
        with_consume_stats(|stats| {
            stats.seals_known_db_checks += 1;
            stats.seals_known_db_elapsed_ms += db_elapsed_ms;
        });
        self.prune_contract_caches();

        if known {
            self.duplicate_seal_def_cache
                .extend(seals.keys().map(|no| CellAddr::new(opid, *no)));
            self.prune_contract_caches();
            with_consume_stats(|stats| {
                stats.duplicate_seal_updates += 1;
                stats.known_materialized_skips += 1;
            });
        }
        known
    }

    fn apply_operation(&mut self, op: VerifiedOperation) {
        let opid = op.opid();
        self.ledger.apply(op).expect("unable to apply operation");
        self.valid_cache.insert(opid);
        self.remove_op_aux_cache_entry(opid);
        self.clear_owned_state_status_cache();
    }

    fn apply_seals(
        &mut self,
        opid: Opid,
        seals: SmallOrdMap<u16, <P::Seal as RgbSeal>::Definition>,
    ) {
        if seals.is_empty() {
            with_consume_stats(|stats| stats.seal_updates_empty += 1);
            return;
        }
        with_consume_stats(|stats| stats.seal_updates_non_empty += 1);

        let cached_duplicate = seals.iter().all(|(no, seal)| {
            let addr = CellAddr::new(opid, *no);
            self.duplicate_seal_def_cache.contains(&addr)
                && self
                    .seal_def_cache
                    .get(&addr)
                    .is_some_and(|stored| stored == seal)
        });
        if cached_duplicate {
            self.remove_op_aux_cache_entry(opid);
            with_consume_stats(|stats| stats.duplicate_seal_updates += 1);
            return;
        }

        let missing = seals
            .iter()
            .filter_map(|(no, seal)| {
                let addr = CellAddr::new(opid, *no);
                if self
                    .seal_def_cache
                    .get(&addr)
                    .is_some_and(|stored| stored == seal)
                {
                    return None;
                }
                if let Some(stored) = self.external_seal_def_cache.get(&addr) {
                    if stored == seal {
                        self.seal_def_cache.insert(addr, stored.clone());
                        return None;
                    }
                }
                Some((*no, seal.clone()))
            })
            .collect::<Vec<_>>();

        let duplicate = if missing.is_empty() {
            true
        } else {
            let mut ps = self.pile.session();
            if let Some(up_to) = seals
                .keys()
                .next_back()
                .and_then(|no| no.checked_add(1))
                .filter(|up_to| *up_to <= SEALS_KNOWN_BATCH_UP_TO_MAX)
            {
                let stored = ps.seals(opid, up_to);
                missing.into_iter().all(|(no, seal)| {
                    let Some(stored_seal) = stored.get(&no) else {
                        return false;
                    };
                    if *stored_seal != seal {
                        return false;
                    }
                    self.seal_def_cache
                        .insert(CellAddr::new(opid, no), stored_seal.clone());
                    true
                })
            } else {
                missing.into_iter().all(|(no, seal)| {
                    let addr = CellAddr::new(opid, no);
                    let Some(stored) = ps.seal(addr) else {
                        return false;
                    };
                    if stored != seal {
                        return false;
                    }
                    self.seal_def_cache.insert(addr, stored);
                    true
                })
            }
        };
        if duplicate {
            self.duplicate_seal_def_cache
                .extend(seals.keys().map(|no| CellAddr::new(opid, *no)));
            self.prune_contract_caches();
            self.remove_op_aux_cache_entry(opid);
            with_consume_stats(|stats| stats.duplicate_seal_updates += 1);
            return;
        }
        for (no, seal) in &seals {
            let addr = CellAddr::new(opid, *no);
            self.seal_def_cache.insert(addr, seal.clone());
            self.resolved_seal_cache.remove(&addr);
            self.duplicate_seal_def_cache.insert(addr);
        }
        self.prune_contract_caches();
        self.pile.session().add_seals(opid, seals);
        self.remove_op_aux_cache_entry(opid);
        self.clear_owned_state_status_cache();
    }

    fn apply_witness(&mut self, opid: Opid, witness: SealWitness<P::Seal>) {
        with_consume_stats(|stats| stats.witness_updates += 1);
        let wid = witness.published.pub_id();
        self.include(opid, witness.client, &witness.published);
        self.duplicate_witness_cache.insert((opid, wid));
        self.resolved_seal_cache.retain(|addr, _| addr.opid != opid);
    }
}

fn decode_consignment_operations<Seal: RgbSeal, R: ReadRaw>(
    reader: &mut StrictReader<R>,
    mut seal_resolver: impl FnMut(&Operation) -> BTreeMap<u16, Seal::Definition>,
) -> Result<Vec<OperationSeals<Seal>>, DecodeError>
where
    Seal::Client: StrictDecode,
    Seal::Published: StrictDecode,
    Seal::WitnessId: StrictDecode,
{
    let mut operations = Vec::new();
    let mut count = u32::MAX;
    loop {
        if count == 0 {
            return Ok(operations);
        }

        let operation = Operation::strict_decode(reader)?;
        let mut defined_seals = SmallOrdMap::strict_decode(reader)?;
        with_consume_stats(|stats| stats.decoded_ops += 1);
        defined_seals
            .extend(seal_resolver(&operation))
            .map_err(|_| {
                DecodeError::DataIntegrityError(format!("too many seals for {}", operation.opid()))
            })?;
        let witness = Option::<SealWitness<Seal>>::strict_decode(reader)?;
        if count == u32::MAX {
            count = u32::strict_decode(reader)?;
            operations.reserve(count.min(MAX_CONSIGNMENT_OPS) as usize);
        } else {
            count -= 1;
        }
        operations.push(OperationSeals { operation, defined_seals, witness });
    }
}

struct PredecodedOpReader<Seal: RgbSeal>(VecDeque<OperationSeals<Seal>>);

impl<Seal: RgbSeal> ReadOperation for PredecodedOpReader<Seal> {
    type Seal = Seal;

    fn read_operation(
        &mut self,
    ) -> Result<Option<OperationSeals<Self::Seal>>, impl Error + 'static> {
        Result::<_, core::convert::Infallible>::Ok(self.0.pop_front())
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
