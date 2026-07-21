// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0

use alloc::collections::{BTreeMap, BTreeSet};
use core::borrow::Borrow;
use core::cell::RefCell;
use core::error::Error;
use core::hash::Hash;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};
use std::{env, io};

use amplify::confinement::SmallOrdMap;
use amplify::{ByteArray, IoError, MultiError};
use chrono::{DateTime, Utc};
use commit_verify::{ReservedBytes, StrictHash};
use hypersonic::{
    AcceptError, Api, Articles, AuthToken, CallParams, CellAddr, Codex, Consensus, ContractId,
    CoreParams, DataCell, EffectiveState, Genesis, IssueError, IssueParams, Ledger, LibRepo,
    Memory, MethodName, NamedState, Operation, Opid, ProcessedState, RawState, SemanticError,
    Semantics, SigBlob, StateAtom, StateCell, StateData, StateName, StateValue, Stock,
    StockSession, Transition,
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
const OWNED_STATE_STATUS_CACHE_TTL: Duration = Duration::from_secs(10 * 60);
const OWNED_STATE_STATUS_CACHE_MAX_OPS: usize = 50_000;
const OWNED_STATE_STATUS_CACHE_MAX_WITNESSES: usize = 50_000;

fn slow_rgb_stage_elapsed(started_at: Instant) -> Option<u128> {
    let elapsed = started_at.elapsed();
    (elapsed >= rgb_std_slow_stage_threshold()).then_some(elapsed.as_millis())
}

fn rgb_std_slow_stage_threshold() -> Duration {
    static THRESHOLD: OnceLock<Duration> = OnceLock::new();
    *THRESHOLD.get_or_init(|| {
        env::var("RGB_STD_SLOW_STAGE_THRESHOLD_MS")
            .ok()
            .and_then(|value| value.trim().parse::<u64>().ok())
            .map(Duration::from_millis)
            .unwrap_or(RGB_STD_SLOW_STAGE_THRESHOLD)
    })
}

/// Runtime switch for consume phase-breakdown diagnostics, cached once. Enabled when
/// `RGB_VERIFY_DIAG` is `1`/`true`/`on`. Off by default; when on,
/// `evaluate_commit` emits one `rgb_verify_diag` line splitting verification from
/// ledger and pile commit time.
fn verify_diag_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("RGB_VERIFY_DIAG")
            .map(|value| {
                let value = value.trim();
                value == "1"
                    || value.eq_ignore_ascii_case("true")
                    || value.eq_ignore_ascii_case("on")
            })
            .unwrap_or(false)
    })
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
where K: Copy + Eq + Hash {
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
where K: Copy + Eq + Hash {
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

struct OwnedStateStatusContext<Wid> {
    cache: OwnedStateStatusCache<Wid>,
    genesis_opid: Opid,
    parent_ops: BTreeMap<Opid, Vec<Opid>>,
    op_witness_ids: BTreeMap<Opid, Vec<Wid>>,
    witness_statuses: BTreeMap<Wid, WitnessStatus>,
    best_statuses: BTreeMap<Opid, WitnessStatus>,
    ancestor_statuses: BTreeMap<Opid, WitnessStatus>,
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
    fn is_warm(&self) -> bool { self.genesis_opid.is_some() }

    fn clear(&mut self) { *self = Self::default(); }
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

#[derive(Clone, Debug, Default)]
struct GenesisVerificationMemory {
    raw: RawState,
}

impl GenesisVerificationMemory {
    fn clear(&mut self) { self.raw = RawState::default(); }

    fn replace_with_operation(&mut self, opid: Opid, operation: &Operation) {
        self.clear();
        self.insert_operation_outputs(opid, operation);
    }

    fn insert_operation_outputs(&mut self, opid: Opid, operation: &Operation) {
        for (no, cell) in operation.destructible_out.iter().cloned().enumerate() {
            let addr = CellAddr::new(opid, no as u16);
            self.raw
                .auth
                .insert(cell.auth, addr)
                .expect("verification state is too large");
            self.raw
                .owned
                .insert(addr, cell)
                .expect("verification state is too large");
        }

        self.raw
            .global
            .extend(
                operation
                    .immutable_out
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(no, data)| (CellAddr::new(opid, no as u16), data)),
            )
            .expect("verification state is too large");
    }

    fn destructible(&self, addr: CellAddr) -> Option<StateCell> { self.raw.destructible(addr) }

    fn immutable(&self, addr: CellAddr) -> Option<StateValue> { self.raw.immutable(addr) }

    fn immutable_data(&self, addr: CellAddr) -> Option<StateData> {
        self.raw.global.get(&addr).cloned()
    }
}

struct ConsignmentGenesisOperations {
    verification: Operation,
    contract: Operation,
}

impl ConsignmentGenesisOperations {
    fn from_issue(issue: &Issue) -> Self {
        let codex_contract_id = ContractId::from_byte_array(issue.codex_id().to_byte_array());

        Self {
            verification: issue.genesis.to_operation(codex_contract_id),
            contract: issue.genesis.to_operation(issue.contract_id()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Contract<S: Stock, P: Pile> {
    contract_id: ContractId,
    ledger: Ledger<S>,
    pile: P,
    genesis_verification_memory: GenesisVerificationMemory,
    /// Per-consume overlay for outputs of fully-known operations skipped by the verifier fast
    /// path. This lets later operations in the same consignment read historical state without
    /// permanently resurrecting already-spent cells.
    known_verification_memory: GenesisVerificationMemory,
    /// Genesis opid for which `genesis_verification_memory` is currently staged, if any.
    /// Genesis state is immutable for the life of a contract (the contract id commits to it),
    /// so once staged it can be reused across every consume instead of being rebuilt and
    /// cleared each time. Only ever holds genesis state, which is always valid to fall back to.
    genesis_verification_memory_staged_for: Option<Opid>,
    /// In-memory cache of valid opids for `ContractApi::is_known(&self)` which requires &self.
    valid_cache: HashSet<Opid>,
    /// Opids applied as *new* (not-known) during the in-flight consume. `apply_operation` runs
    /// only for not-known ops (rgb-core invariant) and before `apply_seals` for the same op, so a
    /// hit here means the op's output seals are not yet stored and `apply_seals` can skip the
    /// per-op `seal_definitions_match` DB round-trip. Cleared at the start of every consume, so it
    /// stays bounded by one consignment's new cohort (transient, not a persistent cross-contract
    /// cache).
    applied_new_ops: HashSet<Opid>,
    /// Per-consume, non-evicting backstop for seal definitions batch-loaded by the prewarm
    /// (known-op aux matches + destructible-input seals). Unlike `seal_def_cache` it is never
    /// pruned mid-consume, so `are_seals_known` and `known_seal` resolve from memory instead of
    /// re-issuing a per-op/per-cell DB round-trip after the bounded cache evicts the prewarmed
    /// entries. Cleared at the start of every consume, so it stays bounded by one consignment's
    /// working set (transient ~MBs, not a persistent per-contract cache that would grow RSS).
    consume_seal_defs: HashMap<CellAddr, <P::Seal as RgbSeal>::Definition>,
    seal_def_cache: HashMap<CellAddr, <P::Seal as RgbSeal>::Definition>,
    resolved_seal_cache: HashMap<CellAddr, P::Seal>,
    external_seal_def_cache: Arc<HashMap<CellAddr, <P::Seal as RgbSeal>::Definition>>,
    external_resolved_seal_cache: Arc<HashMap<CellAddr, P::Seal>>,
    duplicate_seal_def_cache: HashSet<CellAddr>,
    duplicate_witness_cache: HashSet<(Opid, <P::Seal as RgbSeal>::WitnessId)>,
    pending_witness_updates: PendingWitnessUpdates<P::Seal>,
    op_aux_cache: HashMap<Opid, OpAuxCacheEntry<P::Seal>>,
    op_aux_cache_order: BTreeMap<u64, Opid>,
    op_aux_cache_positions: HashMap<Opid, u64>,
    op_aux_cache_next_seq: u64,
    op_aux_cache_bytes: usize,
    owned_state_status_cache: OwnedStateStatusCache<<P::Seal as RgbSeal>::WitnessId>,
}

struct PendingWitnessUpdates<Seal: RgbSeal>(Vec<(Opid, SealWitness<Seal>)>);

impl<Seal: RgbSeal> PendingWitnessUpdates<Seal> {
    fn is_empty(&self) -> bool { self.0.is_empty() }
    fn len(&self) -> usize { self.0.len() }
    fn push(&mut self, update: (Opid, SealWitness<Seal>)) { self.0.push(update); }
    fn take(&mut self) -> Vec<(Opid, SealWitness<Seal>)> { core::mem::take(&mut self.0) }
}

impl<Seal: RgbSeal> Default for PendingWitnessUpdates<Seal> {
    fn default() -> Self { Self(Vec::new()) }
}

impl<Seal: RgbSeal> Clone for PendingWitnessUpdates<Seal> {
    fn clone(&self) -> Self { Self::default() }
}

impl<Seal: RgbSeal> core::fmt::Debug for PendingWitnessUpdates<Seal> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PendingWitnessUpdates")
            .field("len", &self.0.len())
            .finish()
    }
}

#[derive(Clone)]
struct OpAuxCacheEntry<Seal: RgbSeal> {
    bytes: Vec<u8>,
    operation_seals: Arc<OperationSeals<Seal>>,
}

impl<Seal: RgbSeal> core::fmt::Debug for OpAuxCacheEntry<Seal> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("OpAuxCacheEntry")
            .field("bytes", &self.bytes.len())
            .finish_non_exhaustive()
    }
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
    // apply_witness / include same-entry sub-timers (microseconds); residual-closed
    // against apply_witness_total_us = include(resolve+add+aux) + dupcache + retain.
    apply_witness_total_us: u128,
    apply_witness_dupcache_us: u128,
    apply_witness_retain_us: u128,
    include_resolve_us: u128,
    include_has_witness_us: u128,
    include_cli_witness_us: u128,
    include_ops_by_witness_us: u128,
    include_add_us: u128,
    include_aux_us: u128,
    // apply_seals same-entry sub-timers (microseconds); residual-closed against
    // apply_seals_total_us = cached_dup + missing_scan + match + dup_finalize + insert +
    // add_seals.
    apply_seals_total_us: u128,
    seals_cached_dup_us: u128,
    seals_missing_scan_us: u128,
    seals_match_us: u128,
    seals_dup_finalize_us: u128,
    seals_insert_us: u128,
    seals_add_seals_us: u128,
    // apply_operation sub-timers (microseconds); residual-closed against the
    // rgb-core apply_op_us bucket.
    apply_operation_total_us: u128,
    apply_operation_opid_us: u128,
    apply_operation_stage_inputs_us: u128,
    apply_operation_ledger_apply_us: u128,
    apply_operation_cache_us: u128,
    known_materialized_skips: usize,
    predecoded_resolver_calls: usize,
    predecoded_resolver_skips: usize,
    prewarm_total_us: u128,
    prewarm_partition_us: u128,
    prewarm_known_duplicates_us: u128,
    prewarm_destructible_inputs_us: u128,
    prewarm_output_seals_us: u128,
    prewarm_witnesses_us: u128,
    prewarm_insert_lookups_us: u128,
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

/// A newly-applied operation must always persist its output-seal membership for this pile.
/// Prewarm caches may already contain the same immutable definition (for example via a
/// contract-wide materialized lookup), but that proves byte equality only — not that this
/// wallet/pile owns a durable membership row. The eventual `add_seals` is idempotent.
fn output_seals_are_already_persisted(
    applied_new_operation: bool,
    all_definitions_cached: bool,
    durable_match: impl FnOnce() -> bool,
) -> bool {
    if applied_new_operation {
        false
    } else if all_definitions_cached {
        true
    } else {
        durable_match()
    }
}

/// Operation counts of the most recently completed consume on this thread.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LastConsumeOpCounts {
    pub decoded_ops: usize,
    pub known_ops: usize,
    pub new_ops: usize,
}

thread_local! {
    static LAST_CONSUME_OP_COUNTS: core::cell::Cell<LastConsumeOpCounts> =
        const { core::cell::Cell::new(LastConsumeOpCounts { decoded_ops: 0, known_ops: 0, new_ops: 0 }) };
}

/// Records the operation counts of the just-finished consume. Always updated,
/// independent of the slow-stage threshold that gates the `consume_evaluate`
/// log line, so a host wrapping consume with its own always-on timer can divide
/// by a population-coherent op count instead of borrowing the slow-gated one.
fn record_last_consume_op_counts(stats: &ConsumeStats) {
    LAST_CONSUME_OP_COUNTS.with(|c| {
        c.set(LastConsumeOpCounts {
            decoded_ops: stats.decoded_ops,
            known_ops: stats.known_ops,
            new_ops: stats.new_ops,
        })
    });
}

/// Returns and resets the operation counts recorded by the last consume on this
/// thread. Intended for host-side per-op telemetry normalization; read it
/// immediately after the consume call that produced it.
pub fn take_last_consume_op_counts() -> LastConsumeOpCounts {
    LAST_CONSUME_OP_COUNTS.with(|c| c.take())
}

/// Phase timing of the most recently completed consume on this thread. Values are populated only
/// when `RGB_VERIFY_DIAG` is enabled. The host must take them immediately after its consume call;
/// this preserves request correlation without a process-global map or any protocol-path state.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LastConsumePhaseStats {
    pub recorded: bool,
    pub verify_ms: u128,
    pub flush_witness_ms: u128,
    pub pending_witness_updates: usize,
    pub applied_witness_updates: usize,
    pub ledger_commit_ms: u128,
    pub pile_commit_ms: u128,
    pub prewarm_total_us: u128,
    pub prewarm_partition_us: u128,
    pub prewarm_known_duplicates_us: u128,
    pub prewarm_destructible_inputs_us: u128,
    pub prewarm_output_seals_us: u128,
    pub prewarm_witnesses_us: u128,
    pub prewarm_insert_lookups_us: u128,
}

thread_local! {
    static LAST_CONSUME_PHASE_STATS: core::cell::Cell<LastConsumePhaseStats> =
        const { core::cell::Cell::new(LastConsumePhaseStats {
            recorded: false,
            verify_ms: 0,
            flush_witness_ms: 0,
            pending_witness_updates: 0,
            applied_witness_updates: 0,
            ledger_commit_ms: 0,
            pile_commit_ms: 0,
            prewarm_total_us: 0,
            prewarm_partition_us: 0,
            prewarm_known_duplicates_us: 0,
            prewarm_destructible_inputs_us: 0,
            prewarm_output_seals_us: 0,
            prewarm_witnesses_us: 0,
            prewarm_insert_lookups_us: 0,
        }) };
}

/// Returns and resets the request-local consume phase timing recorded on this thread.
pub fn take_last_consume_phase_stats() -> LastConsumePhaseStats {
    LAST_CONSUME_PHASE_STATS.with(|stats| stats.take())
}

fn record_last_consume_prewarm_phase_stats(stats: &ConsumeStats) {
    LAST_CONSUME_PHASE_STATS.with(|last| {
        let mut phase = last.get();
        if phase.recorded {
            phase.prewarm_total_us = stats.prewarm_total_us;
            phase.prewarm_partition_us = stats.prewarm_partition_us;
            phase.prewarm_known_duplicates_us = stats.prewarm_known_duplicates_us;
            phase.prewarm_destructible_inputs_us = stats.prewarm_destructible_inputs_us;
            phase.prewarm_output_seals_us = stats.prewarm_output_seals_us;
            phase.prewarm_witnesses_us = stats.prewarm_witnesses_us;
            phase.prewarm_insert_lookups_us = stats.prewarm_insert_lookups_us;
            last.set(phase);
        }
    });
}

/// Accumulated per-phase wall time of the consign prewarm loop, reported with the
/// `consign_prewarm_operations` summary so its residual is attributable per phase.
#[derive(Default)]
struct ConsignPrewarmPhaseTimers {
    encode_us: u128,
    seals_us: u128,
    retrieve_us: u128,
    finish_us: u128,
}

struct SelectionPreloadPlan {
    opids: HashSet<Opid>,
    parent_ops: usize,
    parent_edges: usize,
}

impl SelectionPreloadPlan {
    fn from_parent_ops(
        parent_ops: HashMap<Opid, Vec<Opid>>,
        roots: impl IntoIterator<Item = Opid>,
        genesis_opid: Opid,
        known_opids: &HashSet<Opid>,
    ) -> Self {
        let parent_count = parent_ops.len();
        let parent_edges = parent_ops.values().map(Vec::len).sum::<usize>();
        // `known_opids` has already been filtered to operations for which every output CellAddr
        // is present in the receiver's exact known-cell set. It is therefore safe to stop the
        // preload graph there. Candidate opids without that proof never enter this set.
        let mut opids = HashSet::new();
        let mut stack = roots.into_iter().collect::<Vec<_>>();

        while let Some(opid) = stack.pop() {
            if opid == genesis_opid || known_opids.contains(&opid) || !opids.insert(opid) {
                continue;
            }

            let Some(parents) = parent_ops.get(&opid) else {
                continue;
            };

            for parent in parents {
                if *parent != genesis_opid && !opids.contains(parent) {
                    stack.push(*parent);
                }
            }
        }

        Self { opids, parent_ops: parent_count, parent_edges }
    }

    fn len(&self) -> usize { self.opids.len() }

    fn is_empty(&self) -> bool { self.opids.is_empty() }
}

/// Upper bound on opids per preload batch: operation blobs average tens of KB, so an
/// unchunked deep-wallet plan would pull hundreds of MB in a single response.
const SELECTION_PRELOAD_CHUNK: usize = 2000;

trait SelectionPreloadSession: StockSession {
    fn preload_selection_plan(&mut self, plan: &SelectionPreloadPlan) {
        if plan.is_empty() {
            return;
        }

        let opids = plan.opids.iter().copied().collect::<Vec<_>>();
        for chunk in opids.chunks(SELECTION_PRELOAD_CHUNK) {
            self.preload_operations(chunk.iter().copied());
            self.preload_transitions(chunk.iter().copied());
        }
    }
}

impl<T: StockSession> SelectionPreloadSession for T {}

struct ConsignmentSelectionBoundaries {
    known_cells: HashSet<CellAddr>,
    known_opids: HashSet<Opid>,
    immutable_checkpoint_opids: HashSet<Opid>,
    raw_known_opids: usize,
    raw_immutable_checkpoint_opids: usize,
    trust_known_opids: bool,
}

impl ConsignmentSelectionBoundaries {
    fn new(
        known_opids: HashSet<Opid>,
        known_cells: HashSet<CellAddr>,
        immutable_checkpoint_opids: HashSet<Opid>,
        trust_known_opids: bool,
    ) -> Self {
        Self {
            raw_known_opids: known_opids.len(),
            raw_immutable_checkpoint_opids: immutable_checkpoint_opids.len(),
            known_cells,
            known_opids,
            immutable_checkpoint_opids,
            trust_known_opids,
        }
    }

    fn filter_known_opids<S: Stock, P: Pile>(&mut self, contract: &mut Contract<S, P>)
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        if self.trust_known_opids && self.known_cells.is_empty() {
            self.known_opids.clear();
            self.immutable_checkpoint_opids.clear();
            return;
        }

        let known_opids = core::mem::take(&mut self.known_opids);
        self.known_opids = contract.known_boundary_opids_by_cells(known_opids, &self.known_cells);
        // Keep exact known cells after filtering opids: destructible dependencies may only stop
        // at an exact receiver-known CellAddr, never at an opid-only boundary.
    }

    fn prune_checkpoint_opids(&mut self, genesis_opid: Opid) {
        self.immutable_checkpoint_opids.remove(&genesis_opid);
        for opid in &self.known_opids {
            self.immutable_checkpoint_opids.remove(opid);
        }
    }

    fn skips_operation(&self, opid: &Opid) -> bool { self.known_opids.contains(opid) }

    fn skips_immutable_dependency(&self, opid: &Opid) -> bool {
        self.known_opids.contains(opid) || self.immutable_checkpoint_opids.contains(opid)
    }

    fn has_known_cells(&self, addr: &CellAddr) -> bool { self.known_cells.contains(addr) }

    fn skips_destructible_dependency(&self, addr: &CellAddr) -> bool { self.has_known_cells(addr) }
}

#[cfg(test)]
mod consignment_boundary_tests {
    use super::*;

    fn opid(byte: u8) -> Opid { Opid::from([byte; 32]) }

    #[test]
    fn new_operation_persists_seals_even_when_every_definition_is_prewarmed() {
        let durable_lookup_called = core::cell::Cell::new(false);
        let duplicate = output_seals_are_already_persisted(true, true, || {
            durable_lookup_called.set(true);
            true
        });

        assert!(!duplicate, "a cache hit is not proof of this pile's membership");
        assert!(
            !durable_lookup_called.get(),
            "new operations must take the idempotent add_seals path without a DB lookup"
        );
    }

    #[test]
    fn prewarm_phase_stats_merge_preserves_commit_fields_and_is_one_shot() {
        LAST_CONSUME_PHASE_STATS.with(|last| {
            last.set(LastConsumePhaseStats {
                recorded: true,
                verify_ms: 11,
                flush_witness_ms: 12,
                pending_witness_updates: 13,
                applied_witness_updates: 14,
                ledger_commit_ms: 15,
                pile_commit_ms: 16,
                ..LastConsumePhaseStats::default()
            })
        });
        let stats = ConsumeStats {
            prewarm_total_us: 101,
            prewarm_partition_us: 102,
            prewarm_known_duplicates_us: 103,
            prewarm_destructible_inputs_us: 104,
            prewarm_output_seals_us: 105,
            prewarm_witnesses_us: 106,
            prewarm_insert_lookups_us: 107,
            ..ConsumeStats::default()
        };

        record_last_consume_prewarm_phase_stats(&stats);

        assert_eq!(take_last_consume_phase_stats(), LastConsumePhaseStats {
            recorded: true,
            verify_ms: 11,
            flush_witness_ms: 12,
            pending_witness_updates: 13,
            applied_witness_updates: 14,
            ledger_commit_ms: 15,
            pile_commit_ms: 16,
            prewarm_total_us: 101,
            prewarm_partition_us: 102,
            prewarm_known_duplicates_us: 103,
            prewarm_destructible_inputs_us: 104,
            prewarm_output_seals_us: 105,
            prewarm_witnesses_us: 106,
            prewarm_insert_lookups_us: 107,
        });
        assert_eq!(
            take_last_consume_phase_stats(),
            LastConsumePhaseStats::default(),
            "taking request-local stats must reset them before the next consume"
        );
    }

    #[test]
    fn destructible_dependency_requires_exact_known_cell() {
        let producer = opid(1);
        let cell = CellAddr::new(producer, 3);
        let opid_only = ConsignmentSelectionBoundaries::new(
            HashSet::from([producer]),
            HashSet::new(),
            HashSet::new(),
            false,
        );
        let exact_cell = ConsignmentSelectionBoundaries::new(
            HashSet::new(),
            HashSet::from([cell]),
            HashSet::new(),
            false,
        );

        assert!(!opid_only.skips_destructible_dependency(&cell));
        assert!(exact_cell.skips_destructible_dependency(&cell));
    }

    #[test]
    fn selection_preload_stops_only_at_filtered_known_opid() {
        let genesis = opid(0);
        let old = opid(1);
        let known = opid(2);
        let root = opid(3);
        let parents =
            HashMap::from([(root, vec![known]), (known, vec![old]), (old, vec![genesis])]);

        let plan = SelectionPreloadPlan::from_parent_ops(
            parents,
            [root],
            genesis,
            &HashSet::from([known]),
        );

        assert!(plan.opids.contains(&root));
        assert!(!plan.opids.contains(&known));
        assert!(!plan.opids.contains(&old));
    }
}

impl<S: Stock, P: Pile> Contract<S, P> {
    fn prune_contract_caches(&mut self) {
        let max_entries = contract_cache_max_entries();
        prune_hashmap_to(&mut self.seal_def_cache, max_entries);
        prune_hashmap_to(&mut self.resolved_seal_cache, max_entries);
        prune_hashset_to(&mut self.duplicate_seal_def_cache, max_entries);
        prune_hashset_to(&mut self.duplicate_witness_cache, max_entries);
    }

    fn known_operation_aux_is_cached(
        &self,
        opid: Opid,
        operation_seals: &OperationSeals<P::Seal>,
    ) -> bool {
        let seals_cached = operation_seals.defined_seals.iter().all(|(no, seal)| {
            let addr = CellAddr::new(opid, *no);

            self.seal_def_cache
                .get(&addr)
                .is_some_and(|stored| stored == seal)
        });

        let witness_cached = operation_seals.witness.as_ref().is_none_or(|witness| {
            let wid = witness.published.pub_id();

            self.duplicate_witness_cache.contains(&(opid, wid))
        });

        seals_cached && witness_cached
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

    /// Incrementally update `valid_cache` after a `sync` rollback/forward instead of rebuilding
    /// the whole set from a full `valid_opids()` scan.
    ///
    /// `affected` must be the descendant closure of the directly-affected ops
    /// (`roll_back` ∪ `forward`), computed *before* the ledger rollback/forward so the
    /// read/spent indices still reflect the pre-sync graph. The ledger's `rollback`/`forward`
    /// operate over that descendant closure, so validity may have changed for any op in it, not
    /// just the seeds. We re-read the reconciled `valid_opids()` set from the ledger and update
    /// only those entries touched by the closure. This keeps the incremental path aligned with
    /// backends which repair or reconcile materialized valid-opid indexes inside `valid_opids()`
    /// instead of trusting a bare point `is_valid` lookup.
    fn apply_valid_cache_delta(&mut self, affected: HashSet<Opid>) {
        let valid_opids = self
            .ledger
            .with_session(|session| {
                Ok::<_, core::convert::Infallible>(
                    session.valid_opids().into_iter().collect::<HashSet<_>>(),
                )
            })
            .expect("infallible valid cache delta");
        for opid in affected {
            if valid_opids.contains(&opid) {
                self.valid_cache.insert(opid);
            } else {
                self.valid_cache.remove(&opid);
            }
        }
    }

    /// Single pass over the consignment operations computing each `opid()` exactly once.
    ///
    /// The result is split into the two prewarm cohorts: `known_ops` (already-valid ops whose
    /// duplicate aux caches are not yet warm) and `new_ops` (not-yet-valid ops needing
    /// insert-lookup prewarm). `opids` is returned in operation order so the caller can hand the
    /// already-computed commitments to `PredecodedOpReader` and let `verify` reuse them instead of
    /// recomputing `opid()` per op. Genesis is special-cased inside `verify` (its `contract_id` is
    /// rewritten there), so the genesis opid carried here is only a placeholder for that op.
    #[allow(clippy::type_complexity)]
    fn partition_consume_operations<'a>(
        &self,
        operations: &'a [OperationSeals<P::Seal>],
    ) -> (
        Vec<(Opid, &'a OperationSeals<P::Seal>)>,
        Vec<(Opid, &'a OperationSeals<P::Seal>)>,
        Vec<Opid>,
    ) {
        let classify_started_at = Instant::now();
        let mut known_ops = Vec::new();
        let mut new_ops = Vec::new();
        let mut opids = Vec::with_capacity(operations.len());
        let mut known_ops_total = 0usize;
        let mut known_cached_ops = 0usize;
        for op in operations {
            let opid = op.operation.opid();
            opids.push(opid);
            if self.valid_cache.contains(&opid) {
                known_ops_total += 1;
                if self.known_operation_aux_is_cached(opid, op) {
                    known_cached_ops += 1;
                } else {
                    known_ops.push((opid, op));
                }
            } else {
                new_ops.push((opid, op));
            }
        }
        let classify_ms = classify_started_at.elapsed().as_millis() as u64;
        tracing::warn!(
            target: "rgb_prewarm_diag",
            operation = "rgb_std",
            stage = "consume_prewarm_partition",
            contract_id = ?self.contract_id,
            operations_total = operations.len(),
            known_ops_total,
            known_cached_ops,
            known_ops = known_ops.len(),
            new_ops = new_ops.len(),
            classify_ms,
            "consume prewarm single-pass opid partition"
        );
        (known_ops, new_ops, opids)
    }

    fn prewarm_known_operation_duplicate_caches(
        &mut self,
        operations_total: usize,
        known_ops: Vec<(Opid, &OperationSeals<P::Seal>)>,
    ) {
        if known_ops.is_empty() {
            return;
        }

        let total_started_at = Instant::now();
        let aux_match_started_at = Instant::now();
        let mut session = self.pile.session();
        let aux_matches = session.known_operation_aux_matches(&known_ops);
        drop(session);
        let aux_match_ms = aux_match_started_at.elapsed().as_millis() as u64;
        let aux_match_seals = aux_matches.seal_definitions.len();
        let aux_match_witnesses = aux_matches.witnesses.len();

        let cache_apply_started_at = Instant::now();
        for (addr, seal) in aux_matches.seal_definitions {
            // Non-evicting backstop so `are_seals_known` still resolves after the bounded
            // `seal_def_cache` gets pruned mid-consume (deep all-known closures otherwise re-issue
            // ~5k per-op `seal_definitions_match` DB round-trips ≈ 168s).
            self.consume_seal_defs.insert(addr, seal.clone());
            self.seal_def_cache.insert(addr, seal);
            self.duplicate_seal_def_cache.insert(addr);
        }

        for (opid, wid) in aux_matches.witnesses {
            self.duplicate_witness_cache.insert((opid, wid));
        }
        let cache_apply_ms = cache_apply_started_at.elapsed().as_millis() as u64;

        let prune_started_at = Instant::now();
        self.prune_contract_caches();
        let prune_ms = prune_started_at.elapsed().as_millis() as u64;

        tracing::warn!(
            target: "rgb_prewarm_diag",
            operation = "rgb_std",
            stage = "known_operation_duplicate_prewarm",
            contract_id = ?self.contract_id,
            operations_total,
            aux_match_ops = known_ops.len(),
            aux_match_seals,
            aux_match_witnesses,
            aux_match_ms,
            cache_apply_ms,
            prune_ms,
            total_ms = total_started_at.elapsed().as_millis() as u64,
            "known operation duplicate prewarm breakdown"
        );
    }

    fn preload_destructible_input_seals(&mut self, operations: &[OperationSeals<P::Seal>]) {
        let total_started_at = Instant::now();
        let collect_started_at = Instant::now();
        let cells = operations
            .iter()
            .flat_map(|operation_seals| {
                operation_seals
                    .operation
                    .destructible_in
                    .iter()
                    .map(|input| input.addr)
            })
            .collect::<BTreeSet<_>>();
        let collect_ms = collect_started_at.elapsed().as_millis() as u64;
        if cells.is_empty() {
            tracing::warn!(
                target: "rgb_prewarm_diag",
                operation = "rgb_std",
                stage = "preload_destructible_input_seals",
                contract_id = ?self.contract_id,
                operations_total = operations.len(),
                cells = 0usize,
                collect_ms,
                preload_ms = 0u64,
                total_ms = total_started_at.elapsed().as_millis() as u64,
                "destructible input seal preload breakdown"
            );
            return;
        }

        let cells_len = cells.len();
        let preload_started_at = Instant::now();
        // `seals_for` batch-loads the definitions (and warms the pile cache) like `preload_seals`,
        // but also returns them so they can land in the non-evicting `consume_seal_defs` backstop.
        // That keeps `known_seal` resolving input-cell seals from memory even after the bounded
        // `seal_def_cache` evicts them during a deep closure (otherwise ~5k per-cell DB ≈ 152s).
        let loaded = self.pile.session().seals_for(cells.iter().copied());
        for (addr, seal) in loaded {
            self.consume_seal_defs.insert(addr, seal);
        }
        let preload_ms = preload_started_at.elapsed().as_millis() as u64;

        tracing::warn!(
            target: "rgb_prewarm_diag",
            operation = "rgb_std",
            stage = "preload_destructible_input_seals",
            contract_id = ?self.contract_id,
            operations_total = operations.len(),
            cells = cells_len,
            collect_ms,
            preload_ms,
            total_ms = total_started_at.elapsed().as_millis() as u64,
            "destructible input seal preload breakdown"
        );
    }

    /// Batch-preload the new cohort's witness ids into the pile witness existence cache. This
    /// deliberately only targets `has_witness`; the reverse `ops_by_witness_id` path stays lazy
    /// until measurements show it is worth a separate batch cache.
    fn preload_consume_witnesses(&mut self, new_operations: &[(Opid, &OperationSeals<P::Seal>)]) {
        if new_operations.is_empty() {
            return;
        }
        let total_started_at = Instant::now();
        let collect_started_at = Instant::now();
        let witness_ids = new_operations
            .iter()
            .filter_map(|(_, operation_seals)| {
                operation_seals
                    .witness
                    .as_ref()
                    .map(|witness| witness.published.pub_id())
            })
            .collect::<BTreeSet<_>>();
        let collect_ms = collect_started_at.elapsed().as_millis() as u64;
        if witness_ids.is_empty() {
            return;
        }

        let witness_ids_len = witness_ids.len();
        let preload_started_at = Instant::now();
        self.pile.session().preload_consume_witnesses(witness_ids);
        let preload_ms = preload_started_at.elapsed().as_millis() as u64;

        tracing::warn!(
            target: "rgb_prewarm_diag",
            operation = "rgb_std",
            stage = "preload_consume_witnesses",
            contract_id = ?self.contract_id,
            new_ops = new_operations.len(),
            witness_ids = witness_ids_len,
            collect_ms,
            preload_ms,
            total_ms = total_started_at.elapsed().as_millis() as u64,
            "apply-path witness preload breakdown"
        );
    }

    fn preload_consume_insert_lookups(
        &mut self,
        operations_total: usize,
        new_operations: Vec<(Opid, &OperationSeals<P::Seal>)>,
    ) {
        if new_operations.is_empty() {
            return;
        }
        let total_started_at = Instant::now();
        let new_ops = new_operations.len();

        let ledger_preload_started_at = Instant::now();
        self.ledger
            .preload_apply_insert_lookups(new_operations.iter().map(|(_, op)| &op.operation));
        let ledger_preload_ms = ledger_preload_started_at.elapsed().as_millis() as u64;

        let pile_preload_started_at = Instant::now();
        self.pile
            .session()
            .preload_consume_insert_lookups(new_operations.into_iter().map(|(_, op)| op));
        let pile_preload_ms = pile_preload_started_at.elapsed().as_millis() as u64;

        tracing::warn!(
            target: "rgb_prewarm_diag",
            operation = "rgb_std",
            stage = "preload_consume_insert_lookups",
            contract_id = ?self.contract_id,
            operations_total,
            new_ops,
            ledger_preload_ms,
            pile_preload_ms,
            total_ms = total_started_at.elapsed().as_millis() as u64,
            "consume insert lookup preload breakdown"
        );
    }

    fn clear_owned_state_status_cache(&mut self) { self.owned_state_status_cache.clear(); }

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
        let parent_ops: BTreeMap<Opid, Vec<Opid>> =
            self.ledger.operation_parent_ops().into_iter().collect();

        if parent_ops.len() > OWNED_STATE_STATUS_CACHE_MAX_OPS {
            return;
        }

        let mut op_witness_ids = BTreeMap::new();
        let mut witness_statuses = BTreeMap::new();
        {
            let mut session = self.pile.session();
            let mut witness_ids = BTreeSet::new();
            let opids = parent_ops
                .keys()
                .copied()
                .chain([genesis_opid])
                .collect::<Vec<_>>();
            for (opid, wids) in session.op_witness_ids_for(opids) {
                for wid in &wids {
                    witness_ids.insert(*wid);
                    if witness_ids.len() > OWNED_STATE_STATUS_CACHE_MAX_WITNESSES {
                        return;
                    }
                }
                op_witness_ids.insert(opid, wids);
            }
            for (wid, status) in session.witness_statuses_for(witness_ids) {
                witness_statuses.insert(wid, status);
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

    fn owned_state_status_context(
        &mut self,
    ) -> OwnedStateStatusContext<<P::Seal as RgbSeal>::WitnessId>
    where <P::Seal as RgbSeal>::WitnessId: Copy + Ord {
        let mut cache = core::mem::take(&mut self.owned_state_status_cache);
        self.ensure_owned_state_status_cache(&mut cache);
        let genesis_opid;
        let parent_ops;
        if let Some(cached_genesis_opid) = cache.genesis_opid {
            genesis_opid = cached_genesis_opid;
            parent_ops = core::mem::take(&mut cache.parent_ops);
        } else {
            genesis_opid = self.ledger.articles().genesis_opid();
            parent_ops = self.ledger.operation_parent_ops().into_iter().collect();
        }

        OwnedStateStatusContext {
            genesis_opid,
            parent_ops,
            op_witness_ids: core::mem::take(&mut cache.op_witness_ids),
            witness_statuses: core::mem::take(&mut cache.witness_statuses),
            best_statuses: core::mem::take(&mut cache.best_statuses),
            ancestor_statuses: core::mem::take(&mut cache.ancestor_statuses),
            cache,
        }
    }

    fn owned_state_status_from_context(
        &mut self,
        opid: Opid,
        direct: WitnessStatus,
        context: &mut OwnedStateStatusContext<<P::Seal as RgbSeal>::WitnessId>,
    ) -> WitnessStatus
    where
        <P::Seal as RgbSeal>::WitnessId: Copy + Ord,
    {
        self.ancestor_status_cached(
            opid,
            context.genesis_opid,
            &context.parent_ops,
            &mut context.op_witness_ids,
            &mut context.witness_statuses,
            &mut context.best_statuses,
            &mut context.ancestor_statuses,
        )
        .worst(direct)
    }

    fn restore_owned_state_status_context(
        &mut self,
        mut context: OwnedStateStatusContext<<P::Seal as RgbSeal>::WitnessId>,
    ) {
        if context.cache.genesis_opid.is_some() {
            context.cache.parent_ops = context.parent_ops;
            context.cache.op_witness_ids = context.op_witness_ids;
            context.cache.witness_statuses = context.witness_statuses;
            context.cache.best_statuses = context.best_statuses;
            context.cache.ancestor_statuses = context.ancestor_statuses;
            context.cache.touched_at = Instant::now();
            self.owned_state_status_cache = context.cache;
        }
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
            genesis_verification_memory: GenesisVerificationMemory::default(),
            known_verification_memory: GenesisVerificationMemory::default(),
            genesis_verification_memory_staged_for: None,
            valid_cache: HashSet::from([genesis_opid]),
            applied_new_ops: HashSet::new(),
            consume_seal_defs: HashMap::new(),
            seal_def_cache: HashMap::new(),
            resolved_seal_cache: HashMap::new(),
            external_seal_def_cache: Arc::new(HashMap::new()),
            external_resolved_seal_cache: Arc::new(HashMap::new()),
            duplicate_seal_def_cache: HashSet::new(),
            duplicate_witness_cache: HashSet::new(),
            pending_witness_updates: PendingWitnessUpdates::default(),
            op_aux_cache: HashMap::new(),
            op_aux_cache_order: BTreeMap::new(),
            op_aux_cache_positions: HashMap::new(),
            op_aux_cache_next_seq: 0,
            op_aux_cache_bytes: 0,
            owned_state_status_cache: OwnedStateStatusCache::default(),
        };
        let genesis_operation = contract.contract_genesis_operation();
        contract.stage_genesis_verification_memory(&genesis_operation);
        let evaluate_result = contract.evaluate_commit(consignment.into_operations());
        evaluate_result.map_err(MultiError::from_a)?;

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
            genesis_verification_memory: GenesisVerificationMemory::default(),
            known_verification_memory: GenesisVerificationMemory::default(),
            genesis_verification_memory_staged_for: None,
            valid_cache: HashSet::from([genesis_opid]),
            applied_new_ops: HashSet::new(),
            consume_seal_defs: HashMap::new(),
            seal_def_cache: HashMap::new(),
            resolved_seal_cache: HashMap::new(),
            external_seal_def_cache: Arc::new(HashMap::new()),
            external_resolved_seal_cache: Arc::new(HashMap::new()),
            duplicate_seal_def_cache: HashSet::new(),
            duplicate_witness_cache: HashSet::new(),
            pending_witness_updates: PendingWitnessUpdates::default(),
            op_aux_cache: HashMap::new(),
            op_aux_cache_order: BTreeMap::new(),
            op_aux_cache_positions: HashMap::new(),
            op_aux_cache_next_seq: 0,
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
            genesis_verification_memory: GenesisVerificationMemory::default(),
            known_verification_memory: GenesisVerificationMemory::default(),
            genesis_verification_memory_staged_for: None,
            valid_cache: HashSet::new(),
            applied_new_ops: HashSet::new(),
            consume_seal_defs: HashMap::new(),
            seal_def_cache: HashMap::new(),
            resolved_seal_cache: HashMap::new(),
            external_seal_def_cache: Arc::new(HashMap::new()),
            external_resolved_seal_cache: Arc::new(HashMap::new()),
            duplicate_seal_def_cache: HashSet::new(),
            duplicate_witness_cache: HashSet::new(),
            pending_witness_updates: PendingWitnessUpdates::default(),
            op_aux_cache: HashMap::new(),
            op_aux_cache_order: BTreeMap::new(),
            op_aux_cache_positions: HashMap::new(),
            op_aux_cache_next_seq: 0,
            op_aux_cache_bytes: 0,
            owned_state_status_cache: OwnedStateStatusCache::default(),
        };
        contract.refresh_valid_cache();
        Ok(contract)
    }

    pub fn contract_id(&self) -> ContractId { self.contract_id }
    pub fn articles(&self) -> &Articles { self.ledger.articles() }
    pub fn full_state(&self) -> &EffectiveState { self.ledger.state() }

    pub fn raw_owned_state_cell(&self, addr: CellAddr) -> Option<(StateName, StrictVal)> {
        let cell = self.ledger.state().raw.owned.get(&addr)?;
        self.ledger
            .articles()
            .default_api()
            .convert_owned(cell.data, self.ledger.articles().types())
            .ok()
            .flatten()
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
                .or_insert_with(|| self.pile.session().op_witness_ids(opid));
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
        if let Some(status) = ancestor_cache.get(&start).copied() {
            return status;
        }

        let mut stack = vec![(start, false)];
        let mut visiting = HashSet::new();
        while let Some((opid, expanded)) = stack.pop() {
            if ancestor_cache.contains_key(&opid) {
                continue;
            }

            if expanded {
                visiting.remove(&opid);
                let mut status = self.best_op_status_cached(
                    opid,
                    op_witness_ids_cache,
                    witness_status_cache,
                    best_status_cache,
                );
                if opid != genesis_opid {
                    if let Some(parents) = parent_ops.get(&opid) {
                        for parent in parents {
                            if let Some(parent_status) = ancestor_cache.get(parent).copied() {
                                status = status.worst(parent_status);
                            }
                        }
                    }
                }
                ancestor_cache.insert(opid, status);
                continue;
            }

            if !visiting.insert(opid) {
                // RGB operation ancestry is expected to be a DAG. If a malformed graph ever
                // exposes a cycle, avoid looping forever and keep the direct op status.
                let status = self.best_op_status_cached(
                    opid,
                    op_witness_ids_cache,
                    witness_status_cache,
                    best_status_cache,
                );
                ancestor_cache.entry(opid).or_insert(status);
                continue;
            }

            stack.push((opid, true));
            if opid != genesis_opid {
                if let Some(parents) = parent_ops.get(&opid) {
                    for parent in parents.iter().rev().copied() {
                        if !ancestor_cache.contains_key(&parent) {
                            stack.push((parent, false));
                        }
                    }
                }
            }
        }

        ancestor_cache
            .get(&start)
            .copied()
            .unwrap_or(WitnessStatus::Genesis)
    }

    fn retrieve_with_session<PS>(ps: &mut PS, opid: Opid) -> Option<SealWitness<P::Seal>>
    where PS: PileSession<Seal = P::Seal> {
        let wids = ps.op_witness_ids(opid);
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

    pub fn trace_ops(&mut self) -> Vec<(Opid, Transition)> { self.ledger.trace_iter().collect() }

    pub fn known_seal_cells(&mut self) -> Vec<CellAddr> { self.pile.session().known_seal_cells() }

    pub fn known_resolved_seals(&mut self) -> Vec<(CellAddr, P::Seal)> {
        let cells = self.known_seal_cells();
        let definitions = self.pile.session().seals_for(cells);
        let mut resolved = Vec::with_capacity(definitions.len());
        for (addr, definition) in definitions {
            self.seal_def_cache.insert(addr, definition.clone());
            if let Some(seal) = definition.to_src() {
                self.resolved_seal_cache.insert(addr, seal.clone());
                resolved.push((addr, seal));
                continue;
            }
            if let Some(witness) = self.retrieve(addr.opid) {
                let seal = definition.resolve(witness.published.pub_id());
                self.resolved_seal_cache.insert(addr, seal.clone());
                resolved.push((addr, seal));
            }
        }
        self.prune_contract_caches();
        resolved
    }

    /// Stable known-seal cells whose seal can be resolved by this wallet.
    ///
    /// A cell only holds a seal *definition* in the pile; a witness-resolved (destructible)
    /// definition additionally needs its producing operation's witness to be present and mined
    /// before it can be used as a pruning boundary. Reporting a definition-only or unconfirmed
    /// cell as a receiver-known boundary
    /// lets the payer prune the producer from the consignment, after which the receiver cannot
    /// resolve the seal and accept fails with `SealUnknown`. This is stricter than `known_seal`:
    /// direct seals are accepted immediately, while witness-resolved seals require a stable
    /// Genesis/Mined producer. It batches the witness lookups and at worst omits a
    /// resolvable cell, which only makes the consignment larger, never unsound.
    pub fn known_resolvable_seal_cells(&mut self) -> Vec<CellAddr>
    where <P::Seal as RgbSeal>::WitnessId: Copy + Ord {
        let cells = self.known_seal_cells();
        let definitions = self.pile.session().seals_for(cells);
        let mut resolvable = Vec::with_capacity(definitions.len());
        let mut witness_needed: Vec<(CellAddr, Opid)> = Vec::new();
        for (addr, definition) in definitions {
            if definition.to_src().is_some() {
                resolvable.push(addr);
            } else {
                witness_needed.push((addr, addr.opid));
            }
        }
        if witness_needed.is_empty() {
            return resolvable;
        }

        let opids = witness_needed
            .iter()
            .map(|(_, opid)| *opid)
            .collect::<BTreeSet<_>>();
        let mut session = self.pile.session();
        let op_wids = session
            .op_witness_ids_for(opids.into_iter())
            .into_iter()
            .collect::<BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>>>();
        let all_wids = op_wids.values().flatten().copied().collect::<BTreeSet<_>>();
        let statuses = session
            .witness_statuses_for(all_wids.into_iter())
            .into_iter()
            .collect::<BTreeMap<<P::Seal as RgbSeal>::WitnessId, WitnessStatus>>();

        // Diagnostics: how the witness-resolved cells were classified. A cell reported as a
        // boundary on the strength of a *tentative/offchain* producer witness is fragile — that
        // witness can be archived before the receiver accepts, reproducing SealUnknown. The
        // unconfirmed sample lets the next round correlate a failing cell against the witness
        // status the gate saw at pay time.
        let to_src_count = resolvable.len();
        let mut witness_stable = 0usize;
        let mut witness_unconfirmed = 0usize;
        let mut excluded = 0usize;
        let mut unconfirmed_sample: Vec<(Opid, WitnessStatus)> = Vec::new();
        for (addr, opid) in witness_needed {
            // Pick the best-status witness for the producing operation, then require it to be
            // stable before advertising the cell as a pruning boundary.
            let best = op_wids
                .get(&opid)
                .into_iter()
                .flatten()
                .filter_map(|wid| statuses.get(wid).copied().map(|status| (status, *wid)))
                .reduce(|best, other| if best.0.is_better(other.0) { best } else { other });
            match best {
                Some((status, _))
                    if status.is_mined() || matches!(status, WitnessStatus::Genesis) =>
                {
                    resolvable.push(addr);
                    witness_stable += 1;
                }
                Some((status, _)) if status.is_valid() => {
                    // A tentative/offchain producer can be archived between pay and accept. Do
                    // not advertise its cells as pruning boundaries: including extra history is
                    // safe, while pruning here can leave the receiver unable to resolve the seal.
                    witness_unconfirmed += 1;
                    excluded += 1;
                    if unconfirmed_sample.len() < 8 {
                        unconfirmed_sample.push((opid, status));
                    }
                }
                _ => excluded += 1,
            }
        }
        tracing::debug!(
            target: "rgb_boundary_diag",
            operation = "rgb_std",
            stage = "known_resolvable_seal_cells",
            contract_id = ?self.contract_id,
            total_cells = resolvable.len() + excluded,
            to_src_cells = to_src_count,
            witness_stable_cells = witness_stable,
            witness_unconfirmed_cells = witness_unconfirmed,
            excluded_cells = excluded,
            unconfirmed_sample = ?unconfirmed_sample,
            "receiver known-cell resolvability breakdown"
        );
        resolvable
    }

    pub fn valid_opids(&mut self) -> Vec<Opid> {
        self.refresh_valid_cache();
        self.valid_cache.iter().copied().collect()
    }

    pub fn operation_output_counts(&mut self) -> Vec<(Opid, u16)> {
        self.ledger.operation_output_counts()
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
            .into_iter()
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
            .into_iter()
            .filter_map(|(opid, count)| {
                let known_positions = known_positions_by_opid.get(&opid)?;
                (known_positions.len() == count as usize
                    && (0..count).all(|pos| known_positions.contains(&pos)))
                .then_some(opid)
            })
            .collect()
    }

    pub fn witness_ids(&mut self) -> Vec<<P::Seal as RgbSeal>::WitnessId> {
        self.pile.session().witness_ids()
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

    pub fn witnesses(&mut self) -> Vec<Witness<P::Seal>> { self.pile.session().witnesses() }

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
        self.pile.session().ops_by_witness_id(wid)
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

    pub fn resolved_owned_state_entries_for_cells(
        &mut self,
        name: &StateName,
        cells: impl IntoIterator<Item = CellAddr>,
    ) -> Vec<OwnedState<P::Seal>>
    where
        P::Seal: Clone,
    {
        let phase_started_at = Instant::now();
        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_for_cells_entered",
            contract_id = ?self.contract_id,
            "resolved_owned_state_entries_for_cells entered"
        );
        let Some(states) = self.ledger.state().main.owned.get(name) else {
            return vec![];
        };

        let mut selected = Vec::new();
        let mut unresolved = Vec::new();
        {
            // Batch the seal and witness-id reads for the candidate cells: the per-cell
            // lazy path costs one DB round-trip per cell (two for absent cells, which the
            // shared cache refuses to negatively cache), and this resolver runs on every
            // balance/coinselect load.
            let mut session = self.pile.session();
            let candidate_cells = cells
                .into_iter()
                .filter(|addr| states.contains_key(addr))
                .collect::<Vec<_>>();
            let seals_by_cell = session
                .seals_for(candidate_cells.iter().copied())
                .into_iter()
                .collect::<BTreeMap<_, _>>();
            let unresolved_opids = candidate_cells
                .iter()
                .filter(|addr| {
                    seals_by_cell
                        .get(*addr)
                        .is_some_and(|seal| seal.to_src().is_none())
                })
                .map(|addr| addr.opid)
                .collect::<BTreeSet<_>>();
            let mut op_wids: BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>> = BTreeMap::new();
            if !unresolved_opids.is_empty() {
                op_wids = session
                    .op_witness_ids_for(unresolved_opids.into_iter())
                    .into_iter()
                    .collect();
            }
            for addr in candidate_cells {
                let Some(data) = states.get(&addr).cloned() else {
                    continue;
                };
                let Some(seal) = seals_by_cell.get(&addr).cloned() else {
                    continue;
                };
                if let Some(seal_src) = seal.to_src() {
                    selected.push((addr, seal_src, data));
                } else {
                    let wids = op_wids.get(&addr.opid).cloned().unwrap_or_default();
                    unresolved.push((addr, seal, data, wids));
                }
            }
        }

        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_for_cells_seals_resolved",
            contract_id = ?self.contract_id,
            selected = selected.len(),
            unresolved = unresolved.len(),
            elapsed_ms = phase_started_at.elapsed().as_millis() as u64,
            "owned-state cell seal resolution finished"
        );
        if selected.is_empty() && unresolved.is_empty() {
            return vec![];
        }

        let mut status_cache = core::mem::take(&mut self.owned_state_status_cache);
        self.ensure_owned_state_status_cache(&mut status_cache);
        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_for_cells_status_cache_ready",
            contract_id = ?self.contract_id,
            cache_warm = status_cache.genesis_opid.is_some(),
            cached_parent_ops = status_cache.parent_ops.len(),
            cached_witness_statuses = status_cache.witness_statuses.len(),
            elapsed_ms = phase_started_at.elapsed().as_millis() as u64,
            "owned-state status cache prewarm finished"
        );
        let fallback_parent_ops;
        let (genesis_opid, parent_ops) = if let Some(genesis_opid) = status_cache.genesis_opid {
            (genesis_opid, &status_cache.parent_ops)
        } else {
            let genesis_opid = self.ledger.articles().genesis_opid();
            fallback_parent_ops = self.ledger.operation_parent_ops().into_iter().collect();
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
                    assignment: Assignment { seal: seal.resolve(wid), data: data.clone() },
                    status,
                });
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

        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_for_cells_done",
            contract_id = ?self.contract_id,
            entries = result.len(),
            elapsed_ms = phase_started_at.elapsed().as_millis() as u64,
            "resolved_owned_state_entries_for_cells finished"
        );
        result
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
        let phase_started_at = Instant::now();
        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_filtered_take_entered",
            contract_id = ?self.contract_id,
            limit = ?limit,
            "resolved_owned_state_entries_filtered_take entered"
        );
        let Some(states) = self.ledger.state().main.owned.get(name) else {
            return vec![];
        };

        let state_entries = states
            .iter()
            .map(|(addr, data)| (*addr, data.clone()))
            .collect::<Vec<_>>();

        // Full-stock traversal: take one batched snapshot of the present seal definitions and
        // the unresolved ops' witness ids up front. Per-cell lazy reads over the whole stock
        // are per-op DB round-trips that grind for minutes on cross-region deployments — and a
        // positive-only cache prewarm still pays them for every absent cell, so the loop below
        // reads exclusively from the local snapshot (absent cells are simply not in it).
        let mut op_wids: BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>> = BTreeMap::new();
        let seals_by_cell: BTreeMap<CellAddr, <P::Seal as RgbSeal>::Definition> = {
            let mut session = self.pile.session();
            let seals_by_cell = session
                .seals_for(state_entries.iter().map(|(addr, _)| *addr))
                .into_iter()
                .collect::<BTreeMap<_, _>>();
            let mut unresolved_opids = BTreeSet::new();
            for (addr, _) in &state_entries {
                let Some(seal) = seals_by_cell.get(addr) else {
                    continue;
                };
                if seal.to_src().is_none() {
                    unresolved_opids.insert(addr.opid);
                }
            }
            if !unresolved_opids.is_empty() {
                op_wids = session
                    .op_witness_ids_for(unresolved_opids.into_iter())
                    .into_iter()
                    .collect();
            }
            seals_by_cell
        };
        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_filtered_take_prepared",
            contract_id = ?self.contract_id,
            cells = state_entries.len(),
            present = seals_by_cell.len(),
            unresolved_ops = op_wids.len(),
            elapsed_ms = phase_started_at.elapsed().as_millis() as u64,
            "owned-state stock traversal snapshot prepared"
        );

        let mut status_context = None;
        let mut result = Vec::new();
        'state: for (addr, data) in state_entries {
            let Some(seal) = seals_by_cell.get(&addr).cloned() else {
                continue;
            };
            if let Some(seal_src) = seal.to_src() {
                if !predicate(&seal_src) {
                    continue;
                }
                if status_context.is_none() {
                    status_context = Some(self.owned_state_status_context());
                }
                let context = status_context
                    .as_mut()
                    .expect("owned state status context initialized");
                let direct = self.best_op_status_cached(
                    addr.opid,
                    &mut context.op_witness_ids,
                    &mut context.witness_statuses,
                    &mut context.best_statuses,
                );
                let status = self.owned_state_status_from_context(addr.opid, direct, context);
                result.push(OwnedState {
                    addr,
                    assignment: Assignment { seal: seal_src, data },
                    status,
                });
                if limit.is_some_and(|limit| result.len() >= limit) {
                    break;
                }
                continue;
            }

            let wids = op_wids.get(&addr.opid).cloned().unwrap_or_default();
            for wid in wids {
                let seal = seal.resolve(wid);
                if !predicate(&seal) {
                    continue;
                }
                if status_context.is_none() {
                    status_context = Some(self.owned_state_status_context());
                }
                let context = status_context
                    .as_mut()
                    .expect("owned state status context initialized");
                let direct = *context
                    .witness_statuses
                    .entry(wid)
                    .or_insert_with(|| self.pile.session().witness_status(wid));
                let status = self.owned_state_status_from_context(addr.opid, direct, context);
                result.push(OwnedState {
                    addr,
                    assignment: Assignment { seal, data: data.clone() },
                    status,
                });
                if limit.is_some_and(|limit| result.len() >= limit) {
                    break 'state;
                }
            }
        }

        if let Some(status_context) = status_context {
            self.restore_owned_state_status_context(status_context);
        }

        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_state_filtered_take_done",
            contract_id = ?self.contract_id,
            entries = result.len(),
            elapsed_ms = phase_started_at.elapsed().as_millis() as u64,
            "resolved_owned_state_entries_filtered_take finished"
        );
        result
    }

    pub fn state(&mut self) -> ContractState<P::Seal> {
        let main = self.ledger.state().main.clone();

        let mut status_cache = core::mem::take(&mut self.owned_state_status_cache);
        self.ensure_owned_state_status_cache(&mut status_cache);
        let fallback_parent_ops;
        let (genesis_opid, parent_ops) = if let Some(genesis_opid) = status_cache.genesis_opid {
            (genesis_opid, &status_cache.parent_ops)
        } else {
            let genesis_opid = self.ledger.articles().genesis_opid();
            fallback_parent_ops = self.ledger.operation_parent_ops().into_iter().collect();
            (genesis_opid, &fallback_parent_ops)
        };
        let mut op_witness_ids_cache = core::mem::take(&mut status_cache.op_witness_ids);
        let mut witness_status_cache = core::mem::take(&mut status_cache.witness_statuses);
        let mut best_status_cache = core::mem::take(&mut status_cache.best_statuses);
        let mut ancestor_cache = core::mem::take(&mut status_cache.ancestor_statuses);

        let mut owned = BTreeMap::new();
        for (name, map) in main.owned {
            let mut state = vec![];
            for (addr, data) in map {
                let Some(seal) = self.pile.session().seal(addr) else {
                    continue;
                };
                if let Some(seal_src) = seal.to_src() {
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
                    state.push(OwnedState {
                        addr,
                        assignment: Assignment { seal: seal_src, data },
                        status,
                    });
                } else {
                    let wids = op_witness_ids_cache
                        .entry(addr.opid)
                        .or_insert_with(|| self.pile.session().op_witness_ids(addr.opid))
                        .clone();
                    for wid in wids {
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
                state.push(ImmutableState { addr, data, status });
            }
            immutable.insert(name, state);
        }
        if status_cache.genesis_opid.is_some() {
            status_cache.op_witness_ids = op_witness_ids_cache;
            status_cache.witness_statuses = witness_status_cache;
            status_cache.best_statuses = best_status_cache;
            status_cache.ancestor_statuses = ancestor_cache;
            status_cache.touched_at = Instant::now();
            self.owned_state_status_cache = status_cache;
        }
        ContractState { immutable, owned, aggregated: main.aggregated }
    }

    /// Returns the resolved single-use seal for every owned-state cell whose seal definition is
    /// known to this wallet's pile, across all owned state names.
    ///
    /// This is the cheap "which seals carry RGB state" primitive: it batch-loads the seal
    /// definitions (`seals_for`) and the witness ids of witness-relative definitions
    /// (`op_witness_ids_for`) in two snapshot queries and performs no witness-status or
    /// ancestor-status resolution at all. Callers needing per-cell status must use
    /// [`Self::state`] or the resolved owned-state entry APIs instead.
    ///
    /// Seal membership matches [`Self::state`]: cells whose seal definition is unknown to the
    /// pile are skipped, and a witness-relative definition is expanded once per known witness id.
    pub fn owned_seals(&mut self) -> Vec<P::Seal>
    where P::Seal: Clone {
        let phase_started_at = Instant::now();
        let mut addrs = self
            .ledger
            .state()
            .main
            .owned
            .values()
            .flat_map(|cells| cells.keys().copied())
            .collect::<Vec<_>>();
        addrs.sort_unstable();
        addrs.dedup();
        let cells = addrs.len();

        let mut session = self.pile.session();
        let seals_by_cell = session.seals_for(addrs.into_iter());
        let unresolved_opids = seals_by_cell
            .iter()
            .filter(|(_, seal)| seal.to_src().is_none())
            .map(|(addr, _)| addr.opid)
            .collect::<BTreeSet<_>>();
        let mut op_wids: BTreeMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>> = BTreeMap::new();
        if !unresolved_opids.is_empty() {
            op_wids = session
                .op_witness_ids_for(unresolved_opids.into_iter())
                .into_iter()
                .collect();
        }

        let mut result = Vec::with_capacity(seals_by_cell.len());
        for (addr, seal) in seals_by_cell {
            if let Some(seal_src) = seal.to_src() {
                result.push(seal_src);
            } else {
                for wid in op_wids.get(&addr.opid).into_iter().flatten() {
                    result.push(seal.resolve(*wid));
                }
            }
        }
        tracing::warn!(
            target: "rgb_owned_state_diag",
            operation = "rgb_std",
            stage = "owned_seals_done",
            contract_id = ?self.contract_id,
            cells,
            resolved = result.len(),
            unresolved_ops = op_wids.len(),
            elapsed_ms = phase_started_at.elapsed().as_millis() as u64,
            "owned_seals batched traversal finished"
        );
        result
    }

    pub fn sync(
        &mut self,
        changed: impl IntoIterator<Item = (<P::Seal as RgbSeal>::WitnessId, WitnessStatus)>,
    ) -> Result<(), MultiError<AcceptError, S::Error>> {
        // Batch-prewarm the pile-shared witness caches (hoard -> has_witness, stand ->
        // ops_by_witness_id) and resolve every status up front, so the per-witness reads below
        // hit memory instead of ~4 DB round-trips each. In replay (no mining) unconfirmed
        // witnesses accumulate unboundedly; a cache-miss balance refresh surfaced >1500 witnesses
        // here, ~54s of per-witness round-trips that timed out the 60s balance endpoint.
        let changed = changed.into_iter().collect::<Vec<_>>();
        let changed_wids = changed.iter().map(|(wid, _)| *wid).collect::<Vec<_>>();
        let mut witness_status_map: HashMap<<P::Seal as RgbSeal>::WitnessId, WitnessStatus> = {
            let mut ps = self.pile.session();
            ps.preload_consume_witnesses(changed_wids.iter().copied());
            ps.witness_statuses_for(changed_wids.iter().copied())
                .into_iter()
                .collect()
        };

        // Step 1-2: collect reads (has_witness hits the warm hoard cache; status from the batch)
        let mut affected_wids = IndexMap::new();
        for (wid, status) in changed {
            if !self.pile.session().has_witness(wid) {
                continue;
            }
            let prev = match witness_status_map.get(&wid) {
                Some(prev) => *prev,
                None => {
                    let prev = self.pile.session().witness_status(wid);
                    witness_status_map.insert(wid, prev);
                    prev
                }
            };
            if status == prev {
                continue;
            }
            let old = affected_wids.insert(wid, status);
            debug_assert!(old.is_none() || old == Some(status));
        }
        let status_changed = !affected_wids.is_empty();

        // Step 2: map affected witnesses to operations (warm stand cache) and compute each op's
        // best status from batched forward opid->wids + witness-status lookups, mirroring
        // `best_op_status` without its per-op/per-witness round-trips.
        let opids_per_wid: Vec<Vec<Opid>> = affected_wids
            .keys()
            .copied()
            .map(|wid| self.pile.session().ops_by_witness_id(wid))
            .collect();
        let affected_opids = opids_per_wid.into_iter().flatten().collect::<IndexSet<_>>();
        let op_witness_ids_map: HashMap<Opid, Vec<<P::Seal as RgbSeal>::WitnessId>> = {
            let mut ps = self.pile.session();
            ps.op_witness_ids_for(affected_opids.iter().copied())
                .into_iter()
                .collect()
        };
        {
            let involved_wids = op_witness_ids_map
                .values()
                .flatten()
                .copied()
                .filter(|wid| !witness_status_map.contains_key(wid))
                .collect::<HashSet<_>>();
            if !involved_wids.is_empty() {
                let mut ps = self.pile.session();
                for (wid, status) in ps.witness_statuses_for(involved_wids) {
                    witness_status_map.insert(wid, status);
                }
            }
        }
        let mut affected_ops = IndexMap::new();
        for opid in affected_opids {
            let op_status = op_witness_ids_map
                .get(&opid)
                .and_then(|wids| {
                    wids.iter()
                        .map(|wid| {
                            witness_status_map
                                .get(wid)
                                .copied()
                                .unwrap_or(WitnessStatus::Archived)
                        })
                        .reduce(|best, other| best.best(other))
                })
                .unwrap_or(WitnessStatus::Genesis);
            affected_ops.insert(opid, op_status);
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
            self.evict_op_seal_caches(opid);
            // Post-update best status, mirroring `best_op_status` but computed from the batched
            // maps: a witness just written in step 3 takes its new status, every other witness of
            // the op keeps its pre-sync status. Avoids a per-op/per-witness DB round-trip here.
            let new_status = op_witness_ids_map
                .get(&opid)
                .and_then(|wids| {
                    wids.iter()
                        .map(|wid| {
                            affected_wids
                                .get(wid)
                                .copied()
                                .or_else(|| witness_status_map.get(wid).copied())
                                .unwrap_or(WitnessStatus::Archived)
                        })
                        .reduce(|best, other| best.best(other))
                })
                .unwrap_or(WitnessStatus::Genesis);
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

        // Capture the descendant closure of all directly-affected ops *before* the ledger
        // rollback/forward mutate the read/spent indices, so the incremental valid-cache update
        // covers every op whose validity the ledger may flip (not just the seed ops).
        let affected_closure = self
            .ledger
            .descendants(roll_back.iter().copied().chain(forward.iter().copied()))
            .collect::<HashSet<_>>();

        // Step 5: ledger rollback/forward
        self.ledger.rollback(roll_back).map_err(MultiError::B)?;
        self.pile.session().commit_transaction();
        self.ledger.forward(forward)?;
        self.pile.session().commit_transaction();
        if status_changed {
            self.clear_owned_state_status_cache();
        }
        self.apply_valid_cache_delta(affected_closure);
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
        let mut ps = self.pile.session();
        let added = Self::include_with_session(&mut ps, opid, anchor, published);
        drop(ps);
        if added {
            let aux_started = Instant::now();
            self.remove_op_aux_cache_entry(opid);
            self.clear_owned_state_status_cache();
            let aux_us = aux_started.elapsed().as_micros();
            with_consume_stats(|stats| stats.include_aux_us += aux_us);
        }
    }

    fn include_with_session<PS>(
        ps: &mut PS,
        opid: Opid,
        anchor: <P::Seal as RgbSeal>::Client,
        published: &<P::Seal as RgbSeal>::Published,
    ) -> bool
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let wid = published.pub_id();
        let resolve_started = Instant::now();
        let has_started = Instant::now();
        let has_witness = ps.has_witness(wid);
        let has_witness_us = has_started.elapsed().as_micros();
        let mut cli_witness_us = 0u128;
        let mut ops_by_witness_us = 0u128;
        let anchor = if has_witness {
            let cli_started = Instant::now();
            let mut prev = ps.cli_witness(wid);
            cli_witness_us = cli_started.elapsed().as_micros();
            if prev == anchor {
                let ops_started = Instant::now();
                let duplicate_witness = ps.ops_by_witness_id(wid).contains(&opid);
                ops_by_witness_us = ops_started.elapsed().as_micros();
                if duplicate_witness {
                    let resolve_us = resolve_started.elapsed().as_micros();
                    with_consume_stats(|stats| {
                        stats.duplicate_witness_updates += 1;
                        stats.include_resolve_us += resolve_us;
                        stats.include_has_witness_us += has_witness_us;
                        stats.include_cli_witness_us += cli_witness_us;
                        stats.include_ops_by_witness_us += ops_by_witness_us;
                    });
                    return false;
                }
            }
            if prev != anchor {
                prev.merge(anchor)
                    .expect("incompatible anchors — storage corrupted");
            }
            prev
        } else {
            anchor
        };
        let resolve_us = resolve_started.elapsed().as_micros();
        let add_started = Instant::now();
        ps.add_witness(opid, wid, published, &anchor, WitnessStatus::Tentative);
        ps.include_commit_transaction();
        let add_us = add_started.elapsed().as_micros();
        with_consume_stats(|stats| {
            stats.include_resolve_us += resolve_us;
            stats.include_has_witness_us += has_witness_us;
            stats.include_cli_witness_us += cli_witness_us;
            stats.include_ops_by_witness_us += ops_by_witness_us;
            stats.include_add_us += add_us;
        });
        true
    }

    pub(crate) fn commit_pile_transaction(&mut self) { self.pile.session().commit_transaction(); }

    fn flush_pending_witness_updates(&mut self) -> usize {
        if self.pending_witness_updates.is_empty() {
            return 0;
        }

        let pending = self.pending_witness_updates.take();
        let mut applied_opids = Vec::with_capacity(pending.len());
        let mut ps = self.pile.session();
        for (opid, witness) in pending {
            if Self::include_with_session(&mut ps, opid, witness.client, &witness.published) {
                applied_opids.push(opid);
            }
        }
        drop(ps);

        let applied_count = applied_opids.len();
        if !applied_opids.is_empty() {
            let aux_started = Instant::now();
            for opid in applied_opids {
                self.remove_op_aux_cache_entry(opid);
            }
            self.clear_owned_state_status_cache();
            let aux_us = aux_started.elapsed().as_micros();
            with_consume_stats(|stats| stats.include_aux_us += aux_us);
        }
        applied_count
    }

    fn aux_with_session<W: WriteRaw, PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
        writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let (writer, _) = Self::aux_operation_seals_with_session(ps, opid, op, writer)?;
        Ok(writer)
    }

    fn aux_operation_seals_with_session<W: WriteRaw, PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<(StrictWriter<W>, OperationSeals<P::Seal>)>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let operation_seals = Self::operation_seals_with_session(ps, opid, op);
        writer = operation_seals.defined_seals.strict_encode(writer)?;
        writer = operation_seals.witness.is_some().strict_encode(writer)?;
        if let Some(w) = &operation_seals.witness {
            writer = w.strict_encode(writer)?;
        }
        Ok((writer, operation_seals))
    }

    fn operation_seals_with_session<PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
    ) -> OperationSeals<P::Seal>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let defined_seals = ps.seals(opid, op.destructible_out.len_u16());
        let witness = Self::retrieve_with_session(ps, opid);
        OperationSeals { operation: op.clone(), defined_seals, witness }
    }

    fn genesis_operation_for_verification(&self) -> Operation {
        let codex_id = self.ledger.articles().codex_id();
        let genesis_contract_id = ContractId::from_byte_array(codex_id.to_byte_array());

        self.ledger
            .articles()
            .genesis()
            .to_operation(genesis_contract_id)
    }

    fn contract_genesis_operation(&self) -> Operation {
        self.ledger
            .articles()
            .genesis()
            .to_operation(self.ledger.articles().contract_id())
    }

    fn stage_genesis_verification_memory(&mut self, operation: &Operation) {
        let genesis_opid = self.ledger.articles().genesis_opid();
        // Genesis state is immutable for the life of the contract, so once staged for this
        // genesis opid it can be reused across consumes without rebuilding.
        if self.genesis_verification_memory_staged_for == Some(genesis_opid) {
            return;
        }
        self.genesis_verification_memory
            .replace_with_operation(genesis_opid, operation);
        self.genesis_verification_memory_staged_for = Some(genesis_opid);
    }

    fn stage_missing_verification_inputs(&mut self, operation: &Operation) -> Result<(), S::Error> {
        let missing_destructible = operation
            .destructible_in
            .iter()
            .filter_map(|input| {
                if self.ledger.state().raw.destructible(input.addr).is_some() {
                    return None;
                }

                self.genesis_verification_memory
                    .destructible(input.addr)
                    .or_else(|| self.known_verification_memory.destructible(input.addr))
                    .map(|cell| (input.addr, cell))
            })
            .collect::<Vec<_>>();

        let missing_immutable = operation
            .immutable_in
            .iter()
            .filter_map(|addr| {
                if self.ledger.state().raw.immutable(*addr).is_some() {
                    return None;
                }

                self.genesis_verification_memory
                    .immutable_data(*addr)
                    .or_else(|| self.known_verification_memory.immutable_data(*addr))
                    .map(|data| (*addr, data))
            })
            .collect::<Vec<_>>();

        if missing_destructible.is_empty() && missing_immutable.is_empty() {
            return Ok(());
        }

        self.ledger.with_session(|session| {
            session.update_state(|state, _| {
                for (addr, cell) in missing_destructible {
                    state
                        .raw
                        .auth
                        .insert(cell.auth, addr)
                        .expect("verification state is too large");
                    state
                        .raw
                        .owned
                        .insert(addr, cell)
                        .expect("verification state is too large");
                }

                state
                    .raw
                    .global
                    .extend(missing_immutable)
                    .expect("verification state is too large");
            })
        })
    }

    fn remove_op_aux_cache_entry(&mut self, opid: Opid) {
        if let Some(entry) = self.op_aux_cache.remove(&opid) {
            self.op_aux_cache_bytes = self.op_aux_cache_bytes.saturating_sub(entry.bytes.len());
        }
        if let Some(seq) = self.op_aux_cache_positions.remove(&opid) {
            self.op_aux_cache_order.remove(&seq);
        }
    }

    fn op_aux_entry_covers_outputs(entry: &OpAuxCacheEntry<P::Seal>) -> bool {
        entry
            .operation_seals
            .operation
            .destructible_out
            .iter()
            .enumerate()
            .all(|(no, cell)| {
                u16::try_from(no)
                    .ok()
                    .and_then(|no| entry.operation_seals.defined_seals.get(&no))
                    .is_some_and(|seal| seal.auth_token() == cell.auth)
            })
    }

    /// Evicts cached seal data defined by `opid`.
    ///
    /// `resolved_seal_cache` stores witness-resolved seals (`definition.resolve(pub_id)`); after a
    /// reorg the producing operation's witness `pub_id` can change (e.g. RBF), so any cached
    /// resolved seal for that operation is stale and must be dropped. `seal_def_cache` and
    /// `duplicate_seal_def_cache` are evicted alongside it to keep the local seal caches coherent
    /// and force a fresh re-read from the pile on the next access. Only locally-owned caches are
    /// touched; the externally-injected caches are not mutated here.
    fn evict_op_seal_caches(&mut self, opid: Opid) {
        self.resolved_seal_cache.retain(|addr, _| addr.opid != opid);
        self.seal_def_cache.retain(|addr, _| addr.opid != opid);
        self.duplicate_seal_def_cache
            .retain(|addr| addr.opid != opid);
    }

    fn next_op_aux_cache_seq(&mut self) -> u64 {
        let seq = self.op_aux_cache_next_seq;
        self.op_aux_cache_next_seq = self.op_aux_cache_next_seq.wrapping_add(1);
        seq
    }

    fn record_op_aux_cache_access(&mut self, opid: Opid) {
        if let Some(seq) = self.op_aux_cache_positions.remove(&opid) {
            self.op_aux_cache_order.remove(&seq);
        }
        let seq = self.next_op_aux_cache_seq();
        self.op_aux_cache_positions.insert(opid, seq);
        self.op_aux_cache_order.insert(seq, opid);
    }

    fn touch_op_aux_cache_entry(&mut self, opid: Opid) {
        if self
            .op_aux_cache
            .get(&opid)
            .is_some_and(Self::op_aux_entry_covers_outputs)
        {
            self.record_op_aux_cache_access(opid);
        } else {
            self.remove_op_aux_cache_entry(opid);
        }
    }

    fn insert_op_aux_cache_entry(&mut self, opid: Opid, entry: OpAuxCacheEntry<P::Seal>) {
        if !Self::op_aux_entry_covers_outputs(&entry) {
            self.remove_op_aux_cache_entry(opid);
            return;
        }

        let max_bytes = op_aux_cache_max_bytes();
        let bytes_len = entry.bytes.len();
        if bytes_len > max_bytes {
            return;
        }

        if let Some(old_entry) = self.op_aux_cache.remove(&opid) {
            self.op_aux_cache_bytes = self
                .op_aux_cache_bytes
                .saturating_sub(old_entry.bytes.len());
        }
        if let Some(seq) = self.op_aux_cache_positions.remove(&opid) {
            self.op_aux_cache_order.remove(&seq);
        }

        while self.op_aux_cache_bytes.saturating_add(bytes_len) > max_bytes {
            let Some((_, oldest)) = self.op_aux_cache_order.pop_first() else {
                break;
            };
            self.op_aux_cache_positions.remove(&oldest);
            if let Some(old_entry) = self.op_aux_cache.remove(&oldest) {
                self.op_aux_cache_bytes = self
                    .op_aux_cache_bytes
                    .saturating_sub(old_entry.bytes.len());
            }
        }

        self.op_aux_cache.insert(opid, entry);
        self.record_op_aux_cache_access(opid);
        self.op_aux_cache_bytes = self.op_aux_cache_bytes.saturating_add(bytes_len);
    }

    fn build_op_aux_cache_entry(
        &mut self,
        opid: Opid,
        op: &Operation,
    ) -> io::Result<OpAuxCacheEntry<P::Seal>> {
        let mut ps = self.pile.session();
        Self::build_op_aux_cache_entry_with_session(&mut ps, opid, op)
    }

    /// Same as [`Self::build_op_aux_cache_entry_with_session`], accumulating per-phase wall
    /// time so the consign prewarm loop can attribute its residual (operation-encode CPU vs
    /// pile seal reads vs witness retrieve vs seal/witness encode+clone) instead of
    /// reporting one opaque total.
    ///
    /// `defined_seals` is supplied by the caller from a batched snapshot: the per-op
    /// `ps.seals()` read costs one DB round-trip per operation with any absent output cell
    /// (the shared seal cache deliberately refuses negative entries), which multiplies into
    /// minutes over deep-history consignments on cross-region deployments.
    fn build_op_aux_cache_entry_with_session_timed<PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
        defined_seals: SmallOrdMap<u16, <P::Seal as RgbSeal>::Definition>,
        timers: &mut ConsignPrewarmPhaseTimers,
    ) -> io::Result<OpAuxCacheEntry<P::Seal>>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let started_at = Instant::now();
        let mem_writer = StrictWriter::with(StreamWriter::in_memory::<{ usize::MAX }>());
        let mem_writer = op.strict_encode(mem_writer)?;
        timers.encode_us += started_at.elapsed().as_micros();

        let started_at = Instant::now();
        let witness = Self::retrieve_with_session(ps, opid);
        timers.retrieve_us += started_at.elapsed().as_micros();

        // Mirrors `aux_operation_seals_with_session`: seal map, witness presence flag, then
        // the witness itself.
        let started_at = Instant::now();
        let mut writer = defined_seals.strict_encode(mem_writer)?;
        writer = witness.is_some().strict_encode(writer)?;
        if let Some(w) = &witness {
            writer = w.strict_encode(writer)?;
        }
        let operation_seals = OperationSeals { operation: op.clone(), defined_seals, witness };
        let entry = OpAuxCacheEntry {
            bytes: writer.unbox().unconfine(),
            operation_seals: Arc::new(operation_seals),
        };
        timers.finish_us += started_at.elapsed().as_micros();
        Ok(entry)
    }

    fn build_op_aux_cache_entry_with_session<PS>(
        ps: &mut PS,
        opid: Opid,
        op: &Operation,
    ) -> io::Result<OpAuxCacheEntry<P::Seal>>
    where
        PS: PileSession<Seal = P::Seal>,
    {
        let mem_writer = StrictWriter::with(StreamWriter::in_memory::<{ usize::MAX }>());
        let mem_writer = op.strict_encode(mem_writer)?;
        let (mem_writer, operation_seals) =
            Self::aux_operation_seals_with_session(ps, opid, op, mem_writer)?;
        Ok(OpAuxCacheEntry {
            bytes: mem_writer.unbox().unconfine(),
            operation_seals: Arc::new(operation_seals),
        })
    }

    fn op_aux_cached_operation_seals<W: WriteRaw>(
        &mut self,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<(StrictWriter<W>, OperationSeals<P::Seal>)>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Published: Clone,
    {
        if let Some(entry) = self.op_aux_cache.get(&opid) {
            if Self::op_aux_entry_covers_outputs(entry) {
                let bytes = entry.bytes.clone();
                let operation_seals = entry.operation_seals.as_ref().clone();
                self.record_op_aux_cache_access(opid);
                unsafe {
                    writer.raw_writer().write_raw::<{ usize::MAX }>(&bytes)?;
                }
                return Ok((writer, operation_seals));
            }
            self.remove_op_aux_cache_entry(opid);
        }

        let entry = self.build_op_aux_cache_entry(opid, op)?;
        let operation_seals = entry.operation_seals.as_ref().clone();
        unsafe {
            writer
                .raw_writer()
                .write_raw::<{ usize::MAX }>(&entry.bytes)?;
        }
        self.insert_op_aux_cache_entry(opid, entry);
        Ok((writer, operation_seals))
    }

    fn op_aux_cached<W: WriteRaw>(
        &mut self,
        opid: Opid,
        op: &Operation,
        mut writer: StrictWriter<W>,
    ) -> io::Result<StrictWriter<W>> {
        if let Some(entry) = self.op_aux_cache.get(&opid) {
            if Self::op_aux_entry_covers_outputs(entry) {
                let bytes = entry.bytes.clone();
                self.record_op_aux_cache_access(opid);
                unsafe {
                    writer.raw_writer().write_raw::<{ usize::MAX }>(&bytes)?;
                }
                return Ok(writer);
            }
            self.remove_op_aux_cache_entry(opid);
        }

        let entry = self.build_op_aux_cache_entry(opid, op)?;
        unsafe {
            writer
                .raw_writer()
                .write_raw::<{ usize::MAX }>(&entry.bytes)?;
        }
        self.insert_op_aux_cache_entry(opid, entry);
        Ok(writer)
    }

    fn prewarm_op_aux_cache(
        &mut self,
        ops: &[(Opid, Arc<Operation>)],
        contract_id: ContractId,
    ) -> io::Result<(usize, HashMap<Opid, OpAuxCacheEntry<P::Seal>>)> {
        let prewarm_started_at = Instant::now();
        let mut encoded = 0usize;
        let mut retained = HashMap::with_capacity(ops.len());
        let mut retained_bytes = 0usize;
        let mut pending = Vec::new();
        for (idx, (opid, op)) in ops.iter().enumerate() {
            if let Some(entry) = self.op_aux_cache.get(opid) {
                if Self::op_aux_entry_covers_outputs(entry) {
                    // Copy the covering entry into the per-consign `retained` snapshot instead of
                    // just skipping it. `retained` is the authoritative source the write loop
                    // reads; the persistent `op_aux_cache` is only 3 MiB and
                    // warming the *other* pending ops below evicts these
                    // covered ones (LRU) before the write loop reaches them.
                    // Dropping them here left the write loop to rebuild each via a per-op DB round
                    // trip — a linear wall on deep consigns whose ancestry exceeds the cache (a
                    // 9k-op consign following another only retained ~4.5k, the
                    // rest rebuilt ≈ 200s+). Retaining them keeps that
                    // knowledge local to this consign (transient, freed
                    // after write) without growing the persistent cache.
                    let entry = entry.clone();
                    retained_bytes = retained_bytes.saturating_add(entry.bytes.len());
                    retained.insert(*opid, entry);
                    self.record_op_aux_cache_access(*opid);
                    continue;
                }
            }
            self.remove_op_aux_cache_entry(*opid);
            pending.push((idx, *opid, op));
        }

        let mut warmed = Vec::with_capacity(pending.len());
        let mut phase_timers = ConsignPrewarmPhaseTimers::default();
        {
            let mut ps = self.pile.session();
            let preload_ops = pending
                .iter()
                .map(|(_, opid, op)| (*opid, op.destructible_out.len_u16()));
            ps.preload_aux_reads(preload_ops);

            // One batched snapshot of every pending op's output seal definitions. The
            // shared seal cache refuses negative entries (cross-actor staleness), so the
            // per-op `ps.seals()` path re-issues a DB round-trip for every op with an
            // absent output cell; the snapshot keeps that knowledge local to this consign.
            let seals_started_at = Instant::now();
            let output_cells = pending.iter().flat_map(|(_, opid, op)| {
                (0..op.destructible_out.len_u16()).map(|no| CellAddr::new(*opid, no))
            });
            let mut seal_snapshot: BTreeMap<Opid, SmallOrdMap<u16, _>> = BTreeMap::new();
            for (addr, seal) in ps.seals_for(output_cells) {
                let _ = seal_snapshot
                    .entry(addr.opid)
                    .or_default()
                    .insert(addr.pos, seal);
            }
            phase_timers.seals_us += seals_started_at.elapsed().as_micros();

            for (idx, opid, op) in pending {
                let op_started_at = Instant::now();
                // The batched snapshot (`seals_for`) is authoritative: it already recovers
                // owned-but-materialized-lagged output seals from legacy. A short map is normal —
                // a multi-party op's outputs are split across wallets and this wallet only defines
                // seals for the ones it owns.
                let defined_seals = seal_snapshot.remove(&opid).unwrap_or_default();
                let entry = Self::build_op_aux_cache_entry_with_session_timed(
                    &mut ps,
                    opid,
                    op,
                    defined_seals,
                    &mut phase_timers,
                )?;
                let elapsed_ms = slow_rgb_stage_elapsed(op_started_at);
                warmed.push((idx, opid, entry, elapsed_ms));
            }
        }

        for (idx, opid, entry, elapsed_ms) in warmed {
            let bytes_len = entry.bytes.len();
            retained_bytes = retained_bytes.saturating_add(bytes_len);
            retained.insert(opid, entry.clone());
            self.insert_op_aux_cache_entry(opid, entry);
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
                    retained_ops = retained.len(),
                    retained_bytes,
                    encode_us = phase_timers.encode_us,
                    seals_us = phase_timers.seals_us,
                    retrieve_us = phase_timers.retrieve_us,
                    finish_us = phase_timers.finish_us,
                    cache_bytes = self.op_aux_cache_bytes,
                    cache_entries = self.op_aux_cache.len(),
                    "Slow rgb-std stage"
                );
            }
        }
        Ok((encoded, retained))
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
        let genesis_op = self.genesis_operation_for_verification();
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
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        self.consign_with_known_opids(terminals, std::iter::empty::<Opid>(), writer)
    }

    pub fn terminal_opids(
        &self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
    ) -> BTreeSet<Opid> {
        terminals
            .into_iter()
            .map(|terminal| self.ledger.state().addr(*terminal.borrow()).opid)
            .collect()
    }

    pub fn consign_predecoded(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<Vec<OperationSeals<P::Seal>>>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        self.consign_with_known_boundaries_impl(
            terminals,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            false,
            true,
            writer,
        )
        .map(Option::unwrap_or_default)
    }

    pub fn consign_with_known_opids(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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

    pub fn consign_with_known_cells_and_opids_predecoded(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<Vec<OperationSeals<P::Seal>>>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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
        self.consign_with_known_boundaries_impl(
            terminals,
            known_opids,
            known_cells,
            HashSet::new(),
            false,
            true,
            writer,
        )
        .map(Option::unwrap_or_default)
    }

    pub fn consign_with_known_cells_opids_and_immutable_checkpoints(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        immutable_checkpoint_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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
        let immutable_checkpoint_opids = immutable_checkpoint_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();

        self.consign_with_known_boundaries_impl(
            terminals,
            known_opids,
            known_cells,
            immutable_checkpoint_opids,
            false,
            false,
            writer,
        )
        .map(drop)
    }

    pub fn consign_with_known_cells_opids_and_immutable_checkpoints_predecoded(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        immutable_checkpoint_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<Vec<OperationSeals<P::Seal>>>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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
        let immutable_checkpoint_opids = immutable_checkpoint_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();

        self.consign_with_known_boundaries_impl(
            terminals,
            known_opids,
            known_cells,
            immutable_checkpoint_opids,
            false,
            true,
            writer,
        )
        .map(Option::unwrap_or_default)
    }

    pub fn consign_with_trusted_known_cells_and_opids(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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

    pub fn consign_with_trusted_known_opids(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let known_opids = known_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();
        self.consign_with_known_boundaries(terminals, known_opids, HashSet::new(), true, writer)
    }

    pub fn consign_with_trusted_known_opids_predecoded(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<Vec<OperationSeals<P::Seal>>>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let known_opids = known_opids
            .into_iter()
            .map(|opid| *opid.borrow())
            .collect::<HashSet<_>>();
        self.consign_with_known_boundaries_impl(
            terminals,
            known_opids,
            HashSet::new(),
            HashSet::new(),
            true,
            true,
            writer,
        )
        .map(Option::unwrap_or_default)
    }

    pub fn consign_with_trusted_known_cells_and_opids_predecoded(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_cells: impl IntoIterator<Item = impl Borrow<CellAddr>>,
        known_opids: impl IntoIterator<Item = impl Borrow<Opid>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<Vec<OperationSeals<P::Seal>>>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
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
        self.consign_with_known_boundaries_impl(
            terminals,
            known_opids,
            known_cells,
            HashSet::new(),
            true,
            true,
            writer,
        )
        .map(Option::unwrap_or_default)
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
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        self.consign_with_known_boundaries_impl(
            terminals,
            known_opids,
            known_cells,
            HashSet::new(),
            trust_known_opids,
            false,
            writer,
        )
        .map(drop)
    }

    fn consign_with_known_boundaries_impl(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        known_opids: HashSet<Opid>,
        known_cells: HashSet<CellAddr>,
        immutable_checkpoint_opids: HashSet<Opid>,
        trust_known_opids: bool,
        capture_operations: bool,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<Option<Vec<OperationSeals<P::Seal>>>>
    where
        <P::Seal as RgbSeal>::Client: Clone,
        <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::Published: Clone,
        <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
        <P::Seal as RgbSeal>::WitnessId: StrictEncode,
    {
        let total_started_at = Instant::now();
        let mut boundaries = ConsignmentSelectionBoundaries::new(
            known_opids,
            known_cells,
            immutable_checkpoint_opids,
            trust_known_opids,
        );
        boundaries.filter_known_opids(self);

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
        boundaries.prune_checkpoint_opids(genesis_opid);

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
        tracing::debug!(
            operation = "rgb_std",
            stage = "consign_select_start",
            contract_id = ?self.contract_id,
            terminal_ops = terminal_opids.len(),
            known_ops = boundaries.known_opids.len(),
            raw_known_ops = boundaries.raw_known_opids,
            known_cells = boundaries.known_cells.len(),
            immutable_checkpoint_ops = boundaries.immutable_checkpoint_opids.len(),
            raw_immutable_checkpoint_ops = boundaries.raw_immutable_checkpoint_opids,
            trust_known_opids = boundaries.trust_known_opids,
            published_ops_added,
            "Starting rgb-std consignment operation selection"
        );
        let (_, ops, known_cell_edges_skipped) = self
            .ledger
            .with_session(|session| -> io::Result<_> {
                let select_ops_started_at = Instant::now();

                let preload_started_at = Instant::now();
                let preload_roots = terminal_opids.iter().chain(published_roots.iter()).copied();
                let preload_plan = SelectionPreloadPlan::from_parent_ops(
                    session
                        .operation_parent_ops()
                        .into_iter()
                        .collect::<HashMap<_, _>>(),
                    preload_roots,
                    genesis_opid,
                    &boundaries.known_opids,
                );
                session.preload_selection_plan(&preload_plan);

                if let Some(elapsed_ms) = slow_rgb_stage_elapsed(preload_started_at) {
                    tracing::warn!(
                        operation = "rgb_std",
                        stage = "consign_preload_selection_ops",
                        elapsed_ms,
                        contract_id = ?self.contract_id,
                        terminal_ops = terminal_opids.len(),
                        candidate_ops = preload_plan.len(),
                        known_ops = boundaries.known_opids.len(),
                        raw_known_ops = boundaries.raw_known_opids,
                        known_cells = boundaries.known_cells.len(),
                        immutable_checkpoint_ops = boundaries.immutable_checkpoint_opids.len(),
                        raw_immutable_checkpoint_ops = boundaries.raw_immutable_checkpoint_opids,
                        parent_ops = preload_plan.parent_ops,
                        parent_edges = preload_plan.parent_edges,
                        trust_known_opids = boundaries.trust_known_opids,
                        published_ops_added,
                        "Slow rgb-std stage"
                    );
                }

                let mut selected_opids = HashSet::new();
                let mut pending_opids = HashSet::new();
                let mut ordered_opids = Vec::new();
                let mut operation_cache = HashMap::new();
                let mut known_cell_edges_skipped = 0usize;
                let mut forced_destructible_edges = 0usize;
                let mut known_destructible_edges_skipped = 0usize;

                macro_rules! include_op_with_dependencies {
                    ($root:expr) => {{
                        let root = $root;
                        if root != genesis_opid
                            && !boundaries.skips_operation(&root)
                            && !selected_opids.contains(&root)
                            && pending_opids.insert(root)
                        {
                            let mut stack = vec![(root, false, false)];
                            while let Some((opid, expanded, force_include)) = stack.pop() {
                                if opid == genesis_opid
                                    || (!force_include && boundaries.skips_operation(&opid))
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

                                stack.push((opid, true, force_include));
                                let op = operation_cache
                                    .entry(opid)
                                    .or_insert_with(|| session.operation(opid));
                                for input in &op.immutable_in {
                                    let prev = input.opid;
                                    if prev != genesis_opid
                                        && !boundaries.skips_immutable_dependency(&prev)
                                        && !selected_opids.contains(&prev)
                                    {
                                        pending_opids.insert(prev);
                                        stack.push((prev, false, false));
                                    }
                                }

                                for input in &op.destructible_in {
                                    // Only an exact CellAddr is a sufficient destructible
                                    // boundary: it proves the receiver already has both the state
                                    // cell and its resolvable seal definition. An opid-only hint
                                    // must never prune this edge.
                                    if boundaries.skips_destructible_dependency(&input.addr) {
                                        known_cell_edges_skipped =
                                            known_cell_edges_skipped.saturating_add(1);
                                        known_destructible_edges_skipped =
                                            known_destructible_edges_skipped.saturating_add(1);
                                        continue;
                                    }
                                    if boundaries.skips_operation(&input.addr.opid) {
                                        forced_destructible_edges =
                                            forced_destructible_edges.saturating_add(1);
                                    }
                                    let prev = input.addr.opid;
                                    if prev != genesis_opid && !selected_opids.contains(&prev) {
                                        pending_opids.insert(prev);
                                        stack.push((prev, false, true));
                                    }
                                }

                                let st = session.transition(opid);
                                for addr in st.destroyed.keys().copied() {
                                    // Destroyed entries follow the same exact-cell rule.
                                    if boundaries.skips_destructible_dependency(&addr) {
                                        known_cell_edges_skipped =
                                            known_cell_edges_skipped.saturating_add(1);
                                        known_destructible_edges_skipped =
                                            known_destructible_edges_skipped.saturating_add(1);
                                        continue;
                                    }
                                    if boundaries.skips_operation(&addr.opid) {
                                        forced_destructible_edges =
                                            forced_destructible_edges.saturating_add(1);
                                    }

                                    let prev = addr.opid;
                                    if prev != genesis_opid && !selected_opids.contains(&prev) {
                                        pending_opids.insert(prev);
                                        stack.push((prev, false, true));
                                    }
                                }
                            }
                        }
                    }};
                }

                for opid in terminal_opids.iter().copied() {
                    include_op_with_dependencies!(opid);
                }
                for opid in published_roots.iter().copied() {
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
                        known_ops = boundaries.known_opids.len(),
                        raw_known_ops = boundaries.raw_known_opids,
                        known_cells = boundaries.known_cells.len(),
                        immutable_checkpoint_ops = boundaries.immutable_checkpoint_opids.len(),
                        raw_immutable_checkpoint_ops = boundaries.raw_immutable_checkpoint_opids,
                        known_cell_edges_skipped,
                        forced_destructible_edges,
                        known_destructible_edges_skipped,
                        trust_known_opids = boundaries.trust_known_opids,
                        published_ops_added,
                        "Slow rgb-std stage"
                    );
                }
                let filter_ops_started_at = Instant::now();
                let ops = ordered_opids
                    .into_iter()
                    .map(|opid| {
                        let op = operation_cache
                            .remove(&opid)
                            .unwrap_or_else(|| session.operation(opid));
                        (opid, op)
                    })
                    .collect::<Vec<_>>();
                if let Some(elapsed_ms) = slow_rgb_stage_elapsed(filter_ops_started_at) {
                    tracing::warn!(
                        operation = "rgb_std",
                        stage = "consign_filter_operations",
                        elapsed_ms,
                        contract_id = ?self.contract_id,
                        selected_ops = ops.len(),
                        terminal_ops = terminal_opids.len(),
                        known_ops = boundaries.known_opids.len(),
                        raw_known_ops = boundaries.raw_known_opids,
                        known_cells = boundaries.known_cells.len(),
                        immutable_checkpoint_ops = boundaries.immutable_checkpoint_opids.len(),
                        raw_immutable_checkpoint_ops = boundaries.raw_immutable_checkpoint_opids,
                        known_cell_edges_skipped,
                        forced_destructible_edges,
                        trust_known_opids = boundaries.trust_known_opids,
                        published_ops_added,
                        "Slow rgb-std stage"
                    );
                }

                Ok((selected_opids.len(), ops, known_cell_edges_skipped))
            })
            .map_err(|err| io::Error::other(err.to_string()))?;
        let count = ops.len() as u32;
        let contract_id = self.contract_id;
        let (prewarmed_ops, mut prewarmed_entries) =
            self.prewarm_op_aux_cache(&ops, contract_id)?;
        let mut writer = writer;
        let mut captured_operations =
            capture_operations.then(|| Vec::with_capacity(ops.len().saturating_add(1)));
        let write_started_at = Instant::now();
        let genesis_op = self.genesis_operation_for_verification();
        writer = 0u8.strict_encode(writer)?; // DEEDS_VERSION = 0
        writer = contract_id.strict_encode(writer)?;
        writer = 0u8.strict_encode(writer)?;
        writer = self.ledger.articles().strict_encode(writer)?;

        if let Some(operations) = captured_operations.as_mut() {
            let mut ps = self.pile.session();
            let (next_writer, operation_seals) =
                Self::aux_operation_seals_with_session(&mut ps, genesis_opid, &genesis_op, writer)?;
            writer = next_writer;
            operations.push(operation_seals);
        } else {
            writer = self.aux_uncached(genesis_opid, &genesis_op, writer)?;
        }

        writer = count.strict_encode(writer)?;
        let mut prewarm_hits = 0usize;
        let mut prewarm_misses = 0usize;
        // Split the miss path so a hung deep consign is diagnosable: a miss that is served from the
        // op-aux cache is cheap, but a miss that must rebuild the entry issues per-op pile
        // round-trips (the suspected per-op×RTT wall on deep full closures with absent output
        // cells, where the batched prewarm snapshot could not produce a covering entry).
        let mut write_cache_hits = 0usize;
        let mut write_rebuilds = 0usize;
        let mut ops_done = 0usize;
        for (opid, op) in ops {
            if let Some(entry) = prewarmed_entries.remove(&opid) {
                prewarm_hits = prewarm_hits.saturating_add(1);
                unsafe {
                    writer
                        .raw_writer()
                        .write_raw::<{ usize::MAX }>(&entry.bytes)?;
                }
                if let Some(operations) = captured_operations.as_mut() {
                    operations.push(entry.operation_seals.as_ref().clone());
                }
                self.touch_op_aux_cache_entry(opid);
            } else {
                prewarm_misses = prewarm_misses.saturating_add(1);
                // Read-only pre-check mirroring `op_aux_cached*`'s branch: a covering entry is
                // served from cache, otherwise the call below rebuilds it via a per-op read.
                if self
                    .op_aux_cache
                    .get(&opid)
                    .is_some_and(Self::op_aux_entry_covers_outputs)
                {
                    write_cache_hits = write_cache_hits.saturating_add(1);
                } else {
                    write_rebuilds = write_rebuilds.saturating_add(1);
                }
                if let Some(operations) = captured_operations.as_mut() {
                    let (next_writer, operation_seals) =
                        self.op_aux_cached_operation_seals(opid, &op, writer)?;
                    writer = next_writer;
                    operations.push(operation_seals);
                } else {
                    writer = self.op_aux_cached(opid, &op, writer)?;
                }
            }
            ops_done = ops_done.saturating_add(1);
            // Incremental progress: a consign killed by the request timeout before the post-loop
            // breadcrumb fires still leaves a rate + hit/miss/rebuild trail. Plain module target
            // (`rgb::contract`) so it clears the RUST_LOG whitelist like the other consign stages.
            if ops_done % 500 == 0 {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consign_write_progress",
                    ?contract_id,
                    ops_done,
                    total_ops = count,
                    prewarm_hits,
                    prewarm_misses,
                    write_cache_hits,
                    write_rebuilds,
                    elapsed_ms = write_started_at.elapsed().as_millis() as u64,
                    "consign write-loop progress"
                );
            }
        }
        if let Some(elapsed_ms) = slow_rgb_stage_elapsed(write_started_at) {
            tracing::warn!(
                operation = "rgb_std",
                stage = "consign_write_operations",
                elapsed_ms,
                ?contract_id,
                selected_ops = count,
                known_ops = boundaries.known_opids.len(),
                raw_known_ops = boundaries.raw_known_opids,
                known_cells = boundaries.known_cells.len(),
                immutable_checkpoint_ops = boundaries.immutable_checkpoint_opids.len(),
                raw_immutable_checkpoint_ops = boundaries.raw_immutable_checkpoint_opids,
                known_cell_edges_skipped,
                trust_known_opids = boundaries.trust_known_opids,
                prewarmed_ops,
                prewarm_hits,
                prewarm_misses,
                write_cache_hits,
                write_rebuilds,
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
                known_ops = boundaries.known_opids.len(),
                raw_known_ops = boundaries.raw_known_opids,
                known_cells = boundaries.known_cells.len(),
                immutable_checkpoint_ops = boundaries.immutable_checkpoint_opids.len(),
                raw_immutable_checkpoint_ops = boundaries.raw_immutable_checkpoint_opids,
                known_cell_edges_skipped,
                trust_known_opids = boundaries.trust_known_opids,
                "Slow rgb-std stage"
            );
        }
        Ok(captured_operations)
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
            .into_iter()
            .collect::<HashMap<_, _>>();
        let output_count_entries = output_counts.len();
        let output_counts_available = !output_counts.is_empty();
        let mut operation_decode_fallbacks = 0usize;
        let mut missing_operations = 0usize;
        let candidates = known_opids
            .into_iter()
            .filter_map(|opid| {
                if let Some(count) = output_counts.get(&opid).copied() {
                    return Some((opid, count));
                }

                if output_counts_available {
                    missing_operations = missing_operations.saturating_add(1);
                    return None;
                }

                if !self.ledger.has_operation(opid) {
                    missing_operations = missing_operations.saturating_add(1);
                    return None;
                }

                operation_decode_fallbacks = operation_decode_fallbacks.saturating_add(1);
                // Only the output count is needed here; take the shared Arc so the fallback does
                // not deep-copy the whole operation just to read a length.
                let op = self.ledger.operation_arc(opid);
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
            let genesis = Genesis::strict_decode(reader)?;
            let issue = Issue { version: issue_version, meta, codex, genesis };
            if issue.contract_id() != self.contract_id {
                return Err(ConsumeError::UnknownContract(issue.contract_id()));
            }
            let genesis_operations = ConsignmentGenesisOperations::from_issue(&issue);

            let evaluate_started_at = Instant::now();
            let previous_stats =
                CONSUME_STATS.with(|stats| stats.replace(Some(ConsumeStats::default())));
            let predecode_started_at = Instant::now();
            let operations = decode_consignment_operations(
                reader,
                genesis_operations.verification,
                seal_resolver,
            )?;
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

            let duplicate_cache_started_at = Instant::now();
            // Reset the per-consume seal-definition backstop up front, then let the prewarm below
            // repopulate it. Clearing here (rather than inside evaluate_commit, which runs after
            // prewarm) preserves the prewarmed entries through verification.
            self.consume_seal_defs.clear();
            let phase_started_at = Instant::now();
            let (known_ops, new_ops, opids) = self.partition_consume_operations(&operations);
            with_consume_stats(|stats| {
                stats.prewarm_partition_us += phase_started_at.elapsed().as_micros()
            });
            let phase_started_at = Instant::now();
            self.prewarm_known_operation_duplicate_caches(operations.len(), known_ops);
            with_consume_stats(|stats| {
                stats.prewarm_known_duplicates_us += phase_started_at.elapsed().as_micros()
            });
            let phase_started_at = Instant::now();
            self.preload_destructible_input_seals(&operations);
            with_consume_stats(|stats| {
                stats.prewarm_destructible_inputs_us += phase_started_at.elapsed().as_micros()
            });
            // Do not preload the new cohort's own output seals. `apply_operation` records every
            // genuinely-new op in `applied_new_ops`, and `apply_seals` then unconditionally takes
            // the idempotent `add_seals` path without consulting durable membership. Preloading
            // these not-yet-owned cells would only issue materialized + legacy absence reads.
            let phase_started_at = Instant::now();
            self.preload_consume_witnesses(&new_ops);
            with_consume_stats(|stats| {
                stats.prewarm_witnesses_us += phase_started_at.elapsed().as_micros()
            });
            let phase_started_at = Instant::now();
            self.preload_consume_insert_lookups(operations.len(), new_ops);
            with_consume_stats(|stats| {
                stats.prewarm_insert_lookups_us += phase_started_at.elapsed().as_micros();
                stats.prewarm_total_us += duplicate_cache_started_at.elapsed().as_micros();
            });
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

            let op_reader = PredecodedOpReader(opids.into_iter().zip(operations).collect());
            self.stage_genesis_verification_memory(&genesis_operations.contract);
            let evaluate_result = self.evaluate_commit(op_reader);
            let stats = CONSUME_STATS
                .with(|stats| stats.replace(previous_stats))
                .unwrap_or_default();
            record_last_consume_op_counts(&stats);
            record_last_consume_prewarm_phase_stats(&stats);
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
                    apply_witness_total_us = stats.apply_witness_total_us,
                    apply_witness_dupcache_us = stats.apply_witness_dupcache_us,
                    apply_witness_retain_us = stats.apply_witness_retain_us,
                    include_resolve_us = stats.include_resolve_us,
                    include_has_witness_us = stats.include_has_witness_us,
                    include_cli_witness_us = stats.include_cli_witness_us,
                    include_ops_by_witness_us = stats.include_ops_by_witness_us,
                    include_add_us = stats.include_add_us,
                    include_aux_us = stats.include_aux_us,
                    apply_seals_total_us = stats.apply_seals_total_us,
                    seals_cached_dup_us = stats.seals_cached_dup_us,
                    seals_missing_scan_us = stats.seals_missing_scan_us,
                    seals_match_us = stats.seals_match_us,
                    seals_dup_finalize_us = stats.seals_dup_finalize_us,
                    seals_insert_us = stats.seals_insert_us,
                    seals_add_seals_us = stats.seals_add_seals_us,
                    apply_operation_total_us = stats.apply_operation_total_us,
                    apply_operation_opid_us = stats.apply_operation_opid_us,
                    apply_operation_stage_inputs_us = stats.apply_operation_stage_inputs_us,
                    apply_operation_ledger_apply_us = stats.apply_operation_ledger_apply_us,
                    apply_operation_cache_us = stats.apply_operation_cache_us,
                    known_materialized_skips = stats.known_materialized_skips,
                    prewarm_total_us = stats.prewarm_total_us,
                    prewarm_partition_us = stats.prewarm_partition_us,
                    prewarm_known_duplicates_us = stats.prewarm_known_duplicates_us,
                    prewarm_destructible_inputs_us = stats.prewarm_destructible_inputs_us,
                    prewarm_output_seals_us = stats.prewarm_output_seals_us,
                    prewarm_witnesses_us = stats.prewarm_witnesses_us,
                    prewarm_insert_lookups_us = stats.prewarm_insert_lookups_us,
                    seal_def_cache_entries = self.seal_def_cache.len(),
                    resolved_seal_cache_entries = self.resolved_seal_cache.len(),
                    duplicate_seal_def_cache_entries = self.duplicate_seal_def_cache.len(),
                    duplicate_witness_cache_entries = self.duplicate_witness_cache.len(),
                    contract_cache_max_entries = contract_cache_max_entries(),
                    "Slow rgb-std stage"
                );
            }
            evaluate_result?;
            Ok(Articles::with(semantics, issue, sig, sig_validator)?)
        })()
        .map_err(MultiError::A)?;

        self.ledger
            .upgrade_apis(articles)
            .map_err(MultiError::from_other_a)?;
        Ok(())
    }

    pub(crate) fn consume_internal_predecoded_operations<E>(
        &mut self,
        reader: &mut StrictReader<impl ReadRaw>,
        mut operations: Vec<OperationSeals<P::Seal>>,
        mut seal_resolver: impl FnMut(&Operation) -> BTreeMap<u16, <P::Seal as RgbSeal>::Definition>,
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
            let genesis = Genesis::strict_decode(reader)?;
            let issue = Issue { version: issue_version, meta, codex, genesis };
            if issue.contract_id() != self.contract_id {
                return Err(ConsumeError::UnknownContract(issue.contract_id()));
            }
            let genesis_operations = ConsignmentGenesisOperations::from_issue(&issue);

            let evaluate_started_at = Instant::now();
            let previous_stats =
                CONSUME_STATS.with(|stats| stats.replace(Some(ConsumeStats::default())));
            let operation_count = operations.len();
            with_consume_stats(|stats| stats.decoded_ops += operation_count);

            for operation_seals in &mut operations {
                let definitions_cover_outputs = operation_seals
                    .operation
                    .destructible_out
                    .iter()
                    .enumerate()
                    .all(|(op_out, cell)| {
                        u16::try_from(op_out)
                            .ok()
                            .and_then(|op_out| operation_seals.defined_seals.get(&op_out))
                            .is_some_and(|seal| seal.auth_token() == cell.auth)
                    });

                if definitions_cover_outputs {
                    with_consume_stats(|stats| stats.predecoded_resolver_skips += 1);
                    continue;
                }

                with_consume_stats(|stats| stats.predecoded_resolver_calls += 1);
                operation_seals
                    .defined_seals
                    .extend(seal_resolver(&operation_seals.operation))
                    .map_err(|_| {
                        DecodeError::DataIntegrityError(format!(
                            "too many seals for {}",
                            operation_seals.operation.opid()
                        ))
                    })?;
            }

            let duplicate_cache_started_at = Instant::now();
            // Reset the per-consume seal-definition backstop up front, then let the prewarm below
            // repopulate it. Clearing here (rather than inside evaluate_commit, which runs after
            // prewarm) preserves the prewarmed entries through verification.
            self.consume_seal_defs.clear();
            let phase_started_at = Instant::now();
            let (known_ops, new_ops, opids) = self.partition_consume_operations(&operations);
            with_consume_stats(|stats| {
                stats.prewarm_partition_us += phase_started_at.elapsed().as_micros()
            });
            let phase_started_at = Instant::now();
            self.prewarm_known_operation_duplicate_caches(operations.len(), known_ops);
            with_consume_stats(|stats| {
                stats.prewarm_known_duplicates_us += phase_started_at.elapsed().as_micros()
            });
            let phase_started_at = Instant::now();
            self.preload_destructible_input_seals(&operations);
            with_consume_stats(|stats| {
                stats.prewarm_destructible_inputs_us += phase_started_at.elapsed().as_micros()
            });
            // See the default consume path above: new output seals are persisted idempotently and
            // never need a durable-membership preload before verification.
            let phase_started_at = Instant::now();
            self.preload_consume_witnesses(&new_ops);
            with_consume_stats(|stats| {
                stats.prewarm_witnesses_us += phase_started_at.elapsed().as_micros()
            });
            let phase_started_at = Instant::now();
            self.preload_consume_insert_lookups(operations.len(), new_ops);
            with_consume_stats(|stats| {
                stats.prewarm_insert_lookups_us += phase_started_at.elapsed().as_micros();
                stats.prewarm_total_us += duplicate_cache_started_at.elapsed().as_micros();
            });
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(duplicate_cache_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consume_prewarm_duplicate_caches",
                    elapsed_ms,
                    contract_id = ?self.contract_id,
                    operations = operation_count,
                    predecoded_operations = true,
                    duplicate_seal_def_cache_entries = self.duplicate_seal_def_cache.len(),
                    duplicate_witness_cache_entries = self.duplicate_witness_cache.len(),
                    "Slow rgb-std stage"
                );
            }

            let op_reader = PredecodedOpReader(opids.into_iter().zip(operations).collect());
            self.stage_genesis_verification_memory(&genesis_operations.contract);
            let evaluate_result = self.evaluate_commit(op_reader);
            let stats = CONSUME_STATS
                .with(|stats| stats.replace(previous_stats))
                .unwrap_or_default();
            record_last_consume_op_counts(&stats);
            record_last_consume_prewarm_phase_stats(&stats);
            if let Some(elapsed_ms) = slow_rgb_stage_elapsed(evaluate_started_at) {
                tracing::warn!(
                    operation = "rgb_std",
                    stage = "consume_evaluate",
                    elapsed_ms,
                    contract_id = ?self.contract_id,
                    predecoded_operations = true,
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
                    apply_witness_total_us = stats.apply_witness_total_us,
                    apply_witness_dupcache_us = stats.apply_witness_dupcache_us,
                    apply_witness_retain_us = stats.apply_witness_retain_us,
                    include_resolve_us = stats.include_resolve_us,
                    include_has_witness_us = stats.include_has_witness_us,
                    include_cli_witness_us = stats.include_cli_witness_us,
                    include_ops_by_witness_us = stats.include_ops_by_witness_us,
                    include_add_us = stats.include_add_us,
                    include_aux_us = stats.include_aux_us,
                    apply_seals_total_us = stats.apply_seals_total_us,
                    seals_cached_dup_us = stats.seals_cached_dup_us,
                    seals_missing_scan_us = stats.seals_missing_scan_us,
                    seals_match_us = stats.seals_match_us,
                    seals_dup_finalize_us = stats.seals_dup_finalize_us,
                    seals_insert_us = stats.seals_insert_us,
                    seals_add_seals_us = stats.seals_add_seals_us,
                    apply_operation_total_us = stats.apply_operation_total_us,
                    apply_operation_opid_us = stats.apply_operation_opid_us,
                    apply_operation_stage_inputs_us = stats.apply_operation_stage_inputs_us,
                    apply_operation_ledger_apply_us = stats.apply_operation_ledger_apply_us,
                    apply_operation_cache_us = stats.apply_operation_cache_us,
                    known_materialized_skips = stats.known_materialized_skips,
                    predecoded_resolver_calls = stats.predecoded_resolver_calls,
                    predecoded_resolver_skips = stats.predecoded_resolver_skips,
                    prewarm_total_us = stats.prewarm_total_us,
                    prewarm_partition_us = stats.prewarm_partition_us,
                    prewarm_known_duplicates_us = stats.prewarm_known_duplicates_us,
                    prewarm_destructible_inputs_us = stats.prewarm_destructible_inputs_us,
                    prewarm_output_seals_us = stats.prewarm_output_seals_us,
                    prewarm_witnesses_us = stats.prewarm_witnesses_us,
                    prewarm_insert_lookups_us = stats.prewarm_insert_lookups_us,
                    seal_def_cache_entries = self.seal_def_cache.len(),
                    resolved_seal_cache_entries = self.resolved_seal_cache.len(),
                    duplicate_seal_def_cache_entries = self.duplicate_seal_def_cache.len(),
                    duplicate_witness_cache_entries = self.duplicate_witness_cache.len(),
                    contract_cache_max_entries = contract_cache_max_entries(),
                    "Slow rgb-std stage"
                );
            }
            evaluate_result?;
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
        LAST_CONSUME_PHASE_STATS.with(|stats| stats.set(LastConsumePhaseStats::default()));
        // Fresh per-consume set of not-known ops applied in this run (see `applied_new_ops`); keeps
        // `apply_seals`'s new-op fast path bounded to this consignment's cohort.
        self.applied_new_ops.clear();
        // NB: `consume_seal_defs` is intentionally NOT cleared here. The consume prewarm populates
        // it *before* calling this method, and clearing it here would wipe those 80k+
        // prewarmed known-op/input-cell seal defs before verification ever reads them —
        // leaving known_seal / are_seals_known to re-hit the DB per op (the ~130s + ~40s
        // residuals). The two prewarming consume paths clear it up front; the one
        // non-prewarming caller is a fresh contract whose map is already empty.

        // The `consume_evaluate` stage timed by the caller wraps this whole method, i.e. verify
        // *and* both commit_transaction calls. A slow `consume_evaluate` therefore is not
        // necessarily verification CPU; split the three phases so a deep-chain consume can be
        // attributed to verification, ledger commit, or pile commit.
        let diag = verify_diag_enabled();
        let verify_started_at = diag.then(Instant::now);
        self.known_verification_memory.clear();
        let verify_result = self.evaluate(reader);
        self.known_verification_memory.clear();
        if let Err(err) = verify_result {
            // Deferred witnesses were never persisted; the duplicate-witness marks `apply_witness`
            // added for them must be rolled back too. Otherwise a retry of the same consignment
            // would classify these ops as fully known and skip `apply_witness` entirely, leaving
            // their witnesses permanently missing from the pile.
            for (opid, witness) in self.pending_witness_updates.take() {
                self.duplicate_witness_cache
                    .remove(&(opid, witness.published.pub_id()));
            }
            return Err(err);
        }
        let pending_witness_update_count = self.pending_witness_updates.len();
        let flush_witness_started_at = diag.then(Instant::now);
        let applied_witness_update_count = self.flush_pending_witness_updates();
        let flush_witness_ms = flush_witness_started_at.map(|at| at.elapsed().as_millis());
        let verify_ms = verify_started_at.map(|at| at.elapsed().as_millis());

        let ledger_commit_started_at = diag.then(Instant::now);
        if let Err(err) = self.ledger.commit_transaction() {
            panic!("ledger commit_transaction failed: {err}");
        }
        let ledger_commit_ms = ledger_commit_started_at.map(|at| at.elapsed().as_millis());

        let pile_commit_started_at = diag.then(Instant::now);
        self.pile.session().commit_transaction();
        let pile_commit_ms = pile_commit_started_at.map(|at| at.elapsed().as_millis());

        if let (
            Some(verify_ms),
            Some(flush_witness_ms),
            Some(ledger_commit_ms),
            Some(pile_commit_ms),
        ) = (verify_ms, flush_witness_ms, ledger_commit_ms, pile_commit_ms)
        {
            LAST_CONSUME_PHASE_STATS.with(|stats| {
                stats.set(LastConsumePhaseStats {
                    recorded: true,
                    verify_ms,
                    flush_witness_ms,
                    pending_witness_updates: pending_witness_update_count,
                    applied_witness_updates: applied_witness_update_count,
                    ledger_commit_ms,
                    pile_commit_ms,
                    prewarm_total_us: 0,
                    prewarm_partition_us: 0,
                    prewarm_known_duplicates_us: 0,
                    prewarm_destructible_inputs_us: 0,
                    prewarm_output_seals_us: 0,
                    prewarm_witnesses_us: 0,
                    prewarm_insert_lookups_us: 0,
                })
            });
            tracing::warn!(
                target: "rgb_verify_diag",
                operation = "rgb_std",
                stage = "evaluate_commit_breakdown",
                contract_id = ?self.contract_id,
                verify_ms,
                flush_witness_ms,
                pending_witness_updates = pending_witness_update_count,
                applied_witness_updates = applied_witness_update_count,
                ledger_commit_ms,
                pile_commit_ms,
                "evaluate_commit phase breakdown"
            );
        }
        Ok(())
    }
}

impl<S: Stock, P: Pile> Memory for Contract<S, P> {
    fn destructible(&self, addr: CellAddr) -> Option<StateCell> {
        self.ledger
            .state()
            .raw
            .destructible(addr)
            .or_else(|| self.known_verification_memory.destructible(addr))
            .or_else(|| self.genesis_verification_memory.destructible(addr))
    }

    fn immutable(&self, addr: CellAddr) -> Option<StateValue> {
        self.ledger
            .state()
            .raw
            .immutable(addr)
            .or_else(|| self.known_verification_memory.immutable(addr))
            .or_else(|| self.genesis_verification_memory.immutable(addr))
    }
}

impl<S: Stock, P: Pile> ContractApi<P::Seal> for Contract<S, P> {
    fn contract_id(&self) -> ContractId { self.ledger.contract_id() }
    fn codex(&self) -> &Codex { self.ledger.articles().codex() }
    fn repo(&self) -> &impl LibRepo { self.ledger.articles() }
    fn memory(&self) -> &impl Memory { self }
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
        let known = ps.op_witness_ids(opid).contains(&wid)
            && ps.has_witness(wid)
            && ps.cli_witness(wid) == witness.client;
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
        } else if let Some(definition) = self.consume_seal_defs.get(&addr) {
            // Non-evicting prewarm backstop: input-cell seals batch-loaded by
            // `preload_destructible_input_seals` survive here after `seal_def_cache` evicts them,
            // so a deep closure resolves them from memory instead of a per-cell DB round-trip.
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
            } else {
                // The cell has a witness-relative definition (to_src was None) but the producing
                // operation's witness cannot be retrieved, so the seal is unresolvable and accept
                // is about to fail with SealUnknown. Dump the producer's live witness view so the
                // gate-vs-accept witness-status divergence can be pinned.
                let wid_statuses = {
                    let mut ps = self.pile.session();
                    ps.op_witness_ids(addr.opid)
                        .into_iter()
                        .map(|wid| (format!("{wid}"), ps.witness_status(wid)))
                        .collect::<Vec<_>>()
                };
                tracing::warn!(
                    target: "rgb_boundary_diag",
                    operation = "rgb_std",
                    stage = "known_seal_unresolved",
                    contract_id = ?self.contract_id,
                    cell = %addr,
                    opid = ?addr.opid,
                    wid_statuses = ?wid_statuses,
                    "witness-relative known-seal cell has no retrievable producer witness"
                );
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
            // Compare the provided definition against the stored one from either the bounded cache
            // or the non-evicting prewarm backstop (`consume_seal_defs`, populated from known-op
            // aux matches). Matching stored defs is exactly what
            // `seal_definitions_match` confirms, so a hit here is authoritative and
            // skips the per-op DB round-trip after the bounded cache evicts the
            // prewarmed entries.
            self.seal_def_cache
                .get(&addr)
                .or_else(|| self.consume_seal_defs.get(&addr))
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

        // A genuinely-new op (not yet valid/known) cannot have its seal definitions stored from
        // previously accepted data, so `are_seals_known` is false. Skip the per-op materialized
        // `seal_definitions_match` DB round-trip and take the full-verification path such an op
        // needs anyway. Only known ops (in `valid_cache`, i.e. `is_known`) reach the DB check. This
        // removes the seals_known_db storm that dominated deep full-closure accepts (~162s) with no
        // persistent cache growth. Conservative: a rare op whose seals were stored without the op
        // becoming valid falls back to full verification rather than being skipped — never unsound.
        if !self.valid_cache.contains(&opid) {
            return false;
        }

        let db_started_at = Instant::now();
        let mut ps = self.pile.session();
        let known = ps.seal_definitions_match(opid, seals);
        drop(ps);
        let db_elapsed_ms = db_started_at.elapsed().as_millis();
        with_consume_stats(|stats| {
            stats.seals_known_db_checks += 1;
            stats.seals_known_db_elapsed_ms += db_elapsed_ms;
        });
        self.prune_contract_caches();

        if known {
            self.seal_def_cache.extend(
                seals
                    .iter()
                    .map(|(no, seal)| (CellAddr::new(opid, *no), seal.clone())),
            );
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
        let total_started = Instant::now();
        let opid_started = Instant::now();
        let opid = op.opid();
        let opid_us = opid_started.elapsed().as_micros();

        let stage_inputs_started = Instant::now();
        self.stage_missing_verification_inputs(op.as_operation())
            .expect("unable to stage verification inputs");
        let stage_inputs_us = stage_inputs_started.elapsed().as_micros();

        let ledger_apply_started = Instant::now();
        self.ledger.apply(op).expect("unable to apply operation");
        let ledger_apply_us = ledger_apply_started.elapsed().as_micros();

        let cache_started = Instant::now();
        self.valid_cache.insert(opid);
        // rgb-core calls `apply_operation` only for not-known ops, before `apply_seals` for the
        // same op — record it so `apply_seals` can skip the guaranteed-false duplicate DB check.
        self.applied_new_ops.insert(opid);
        self.remove_op_aux_cache_entry(opid);
        self.clear_owned_state_status_cache();
        let cache_us = cache_started.elapsed().as_micros();
        let total_us = total_started.elapsed().as_micros();

        with_consume_stats(|stats| {
            stats.apply_operation_total_us += total_us;
            stats.apply_operation_opid_us += opid_us;
            stats.apply_operation_stage_inputs_us += stage_inputs_us;
            stats.apply_operation_ledger_apply_us += ledger_apply_us;
            stats.apply_operation_cache_us += cache_us;
        });
    }

    fn stage_known_operation(&mut self, opid: Opid, operation: &Operation) {
        self.known_verification_memory
            .insert_operation_outputs(opid, operation);
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
        let total_started = Instant::now();
        let applied_new_operation = self.applied_new_ops.contains(&opid);

        let cached_dup_started = Instant::now();
        let cached_duplicate = !applied_new_operation
            && seals.iter().all(|(no, seal)| {
                let addr = CellAddr::new(opid, *no);
                self.duplicate_seal_def_cache.contains(&addr)
                    && self
                        .seal_def_cache
                        .get(&addr)
                        .is_some_and(|stored| stored == seal)
            });
        let cached_dup_us = cached_dup_started.elapsed().as_micros();
        if cached_duplicate {
            self.remove_op_aux_cache_entry(opid);
            let total_us = total_started.elapsed().as_micros();
            with_consume_stats(|stats| {
                stats.duplicate_seal_updates += 1;
                stats.apply_seals_total_us += total_us;
                stats.seals_cached_dup_us += cached_dup_us;
            });
            return;
        }

        let missing_started = Instant::now();
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
        let missing_us = missing_started.elapsed().as_micros();

        let match_started = Instant::now();
        // Genuinely-new ops take precedence over cache hits. The output-seal prewarm may have
        // found matching immutable bytes through a contract-wide materialized row, but that does
        // not prove this wallet's pile membership exists. Always run the idempotent `add_seals`
        // path for an op applied in this consume; known ops may keep the cached/durable shortcut.
        let duplicate =
            output_seals_are_already_persisted(applied_new_operation, missing.is_empty(), || {
                let mut ps = self.pile.session();
                ps.seal_definitions_match(opid, &seals)
            });
        let match_us = match_started.elapsed().as_micros();
        if duplicate {
            let dup_finalize_started = Instant::now();
            self.seal_def_cache.extend(
                seals
                    .iter()
                    .map(|(no, seal)| (CellAddr::new(opid, *no), seal.clone())),
            );
            // Same intra-consignment backstop as the fresh-insert path below: keep these producer
            // cells resolvable from memory after `seal_def_cache` prunes them (see comment there).
            self.consume_seal_defs.extend(
                seals
                    .iter()
                    .map(|(no, seal)| (CellAddr::new(opid, *no), seal.clone())),
            );
            self.duplicate_seal_def_cache
                .extend(seals.keys().map(|no| CellAddr::new(opid, *no)));
            self.prune_contract_caches();
            self.remove_op_aux_cache_entry(opid);
            let dup_finalize_us = dup_finalize_started.elapsed().as_micros();
            let total_us = total_started.elapsed().as_micros();
            with_consume_stats(|stats| {
                stats.duplicate_seal_updates += 1;
                stats.apply_seals_total_us += total_us;
                stats.seals_cached_dup_us += cached_dup_us;
                stats.seals_missing_scan_us += missing_us;
                stats.seals_match_us += match_us;
                stats.seals_dup_finalize_us += dup_finalize_us;
            });
            return;
        }
        let insert_started = Instant::now();
        for (no, seal) in &seals {
            let addr = CellAddr::new(opid, *no);
            self.seal_def_cache.insert(addr, seal.clone());
            // Non-evicting intra-consignment backstop: this op's freshly-applied output seals are
            // the producer cells that *later* new ops in the same closure consume.
            // `seal_def_cache` is bounded and prunes them mid-consume, forcing
            // `known_seal` back to a per-cell DB round trip on deep closures (~5k
            // checks ≈ 136s). Mirroring them here (cleared per consume, ~working-set
            // MB) keeps that resolution in memory. The pile-time `seals_for` prewarm
            // cannot cover these because they are not stored until this very `apply_seals` runs.
            self.consume_seal_defs.insert(addr, seal.clone());
            self.resolved_seal_cache.remove(&addr);
            self.duplicate_seal_def_cache.insert(addr);
        }
        self.prune_contract_caches();
        let insert_us = insert_started.elapsed().as_micros();
        let add_seals_started = Instant::now();
        self.pile.session().add_seals(opid, seals);
        let add_seals_us = add_seals_started.elapsed().as_micros();
        self.remove_op_aux_cache_entry(opid);
        self.clear_owned_state_status_cache();
        let total_us = total_started.elapsed().as_micros();
        with_consume_stats(|stats| {
            stats.apply_seals_total_us += total_us;
            stats.seals_cached_dup_us += cached_dup_us;
            stats.seals_missing_scan_us += missing_us;
            stats.seals_match_us += match_us;
            stats.seals_insert_us += insert_us;
            stats.seals_add_seals_us += add_seals_us;
        });
    }

    fn apply_witness(&mut self, opid: Opid, witness: SealWitness<P::Seal>) {
        let total_started = Instant::now();
        with_consume_stats(|stats| stats.witness_updates += 1);
        let wid = witness.published.pub_id();
        self.pending_witness_updates.push((opid, witness));
        let dupcache_started = Instant::now();
        self.duplicate_witness_cache.insert((opid, wid));
        let retain_started = Instant::now();
        self.resolved_seal_cache.retain(|addr, _| addr.opid != opid);
        let now = Instant::now();
        let dupcache_us = (retain_started - dupcache_started).as_micros();
        let retain_us = (now - retain_started).as_micros();
        let total_us = (now - total_started).as_micros();
        with_consume_stats(|stats| {
            stats.apply_witness_total_us += total_us;
            stats.apply_witness_dupcache_us += dupcache_us;
            stats.apply_witness_retain_us += retain_us;
        });
    }
}

fn decode_operation_aux<Seal: RgbSeal, R: ReadRaw>(
    reader: &mut StrictReader<R>,
    operation: Operation,
    seal_resolver: &mut impl FnMut(&Operation) -> BTreeMap<u16, Seal::Definition>,
) -> Result<OperationSeals<Seal>, DecodeError>
where
    Seal::Client: StrictDecode,
    Seal::Published: StrictDecode,
    Seal::WitnessId: StrictDecode,
{
    let mut defined_seals = SmallOrdMap::strict_decode(reader)?;
    with_consume_stats(|stats| stats.decoded_ops += 1);
    defined_seals
        .extend(seal_resolver(&operation))
        .map_err(|_| {
            DecodeError::DataIntegrityError(format!("too many seals for {}", operation.opid()))
        })?;
    let witness = Option::<SealWitness<Seal>>::strict_decode(reader)?;

    Ok(OperationSeals { operation, defined_seals, witness })
}

fn decode_consignment_operations<Seal: RgbSeal, R: ReadRaw>(
    reader: &mut StrictReader<R>,
    genesis_operation: Operation,
    mut seal_resolver: impl FnMut(&Operation) -> BTreeMap<u16, Seal::Definition>,
) -> Result<Vec<OperationSeals<Seal>>, DecodeError>
where
    Seal::Client: StrictDecode,
    Seal::Published: StrictDecode,
    Seal::WitnessId: StrictDecode,
{
    let genesis = decode_operation_aux(reader, genesis_operation, &mut seal_resolver)?;
    let count = u32::strict_decode(reader)?;
    if count > MAX_CONSIGNMENT_OPS {
        return Err(DecodeError::DataIntegrityError(format!(
            "number of operations in contract consignment ({count}) exceeds maximum allowed \
             ({MAX_CONSIGNMENT_OPS})"
        )));
    }

    let mut operations = Vec::with_capacity(count as usize + 1);
    operations.push(genesis);

    for _ in 0..count {
        let operation = Operation::strict_decode(reader)?;
        let operation_seals = decode_operation_aux(reader, operation, &mut seal_resolver)?;
        operations.push(operation_seals);
    }

    Ok(operations)
}

/// Holds `(opid, operation)` pairs with the `opid` memoized at decode/partition time, so `verify`
/// reuses the commitment via `read_operation_with_opid` instead of recomputing `opid()` per op.
struct PredecodedOpReader<Seal: RgbSeal>(VecDeque<(Opid, OperationSeals<Seal>)>);

impl<Seal: RgbSeal> ReadOperation for PredecodedOpReader<Seal> {
    type Seal = Seal;

    fn read_operation(
        &mut self,
    ) -> Result<Option<OperationSeals<Self::Seal>>, impl Error + 'static> {
        Result::<_, core::convert::Infallible>::Ok(self.0.pop_front().map(|(_, op)| op))
    }

    fn read_operation_with_opid(
        &mut self,
    ) -> Result<Option<(Opid, OperationSeals<Self::Seal>)>, impl Error + 'static> {
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
            <P::Seal as RgbSeal>::Client: Clone,
            <P::Seal as RgbSeal>::Client: StrictDumb + StrictEncode,
            <P::Seal as RgbSeal>::Published: Clone,
            <P::Seal as RgbSeal>::Published: StrictDumb + StrictEncode,
            <P::Seal as RgbSeal>::WitnessId: StrictEncode,
        {
            let file = BinFile::<CONSIGN_MAGIC_NUMBER, CONSIGN_VERSION>::create_new(path)?;
            self.consign(terminals, StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file)))
        }
    }
}
