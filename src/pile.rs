// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0

use alloc::collections::BTreeSet;
use core::error::Error as StdError;
use core::fmt::Debug;
use core::marker::PhantomData;
use core::num::NonZeroU64;
use std::collections::HashSet;

use amplify::confinement::SmallOrdMap;
use hypersonic::Opid;
use rgb::RgbSeal;
use single_use_seals::{PublishedWitness, SealWitness};

use crate::CellAddr;

const SEALS_MATCH_BATCH_UP_TO_MAX: u16 = 2048;

/// Witness transaction confirmation status.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Display, Default)]
#[display(lowercase)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(rename_all = "camelCase"))]
pub enum WitnessStatus {
    Genesis,
    #[display(inner)]
    Mined(NonZeroU64),
    Offchain,
    Tentative,
    #[default]
    Archived,
}

impl WitnessStatus {
    const GENESIS: u64 = 0;
    const TENTATIVE: u64 = u64::MAX ^ 0x01;
    const OFFCHAIN: u64 = u64::MAX ^ 0x02;
    const ARCHIVED: u64 = u64::MAX;

    pub fn is_mined(&self) -> bool {
        matches!(self, Self::Mined(_))
    }
    pub fn is_valid(&self) -> bool {
        !matches!(self, Self::Archived)
    }
    pub fn is_tentative(&self) -> bool {
        matches!(self, Self::Tentative)
    }
    pub fn is_archived(&self) -> bool {
        matches!(self, Self::Archived)
    }
    pub fn is_offchain(&self) -> bool {
        matches!(self, Self::Offchain)
    }
    pub fn is_mature(self, last_block_height: u64, min_confirmations: u32) -> bool {
        let Self::Mined(height) = self else {
            return false;
        };
        let Some(confirmations) = last_block_height
            .checked_sub(height.get())
            .and_then(|depth| depth.checked_add(1))
        else {
            return false;
        };
        confirmations >= min_confirmations as u64
    }

    fn quasi_height(&self) -> u64 {
        match self {
            Self::Genesis => Self::GENESIS,
            Self::Archived => Self::ARCHIVED,
            Self::Tentative => Self::TENTATIVE,
            Self::Offchain => Self::OFFCHAIN,
            Self::Mined(h) => h.get(),
        }
    }

    pub fn is_better(self, other: Self) -> bool {
        self.quasi_height() < other.quasi_height()
    }
    pub fn is_worse(self, other: Self) -> bool {
        !self.is_better(other)
    }
    pub fn best(self, other: Self) -> Self {
        if self.is_better(other) {
            self
        } else {
            other
        }
    }
    pub fn worst(self, other: Self) -> Self {
        if self.is_worse(other) {
            self
        } else {
            other
        }
    }
}

impl From<[u8; 8]> for WitnessStatus {
    fn from(value: [u8; 8]) -> Self {
        let depth = u64::from_be_bytes(value);
        let height = u64::MAX - depth;
        match height {
            Self::GENESIS => Self::Genesis,
            Self::ARCHIVED => Self::Archived,
            Self::TENTATIVE => Self::Tentative,
            Self::OFFCHAIN => Self::Offchain,
            h => Self::Mined(NonZeroU64::new(h).expect("GENESIS=0 already matched")),
        }
    }
}

impl From<WitnessStatus> for [u8; 8] {
    fn from(value: WitnessStatus) -> Self {
        (u64::MAX - value.quasi_height()).to_be_bytes()
    }
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize))]
pub struct Witness<Seal: RgbSeal> {
    pub id: Seal::WitnessId,
    pub published: Seal::Published,
    pub client: Seal::Client,
    pub status: WitnessStatus,
    pub opids: HashSet<Opid>,
}

#[derive(Clone, Debug)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize),
    serde(bound = "Seal::WitnessId: serde::Serialize, Seal::Definition: serde::Serialize")
)]
pub struct OpRels<Seal: RgbSeal> {
    pub opid: Opid,
    pub witness_ids: BTreeSet<Seal::WitnessId>,
    pub defines: SmallOrdMap<u16, Seal::Definition>,
    #[cfg_attr(feature = "serde", serde(skip))]
    pub _phantom: PhantomData<Seal>,
}

/// A session encapsulates all I/O access to a [`Pile`].
///
/// Callers open one session per logical operation and forward it through the call chain.
/// For lock-free backends (e.g. file-system) the session is simply `&'s mut Self`.
pub trait PileSession {
    type Seal: RgbSeal;
    type Error: StdError;

    // ── read ──────────────────────────────────────────────────────────────

    fn pub_witness(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
    ) -> <Self::Seal as RgbSeal>::Published;

    fn has_witness(&mut self, wid: <Self::Seal as RgbSeal>::WitnessId) -> bool;

    fn cli_witness(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
    ) -> <Self::Seal as RgbSeal>::Client;

    fn witness_status(&mut self, wid: <Self::Seal as RgbSeal>::WitnessId) -> WitnessStatus;

    fn witness_statuses_for(
        &mut self,
        witness_ids: impl IntoIterator<Item = <Self::Seal as RgbSeal>::WitnessId>,
    ) -> Vec<(<Self::Seal as RgbSeal>::WitnessId, WitnessStatus)> {
        witness_ids
            .into_iter()
            .map(|wid| {
                let status = self.witness_status(wid);
                (wid, status)
            })
            .collect()
    }

    fn witness_ids(&mut self) -> Vec<<Self::Seal as RgbSeal>::WitnessId>;

    fn witness_statuses(&mut self) -> Vec<(<Self::Seal as RgbSeal>::WitnessId, WitnessStatus)> {
        self.witness_ids()
            .into_iter()
            .map(|wid| {
                let status = self.witness_status(wid);
                (wid, status)
            })
            .collect()
    }

    fn witness_statuses_requiring_update(
        &mut self,
        last_block_height: u64,
        min_confirmations: u32,
    ) -> Vec<(<Self::Seal as RgbSeal>::WitnessId, WitnessStatus)> {
        self.witness_statuses()
            .into_iter()
            .filter(|(_, status)| !status.is_mature(last_block_height, min_confirmations))
            .collect()
    }

    fn witnesses(&mut self) -> Vec<Witness<Self::Seal>>;

    fn op_witness_ids(&mut self, opid: Opid) -> Vec<<Self::Seal as RgbSeal>::WitnessId>;

    fn ops_by_witness_id(&mut self, wid: <Self::Seal as RgbSeal>::WitnessId) -> Vec<Opid>;

    fn known_seal_cells(&mut self) -> Vec<CellAddr>;

    fn seal(&mut self, addr: CellAddr) -> Option<<Self::Seal as RgbSeal>::Definition>;

    fn seals(
        &mut self,
        opid: Opid,
        up_to: u16,
    ) -> SmallOrdMap<u16, <Self::Seal as RgbSeal>::Definition>;

    fn witness_matches(&mut self, opid: Opid, witness: &SealWitness<Self::Seal>) -> bool {
        let wid = witness.published.pub_id();

        self.op_witness_ids(opid).contains(&wid)
            && self.has_witness(wid)
            && self.cli_witness(wid) == witness.client
    }

    fn seal_definitions_match(
        &mut self,
        opid: Opid,
        seals: &SmallOrdMap<u16, <Self::Seal as RgbSeal>::Definition>,
    ) -> bool {
        if seals.is_empty() {
            return true;
        }

        if let Some(up_to) = seals
            .keys()
            .next_back()
            .and_then(|no| no.checked_add(1))
            .filter(|up_to| *up_to <= SEALS_MATCH_BATCH_UP_TO_MAX)
        {
            let stored = self.seals(opid, up_to);

            return seals
                .iter()
                .all(|(no, seal)| stored.get(no).is_some_and(|stored| stored == seal));
        }

        seals.iter().all(|(no, seal)| {
            let addr = CellAddr::new(opid, *no);

            self.seal(addr).is_some_and(|stored| stored == *seal)
        })
    }

    fn preload_aux_reads(&mut self, ops: impl IntoIterator<Item = (Opid, u16)>) {
        let _ = ops;
    }

    fn known_boundary_opids_by_cells(
        &mut self,
        candidates: impl IntoIterator<Item = (Opid, u16)>,
        known_cells: &HashSet<CellAddr>,
    ) -> HashSet<Opid> {
        candidates
            .into_iter()
            .filter_map(|(opid, up_to)| {
                let rels = self.op_relations(opid, up_to);
                (!rels.defines.is_empty()
                    && rels
                        .defines
                        .keys()
                        .all(|no| known_cells.contains(&CellAddr::new(opid, *no))))
                .then_some(opid)
            })
            .collect()
    }

    fn op_relations(&mut self, opid: Opid, up_to: u16) -> OpRels<Self::Seal>;

    // ── write ─────────────────────────────────────────────────────────────

    fn add_witness(
        &mut self,
        opid: Opid,
        wid: <Self::Seal as RgbSeal>::WitnessId,
        published: &<Self::Seal as RgbSeal>::Published,
        anchor: &<Self::Seal as RgbSeal>::Client,
        status: WitnessStatus,
    );

    fn add_seals(
        &mut self,
        opid: Opid,
        seals: SmallOrdMap<u16, <Self::Seal as RgbSeal>::Definition>,
    );

    fn update_witness_status(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
        status: WitnessStatus,
    );

    fn commit_transaction(&mut self);

    /// Called after each [`Pile::add_witness`] inside a consume loop to ensure written data
    /// remains readable for subsequent verification steps within the same session.
    ///
    /// The default implementation calls [`Pile::commit_transaction`], which is required for
    /// file-based backends where uncommitted writes are not visible to reads.
    ///
    /// Backends that buffer writes in memory and make them immediately readable (e.g. a
    /// PostgreSQL-backed implementation using in-process aora buffers) should override this
    /// method as a no-op to avoid a per-operation database round-trip.  The outer
    /// [`Contract::evaluate_commit`] still calls [`Pile::commit_transaction`] once at the end
    /// to durably persist all accumulated writes.
    fn include_commit_transaction(&mut self) {
        self.commit_transaction();
    }
}

/// Persistent storage for contract witness and single-use seal definition data.
pub trait Pile {
    type Seal: RgbSeal;
    type Conf;
    type Error: StdError;

    /// Session type for all I/O access.
    /// For lock-free backends: `type Session<'s> = &'s mut Self`.
    type Session<'s>: PileSession<Seal = Self::Seal, Error = Self::Error>
    where
        Self: 's;

    fn new(conf: Self::Conf) -> Result<Self, Self::Error>
    where
        Self: Sized;

    fn load(conf: Self::Conf) -> Result<Self, Self::Error>
    where
        Self: Sized;

    /// Opens a session for all I/O operations.
    fn session(&mut self) -> Self::Session<'_>;
}

#[cfg(test)]
mod tests {
    #![cfg_attr(coverage_nightly, coverage(off))]
    use super::*;

    #[test]
    fn witness_status_bytes() {
        assert_eq!(WitnessStatus::Genesis, [0xFFu8; 8].into());
        assert_eq!(<[u8; 8]>::from(WitnessStatus::Genesis), [0xFFu8; 8]);
    }

    #[test]
    fn witness_status_ordering() {
        assert!(WitnessStatus::Genesis.is_better(WitnessStatus::Mined(NonZeroU64::new(1).unwrap())));
        assert!(WitnessStatus::Mined(NonZeroU64::new(10).unwrap())
            .is_better(WitnessStatus::Mined(NonZeroU64::new(100).unwrap())));
        assert!(
            WitnessStatus::Mined(NonZeroU64::new(1).unwrap()).is_better(WitnessStatus::Tentative)
        );
        assert!(WitnessStatus::Tentative.is_worse(WitnessStatus::Offchain));
        assert!(WitnessStatus::Offchain.is_better(WitnessStatus::Archived));
        assert!(WitnessStatus::Archived.is_worse(WitnessStatus::Genesis));
    }

    #[test]
    fn mined_witness_maturity_counts_confirmations() {
        let mined_at_100 = WitnessStatus::Mined(NonZeroU64::new(100).unwrap());

        assert!(mined_at_100.is_mature(100, 0));
        assert!(mined_at_100.is_mature(100, 1));
        assert!(mined_at_100.is_mature(101, 2));
        assert!(!mined_at_100.is_mature(100, 2));
        assert!(!mined_at_100.is_mature(99, 0));
        assert!(!WitnessStatus::Tentative.is_mature(100, 0));
        assert!(!WitnessStatus::Offchain.is_mature(100, 0));
    }
}
