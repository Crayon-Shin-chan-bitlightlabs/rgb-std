// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0

use core::error::Error as StdError;

use amplify::confinement::SmallOrdMap;
use amplify::MultiError;
use hypersonic::{CellAddr, ContractId, Operation, Opid, Stock, Transition};
use rgb::RgbSeal;

use crate::{Articles, EffectiveState, OpRels, Pile, Stockpile, Witness, WitnessStatus};

/// Experimental session-oriented persistence traits for backends which need to reuse a single
/// mutable runtime resource, such as a dedicated database connection.
///
/// These traits are intentionally additive and are not wired into [`crate::Contract`] yet.
/// They document the API shape required to eliminate implementation-side mutexes around shared
/// connection state.
pub trait StockReadSession {
    type Error: StdError;

    fn articles(&self) -> &Articles;
    fn state(&self) -> &EffectiveState;

    fn is_valid(&mut self, opid: Opid) -> Result<bool, Self::Error>;
    fn has_operation(&mut self, opid: Opid) -> Result<bool, Self::Error>;
    fn operation_count(&mut self) -> Result<u64, Self::Error>;
    fn operation(&mut self, opid: Opid) -> Result<Operation, Self::Error>;
    fn operations(&mut self) -> Result<Vec<(Opid, Operation)>, Self::Error>;
    fn transition(&mut self, opid: Opid) -> Result<Transition, Self::Error>;
    fn trace(&mut self) -> Result<Vec<(Opid, Transition)>, Self::Error>;
    fn read_by(&mut self, addr: CellAddr) -> Result<Vec<Opid>, Self::Error>;
    fn spent_by(&mut self, addr: CellAddr) -> Result<Option<Opid>, Self::Error>;
}

pub trait StockWriteSession: StockReadSession {
    type SemanticError: StdError;

    fn mark_valid(&mut self, opid: Opid) -> Result<(), Self::Error>;
    fn mark_invalid(&mut self, opid: Opid) -> Result<(), Self::Error>;
    fn update_articles(
        &mut self,
        f: impl FnOnce(&mut Articles) -> Result<bool, Self::SemanticError>,
    ) -> Result<bool, MultiError<Self::SemanticError, Self::Error>>;
    fn update_state<R>(
        &mut self,
        f: impl FnOnce(&mut EffectiveState, &Articles) -> R,
    ) -> Result<R, Self::Error>;
    fn add_operation(&mut self, opid: Opid, operation: &Operation) -> Result<(), Self::Error>;
    fn add_transition(&mut self, opid: Opid, transition: &Transition) -> Result<(), Self::Error>;
    fn add_reading(&mut self, addr: CellAddr, spender: Opid) -> Result<(), Self::Error>;
    fn add_spending(&mut self, spent: CellAddr, spender: Opid) -> Result<(), Self::Error>;
    fn commit_transaction(&mut self) -> Result<(), Self::Error>;
}

pub trait PileReadSession {
    type Seal: RgbSeal;
    type Error: StdError;

    fn pub_witness(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
    ) -> Result<<Self::Seal as RgbSeal>::Published, Self::Error>;
    fn has_witness(&mut self, wid: <Self::Seal as RgbSeal>::WitnessId)
        -> Result<bool, Self::Error>;
    fn cli_witness(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
    ) -> Result<<Self::Seal as RgbSeal>::Client, Self::Error>;
    fn witness_status(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
    ) -> Result<WitnessStatus, Self::Error>;
    fn witness_ids(&mut self) -> Result<Vec<<Self::Seal as RgbSeal>::WitnessId>, Self::Error>;
    fn witnesses(&mut self) -> Result<Vec<Witness<Self::Seal>>, Self::Error>;
    fn op_witness_ids(
        &mut self,
        opid: Opid,
    ) -> Result<Vec<<Self::Seal as RgbSeal>::WitnessId>, Self::Error>;
    fn ops_by_witness_id(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
    ) -> Result<Vec<Opid>, Self::Error>;
    fn seal(
        &mut self,
        addr: CellAddr,
    ) -> Result<Option<<Self::Seal as RgbSeal>::Definition>, Self::Error>;
    fn seals(
        &mut self,
        opid: Opid,
        up_to: u16,
    ) -> Result<SmallOrdMap<u16, <Self::Seal as RgbSeal>::Definition>, Self::Error>;
    fn op_relations(&mut self, opid: Opid, up_to: u16) -> Result<OpRels<Self::Seal>, Self::Error>;
}

pub trait PileWriteSession: PileReadSession {
    fn add_witness(
        &mut self,
        opid: Opid,
        wid: <Self::Seal as RgbSeal>::WitnessId,
        published: &<Self::Seal as RgbSeal>::Published,
        anchor: &<Self::Seal as RgbSeal>::Client,
        status: WitnessStatus,
    ) -> Result<(), Self::Error>;
    fn add_seals(
        &mut self,
        opid: Opid,
        seals: SmallOrdMap<u16, <Self::Seal as RgbSeal>::Definition>,
    ) -> Result<(), Self::Error>;
    fn update_witness_status(
        &mut self,
        wid: <Self::Seal as RgbSeal>::WitnessId,
        status: WitnessStatus,
    ) -> Result<(), Self::Error>;
    fn commit_transaction(&mut self) -> Result<(), Self::Error>;
}

pub trait ContractSession {
    type Stock<'session>: StockWriteSession<Error = Self::StockError>
    where
        Self: 'session;
    type Pile<'session>: PileWriteSession<Seal = Self::Seal, Error = Self::PileError>
    where
        Self: 'session;
    type Seal: RgbSeal;
    type StockError: StdError;
    type PileError: StdError;

    fn stock(&mut self) -> &mut Self::Stock<'_>;
    fn pile(&mut self) -> &mut Self::Pile<'_>;
}

pub trait SessionStockpile: Stockpile {
    type Session<'session>: ContractSession<
        Seal = <<Self as Stockpile>::Pile as Pile>::Seal,
        StockError = <<Self as Stockpile>::Stock as Stock>::Error,
        PileError = <<Self as Stockpile>::Pile as Pile>::Error,
    >
    where
        Self: 'session;
    type SessionError: StdError;

    fn with_contract_session<T>(
        &mut self,
        contract_id: ContractId,
        f: impl FnOnce(&mut Self::Session<'_>) -> Result<T, Self::SessionError>,
    ) -> Result<Option<T>, Self::SessionError>;
}
