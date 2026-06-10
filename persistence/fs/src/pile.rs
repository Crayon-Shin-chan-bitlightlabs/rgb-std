// Standard Library for RGB smart contracts
//
// SPDX-License-Identifier: Apache-2.0

use std::io;
use std::marker::PhantomData;
use std::path::PathBuf;

use amplify::confinement::SmallOrdMap;
use aora::file::{FileAoraIndex, FileAoraMap, FileAuraMap};
use aora::{AoraIndex, AoraMap, AuraMap, TransactionalMap};
use rgb::{CellAddr, OpRels, Opid, Pile, PileSession, RgbSeal, Witness, WitnessStatus};
use strict_encoding::{StrictDecode, StrictEncode};

const HOARD_MAGIC: u64 = u64::from_be_bytes(*b"RGBHOARD");
const CACHE_MAGIC: u64 = u64::from_be_bytes(*b"RGBCACHE");
const KEEP_MAGIC: u64 = u64::from_be_bytes(*b"RGBKEEPS");
const INDEX_MAGIC: u64 = u64::from_be_bytes(*b"RGBINDEX");
const STAND_MAGIC: u64 = u64::from_be_bytes(*b"RGBSTAND");
const MINE_MAGIC: u64 = u64::from_be_bytes(*b"RGBMINES");

#[derive(Debug)]
pub struct PileFs<Seal: RgbSeal>
where Seal::WitnessId: From<[u8; 32]> + Into<[u8; 32]>
{
    hoard: FileAoraMap<Seal::WitnessId, Seal::Client, HOARD_MAGIC, 1>,
    cache: FileAoraMap<Seal::WitnessId, Seal::Published, CACHE_MAGIC, 1>,
    keep: FileAoraMap<CellAddr, Seal::Definition, KEEP_MAGIC, 1, 34>,
    index: FileAoraIndex<Opid, Seal::WitnessId, INDEX_MAGIC, 1>,
    stand: FileAoraIndex<Seal::WitnessId, Opid, STAND_MAGIC, 1>,
    mine: FileAuraMap<Seal::WitnessId, WitnessStatus, MINE_MAGIC, 1, 32, 8>,
    _phantom: PhantomData<Seal>,
}

/// For the FS backend, the session IS `&mut PileFs` — zero overhead.
impl<Seal: RgbSeal> PileSession for &mut PileFs<Seal>
where
    Seal::Client: StrictEncode + StrictDecode,
    Seal::Published: Eq + StrictEncode + StrictDecode,
    Seal::WitnessId: From<[u8; 32]> + Into<[u8; 32]>,
{
    type Seal = Seal;
    type Error = io::Error;

    // ── read ──────────────────────────────────────────────────────────────
    fn pub_witness(&mut self, wid: Seal::WitnessId) -> Seal::Published {
        self.cache.get_expect(wid)
    }
    fn has_witness(&mut self, wid: Seal::WitnessId) -> bool { self.hoard.contains_key(wid) }
    fn cli_witness(&mut self, wid: Seal::WitnessId) -> Seal::Client { self.hoard.get_expect(wid) }
    fn witness_status(&mut self, wid: Seal::WitnessId) -> WitnessStatus {
        self.mine.get(wid).unwrap_or(WitnessStatus::Archived)
    }
    fn witness_ids(&mut self) -> impl Iterator<Item = Seal::WitnessId> { self.stand.keys() }
    fn op_witness_ids(&mut self, opid: Opid) -> impl ExactSizeIterator<Item = Seal::WitnessId> {
        self.index.get(opid)
    }
    fn ops_by_witness_id(&mut self, wid: Seal::WitnessId) -> impl ExactSizeIterator<Item = Opid> {
        self.stand.get(wid)
    }
    fn known_seal_cells(&mut self) -> impl Iterator<Item = CellAddr> {
        self.keep.iter().map(|(addr, _)| addr)
    }
    fn seal(&mut self, addr: CellAddr) -> Option<Seal::Definition> { self.keep.get(addr) }
    fn seals(&mut self, opid: Opid, up_to: u16) -> SmallOrdMap<u16, Seal::Definition> {
        let mut seals = SmallOrdMap::new();
        for no in 0..up_to {
            if let Some(seal) = self.keep.get(CellAddr::new(opid, no)) {
                let _ = seals.insert(no, seal);
            }
        }
        seals
    }
    fn witnesses(&mut self) -> impl Iterator<Item = Witness<Self::Seal>> {
        self.hoard.iter().map(|(wid, client)| {
            let published = self.cache.get_expect(wid);
            let status = self.mine.get_expect(wid);
            let opids = self.stand.get(wid).collect();
            Witness { id: wid, published, client, status, opids }
        })
    }
    fn op_relations(&mut self, opid: Opid, up_to: u16) -> OpRels<Self::Seal> {
        let seals = self.seals(opid, up_to);
        let witness_ids = self.index.get(opid).collect();
        OpRels { opid, witness_ids, defines: seals, _phantom: PhantomData }
    }

    // ── write ─────────────────────────────────────────────────────────────
    fn add_witness(
        &mut self,
        opid: Opid,
        wid: Seal::WitnessId,
        published: &Seal::Published,
        anchor: &Seal::Client,
        status: WitnessStatus,
    ) {
        self.index.push(opid, wid);
        self.stand.push(wid, opid);
        self.hoard.insert(wid, anchor);
        self.cache.insert(wid, published);
        if !self.mine.contains_key(wid) {
            self.mine.insert_only(wid, status);
        }
    }
    fn add_seals(&mut self, opid: Opid, seals: SmallOrdMap<u16, Seal::Definition>) {
        for (no, seal) in seals {
            self.keep.insert(CellAddr::new(opid, no), &seal)
        }
    }
    fn update_witness_status(&mut self, wid: Seal::WitnessId, status: WitnessStatus) {
        self.mine.update_only(wid, status);
    }
    fn commit_transaction(&mut self) { self.mine.commit_transaction(); }
}

impl<Seal: RgbSeal> Pile for PileFs<Seal>
where
    Seal::Client: StrictEncode + StrictDecode,
    Seal::Published: Eq + StrictEncode + StrictDecode,
    Seal::WitnessId: From<[u8; 32]> + Into<[u8; 32]>,
{
    type Seal = Seal;
    type Conf = PathBuf;
    type Error = io::Error;
    type Session<'s>
        = &'s mut Self
    where Self: 's;

    fn new(path: PathBuf) -> Result<Self, io::Error>
    where Self: Sized {
        Ok(Self {
            hoard: FileAoraMap::create_new(&path, "hoard")?,
            cache: FileAoraMap::create_new(&path, "cache")?,
            keep: FileAoraMap::create_new(&path, "keep")?,
            index: FileAoraIndex::create_new(&path, "index.dat")?,
            stand: FileAoraIndex::create_new(&path, "stand.dat")?,
            mine: FileAuraMap::create_new(&path, "mine.dat")?,
            _phantom: PhantomData,
        })
    }

    fn load(path: PathBuf) -> Result<Self, io::Error>
    where Self: Sized {
        Ok(Self {
            hoard: FileAoraMap::open(&path, "hoard")?,
            cache: FileAoraMap::open(&path, "cache")?,
            keep: FileAoraMap::open(&path, "keep")?,
            index: FileAoraIndex::open(&path, "index.dat")?,
            stand: FileAoraIndex::open(&path, "stand.dat")?,
            mine: FileAuraMap::open(&path, "mine.dat")?,
            _phantom: PhantomData,
        })
    }

    fn session(&mut self) -> &mut Self { self }
}
