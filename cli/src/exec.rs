// RGB command-line toolbox utility
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

use std::convert::Infallible;
use std::io::stdout;

use bp::seals::{TxoSeal, WTxoSeal};
use rgb::popls::bp::PrefabBundle;
use rgb::Issuer;

use crate::cmd::{Args, Cmd};
use crate::dump::{dump_consignment, dump_stockpile};

impl Args {
    pub fn exec(&self) -> anyhow::Result<()> {
        match &self.command {
            Cmd::Info { file } => match file.extension() {
                Some(ext) if ext == "issuer" => {
                    let issuer = Issuer::load(file, |_, _, _| Result::<_, Infallible>::Ok(()))?;
                    eprintln!("File type: Issuer (contract schema)");
                    eprintln!("Issuer Id: {}", issuer.issuer_id());
                    eprintln!(
                        "Signature: {}",
                        if issuer.is_signed() { "present" } else { "absent" }
                    );
                }
                Some(_) => {
                    return Err(anyhow!(
                        "Unknown file type for '{}': the extension is not recognized",
                        file.display()
                    ))
                }
                None => {
                    return Err(anyhow!(
                        "The file '{}' has no extension; unable to detect the file type",
                        file.display()
                    ))
                }
            },

            Cmd::Inspect { file } => match file.extension() {
                Some(ext) if ext == "pfab" => {
                    let pfab = PrefabBundle::load(file)?;
                    serde_yaml::to_writer(stdout(), &pfab)?;
                }
                Some(ext) if ext == "issuer" => {
                    let issuer = Issuer::load(file, |_, _, _| Result::<_, Infallible>::Ok(()))?;
                    serde_yaml::to_writer(stdout(), &issuer.codex())?;
                    serde_yaml::to_writer(stdout(), &issuer.semantics())?;
                    eprintln!("sig: {}", if issuer.is_signed() { "present" } else { "absent" });
                }
                Some(_) => {
                    return Err(anyhow!(
                        "Unknown file type for '{}': the extension is not recognized",
                        file.display()
                    ))
                }
                None => {
                    return Err(anyhow!(
                        "The file '{}' has no extension; unable to detect the file type",
                        file.display()
                    ))
                }
            },
            Cmd::Dump { force, src, dst } => match src.extension() {
                Some(ext) if ext == "rgb" => {
                    let dst = dst
                        .as_ref()
                        .map(|p| p.to_owned())
                        .or_else(|| src.parent().map(|path| path.join("dump")))
                        .ok_or(anyhow!(
                            "Can't detect a destination path for '{}'",
                            src.display()
                        ))?;
                    dump_consignment::<WTxoSeal>(src, dst, *force).inspect_err(|_| println!())?;
                }
                Some(ext) if ext == "contract" => {
                    let dst = dst
                        .as_ref()
                        .map(|p| p.to_owned())
                        .unwrap_or_else(|| src.join("dump"));
                    dump_stockpile::<TxoSeal>(src, dst, *force).inspect_err(|_| println!())?;
                }
                Some(_) => {
                    return Err(anyhow!(
                        "Can't detect the type for '{}': the extension is not recognized",
                        src.display()
                    ))
                }
                None => {
                    return Err(anyhow!(
                        "The path '{}' can't be recognized as known data",
                        src.display()
                    ))
                }
            },
        }
        Ok(())
    }
}
