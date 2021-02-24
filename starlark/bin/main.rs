/*
 * Copyright 2019 The Starlark in Rust Authors.
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Features we use
#![feature(box_syntax)]
//
// Plugins
#![cfg_attr(feature = "custom_linter", feature(plugin))]
#![cfg_attr(feature = "custom_linter", allow(deprecated))] // :(
#![cfg_attr(feature = "custom_linter", plugin(linter))]

use crate::types::{LintMessage, Message, Severity};
use anyhow::anyhow;
use eval::Context;
use gazebo::prelude::*;
use itertools::Either;
use rustyline::{error::ReadlineError, Editor};
use std::{ffi::OsStr, fmt, fmt::Display, fs, path::PathBuf, sync::Arc};
use structopt::{clap::AppSettings, StructOpt};
use walkdir::WalkDir;

mod eval;
mod lsp;
mod types;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "starlark",
    about = "Evaluate Starlark code",
    global_settings(&[AppSettings::ColoredHelp]),
)]
pub struct Args {
    #[structopt(
        long = "interactive",
        long = "repl",
        short = "i",
        help = "Start an interactive REPL."
    )]
    interactive: bool,

    #[structopt(long = "lsp", help = "Start an LSP server.")]
    lsp: bool,

    #[structopt(long = "check", help = "Run checks and lints.")]
    check: bool,

    #[structopt(long = "info", help = "Show information about the code.")]
    info: bool,

    #[structopt(long = "json", help = "Show output as JSON lines.")]
    json: bool,

    #[structopt(
        long = "extension",
        help = "File extension when searching directories."
    )]
    extension: Option<String>,

    #[structopt(long = "prelude", help = "Files to load in advance.")]
    prelude: Vec<PathBuf>,

    #[structopt(
        long = "expression",
        short = "e",
        name = "EXPRESSION",
        help = "Expressions to evaluate."
    )]
    evaluate: Vec<String>,

    #[structopt(name = "FILE", help = "Files to evaluate.")]
    // String instead of PathBuf so we can expand @file things
    files: Vec<String>,
}

// We'd really like clap to deal with args-files, but it doesn't yet
// Waiting on: https://github.com/clap-rs/clap/issues/1693.
// This is a minimal version to make basic @file options work.
fn expand_args(args: Vec<String>) -> anyhow::Result<Vec<PathBuf>> {
    let mut res = Vec::with_capacity(args.len());
    for x in args {
        match x.strip_prefix('@') {
            None => res.push(PathBuf::from(x)),
            Some(x) => {
                let src = fs::read_to_string(x)?;
                for x in src.lines() {
                    res.push(PathBuf::from(x));
                }
            }
        }
    }
    Ok(res)
}

// Treat directories as things to recursively walk for .<extension> files,
// and everything else as normal files.
fn expand_dirs(extension: &str, xs: Vec<PathBuf>) -> impl Iterator<Item = PathBuf> {
    let extension = Arc::new(extension.to_owned());
    xs.into_iter().flat_map(move |x| {
        // Have to keep cloning extension so we keep ownership
        let extension = extension.dupe();
        if x.is_dir() {
            Either::Left(
                WalkDir::new(x)
                    .into_iter()
                    .filter_map(|e| e.ok())
                    .filter(move |e| e.path().extension() == Some(OsStr::new(extension.as_str())))
                    .map(|e| e.into_path()),
            )
        } else {
            Either::Right(box vec![x].into_iter())
        }
    })
}

#[derive(Default)]
struct Stats {
    file: usize,
    error: usize,
    warning: usize,
    advice: usize,
    disabled: usize,
}

impl Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&format!(
            "{} files, {} errors, {} warnings, {} advices, {} disabled",
            self.file, self.error, self.warning, self.advice, self.disabled
        ))
    }
}

impl Stats {
    fn increment_file(&mut self) {
        self.file += 1;
    }

    fn increment(&mut self, x: Severity) {
        match x {
            Severity::Error => self.error += 1,
            Severity::Warning => self.warning += 1,
            Severity::Advice => self.advice += 1,
            Severity::Disabled => self.disabled += 1,
        }
    }
}

fn drain(xs: impl Iterator<Item = Message>, json: bool, stats: &mut Stats) {
    for x in xs {
        stats.increment(x.severity);
        if json {
            println!("{}", serde_json::to_string(&LintMessage::new(x)).unwrap());
        } else {
            println!("{}", x);
        }
    }
}

fn interactive(ctx: &Context) -> anyhow::Result<()> {
    let mut rl = Editor::<()>::new();
    loop {
        let readline = rl.readline("$> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let mut stats = Stats::default();
                drain(ctx.expression(line), false, &mut stats);
            }
            // User pressed EOF - disconnected terminal, or similar
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => return Ok(()),
            Err(err) => return Err(err.into()),
        }
    }
}

fn main() -> anyhow::Result<()> {
    gazebo::terminate_on_panic();

    let args = Args::from_args();
    let ext = args
        .extension
        .as_ref()
        .map_or("bzl", |x| x.as_str())
        .trim_start_match('.');
    let mut ctx = Context::new(
        args.check,
        args.info,
        !args.check && !args.info,
        &expand_dirs(ext, args.prelude).collect::<Vec<_>>(),
    )?;

    let mut stats = Stats::default();
    for e in args.evaluate {
        stats.increment_file();
        drain(ctx.expression(e), args.json, &mut stats);
    }

    for file in expand_dirs(ext, expand_args(args.files)?) {
        stats.increment_file();
        drain(ctx.file(&file), args.json, &mut stats);
    }

    if args.interactive {
        interactive(&ctx)?;
    }

    if args.lsp {
        ctx.check = true;
        ctx.info = false;
        ctx.run = false;
        tokio::runtime::Runtime::new()?.block_on(async {
            lsp::server(ctx).await;
        })
    }

    if !args.json {
        println!("{}", stats);
        if stats.error > 0 {
            return Err(anyhow!("Failed with {} errors", stats.error));
        }
    }
    Ok(())
}
