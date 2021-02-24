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

use crate::types::Message;
use itertools::Either;
use starlark::{
    analysis,
    environment::{FrozenModule, Globals, Module},
    eval::{eval_module, EvaluationContext, NoLoadFileLoader},
    stdlib::{add_typing, extended_environment},
    syntax::{parse, parse_file, AstModule, Dialect},
};
use std::{
    fs, iter,
    path::{Path, PathBuf},
};

#[derive(Debug)]
pub struct Context {
    pub check: bool,
    pub info: bool,
    pub run: bool,
    pub prelude: Vec<FrozenModule>,
}

impl Context {
    pub fn new(check: bool, info: bool, run: bool, prelude: &[PathBuf]) -> anyhow::Result<Self> {
        let globals = globals();
        let prelude = prelude
            .iter()
            .map(|x| {
                let env = Module::new("prelude");

                let mut context = EvaluationContext::new(&env, &globals, &NoLoadFileLoader);
                let module = parse_file(x, &dialect())?;
                eval_module(module, &mut context)?;
                Ok(env.freeze())
            })
            .collect::<anyhow::Result<_>>()?;

        Ok(Self {
            check,
            info,
            run,
            prelude,
        })
    }

    fn go(&self, file: &str, module: AstModule) -> impl Iterator<Item = Message> {
        let mut warnings = Either::Left(iter::empty());
        let mut errors = Either::Left(iter::empty());
        if self.info {
            self.info(&module);
        }
        if self.check {
            warnings = Either::Right(self.check(&module));
        }
        if self.run {
            errors = Either::Right(self.run(file, module));
        }
        warnings.chain(errors)
    }

    // Convert an anyhow over iterator of Message, into an iterator of Message
    fn err(
        file: &str,
        result: anyhow::Result<impl Iterator<Item = Message>>,
    ) -> impl Iterator<Item = Message> {
        match result {
            Err(e) => Either::Left(iter::once(Message::from_anyhow(file, e))),
            Ok(res) => Either::Right(res),
        }
    }

    pub fn expression(&self, content: String) -> impl Iterator<Item = Message> {
        let file = "expression";
        Self::err(
            file,
            parse(file, content, &dialect()).map(|module| self.go(file, module)),
        )
    }

    pub fn file(&self, file: &Path) -> impl Iterator<Item = Message> {
        let filename = &file.to_string_lossy();
        Self::err(
            filename,
            fs::read_to_string(file)
                .map(|content| self.file_with_contents(filename, content))
                .map_err(|e| e.into()),
        )
    }

    pub fn file_with_contents(
        &self,
        filename: &str,
        content: String,
    ) -> impl Iterator<Item = Message> {
        Self::err(
            filename,
            parse(filename, content, &dialect()).map(|module| self.go(filename, module)),
        )
    }

    fn run(&self, file: &str, module: AstModule) -> impl Iterator<Item = Message> {
        let env = Module::new(file);
        for p in &self.prelude {
            env.import_public_symbols(p)
        }
        let globals = globals();
        let mut context = EvaluationContext::new(&env, &globals, &NoLoadFileLoader);
        Self::err(
            file,
            eval_module(module, &mut context).map(|_| iter::empty()),
        )
    }

    fn info(&self, module: &AstModule) {
        let exports = analysis::exported_symbols(module);
        println!("Exports {} symbol(s)", exports.len());
        for (loc, name) in exports {
            println!("* {} {}", loc, name)
        }
    }

    fn check(&self, module: &AstModule) -> impl Iterator<Item = Message> {
        let mut globals = Vec::new();
        for x in &self.prelude {
            globals.extend(x.names());
        }
        let globals = if self.prelude.is_empty() {
            None
        } else {
            Some(globals.as_slice())
        };

        analysis::lint(module, globals)
            .into_iter()
            .map(Message::from_lint)
    }
}

pub fn globals() -> Globals {
    extended_environment().with(add_typing).build()
}

pub fn dialect() -> Dialect {
    Dialect::Extended
}
