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

use std::collections::HashMap;
use std::fs;
use std::io;
use std::iter;
use std::path::Path;
use std::path::PathBuf;

use bazel::bazel_info::BazelInfo;
use bazel::label::Label;
use gazebo::prelude::*;
use itertools::Either;
use lsp_types::Diagnostic;
use lsp_types::Range;
use lsp_types::Url;
use starlark::environment::FrozenModule;
use starlark::environment::Globals;
use starlark::environment::Module;
use starlark::errors::EvalMessage;
use starlark::eval::Evaluator;
use starlark::lsp::server::LoadContentsError;
use starlark::lsp::server::LspContext;
use starlark::lsp::server::LspEvalResult;
use starlark::lsp::server::LspUrl;
use starlark::lsp::server::ResolveLoadError;
use starlark::lsp::server::StringLiteralResult;
use starlark::syntax::AstModule;
use starlark::syntax::Dialect;
use starlark::values::docs::get_registered_docs;
use starlark::values::docs::render_docs_as_code;
use starlark::values::docs::Doc;
use starlark::values::docs::DocItem;

#[derive(Debug)]
pub(crate) enum ContextMode {
    Check,
    Run,
}

#[derive(Debug)]
pub(crate) struct Context {
    pub(crate) mode: ContextMode,
    pub(crate) print_non_none: bool,
    pub(crate) prelude: Vec<FrozenModule>,
    pub(crate) module: Option<Module>,
    pub(crate) builtin_docs: HashMap<LspUrl, String>,
    pub(crate) builtin_symbols: HashMap<String, LspUrl>,
    pub(crate) bazel_info: Option<BazelInfo>,
}

/// The outcome of evaluating (checking, parsing or running) given starlark code.
pub(crate) struct EvalResult<T: Iterator<Item = EvalMessage>> {
    /// The diagnostic and error messages from evaluating a given piece of starlark code.
    pub messages: T,
    /// If the code is only parsed, not run, and there were no errors, this will contain
    /// the parsed module. Otherwise, it will be `None`
    pub ast: Option<AstModule>,
}

impl Context {
    pub(crate) fn new(
        mode: ContextMode,
        print_non_none: bool,
        prelude: &[PathBuf],
        module: bool,
    ) -> anyhow::Result<Self> {
        let globals = globals();
        let prelude = prelude.try_map(|x| {
            let env = Module::new();

            let mut eval = Evaluator::new(&env);
            let module = AstModule::parse_file(x, &dialect())?;
            eval.eval_module(module, &globals)?;
            env.freeze()
        })?;

        let module = if module {
            Some(Self::new_module(&prelude))
        } else {
            None
        };
        let mut builtins: HashMap<LspUrl, Vec<Doc>> = HashMap::new();
        let mut builtin_symbols: HashMap<String, LspUrl> = HashMap::new();
        for doc in get_registered_docs() {
            let uri = Self::url_for_doc(&doc);
            builtin_symbols.insert(doc.id.name.clone(), uri.clone());
            builtins.entry(uri).or_default().push(doc);
        }
        let builtin_docs = builtins
            .into_iter()
            .map(|(u, ds)| (u, render_docs_as_code(&ds).join("\n\n")))
            .collect();

        Ok(Self {
            mode,
            print_non_none,
            prelude,
            module,
            builtin_docs,
            builtin_symbols,
            bazel_info: None,
        })
    }

    fn url_for_doc(doc: &Doc) -> LspUrl {
        let url = match &doc.item {
            DocItem::Module(_) => Url::parse("starlark:/native/builtins.bzl").unwrap(),
            DocItem::Object(_) => {
                Url::parse(&format!("starlark:/native/builtins/{}.bzl", doc.id.name)).unwrap()
            }
            DocItem::Function(_) => Url::parse("starlark:/native/builtins.bzl").unwrap(),
        };
        LspUrl::try_from(url).unwrap()
    }

    fn new_module(prelude: &[FrozenModule]) -> Module {
        let module = Module::new();
        for p in prelude {
            module.import_public_symbols(p);
        }
        module
    }

    fn go(&self, file: &str, ast: AstModule) -> EvalResult<impl Iterator<Item = EvalMessage>> {
        let mut warnings = Either::Left(iter::empty());
        let mut errors = Either::Left(iter::empty());
        let final_ast = match self.mode {
            ContextMode::Check => {
                warnings = Either::Right(self.check(&ast));
                Some(ast)
            }
            ContextMode::Run => {
                errors = Either::Right(self.run(file, ast).messages);
                None
            }
        };
        EvalResult {
            messages: warnings.chain(errors),
            ast: final_ast,
        }
    }

    // Convert an anyhow over iterator of EvalMessage, into an iterator of EvalMessage
    fn err(
        file: &str,
        result: anyhow::Result<EvalResult<impl Iterator<Item = EvalMessage>>>,
    ) -> EvalResult<impl Iterator<Item = EvalMessage>> {
        match result {
            Err(e) => EvalResult {
                messages: Either::Left(iter::once(EvalMessage::from_anyhow(Path::new(file), &e))),
                ast: None,
            },
            Ok(res) => EvalResult {
                messages: Either::Right(res.messages),
                ast: res.ast,
            },
        }
    }

    pub(crate) fn expression(
        &self,
        content: String,
    ) -> EvalResult<impl Iterator<Item = EvalMessage>> {
        let file = "expression";
        Self::err(
            file,
            AstModule::parse(file, content, &dialect()).map(|module| self.go(file, module)),
        )
    }

    pub(crate) fn file(&self, file: &Path) -> EvalResult<impl Iterator<Item = EvalMessage>> {
        let filename = &file.to_string_lossy();
        Self::err(
            filename,
            fs::read_to_string(file)
                .map(|content| self.file_with_contents(filename, content))
                .map_err(|e| e.into()),
        )
    }

    pub(crate) fn file_with_contents(
        &self,
        filename: &str,
        content: String,
    ) -> EvalResult<impl Iterator<Item = EvalMessage>> {
        Self::err(
            filename,
            AstModule::parse(filename, content, &dialect()).map(|module| self.go(filename, module)),
        )
    }

    fn run(&self, file: &str, ast: AstModule) -> EvalResult<impl Iterator<Item = EvalMessage>> {
        let new_module;
        let module = match self.module.as_ref() {
            Some(module) => module,
            None => {
                new_module = Self::new_module(&self.prelude);
                &new_module
            }
        };
        let mut eval = Evaluator::new(module);
        eval.enable_terminal_breakpoint_console();
        let globals = globals();
        Self::err(
            file,
            eval.eval_module(ast, &globals).map(|v| {
                if self.print_non_none && !v.is_none() {
                    println!("{}", v);
                }
                EvalResult {
                    messages: iter::empty(),
                    ast: None,
                }
            }),
        )
    }

    fn check(&self, module: &AstModule) -> impl Iterator<Item = EvalMessage> {
        let mut globals = Vec::new();
        for x in &self.prelude {
            globals.extend(x.names().map(|s| s.as_str()));
        }
        let globals = if self.prelude.is_empty() {
            None
        } else {
            Some(globals.as_slice())
        };

        module.lint(globals).into_iter().map(EvalMessage::from)
    }
}

fn find_location_in_build_file(
    info: &Option<BazelInfo>,
    literal: String,
    current_file_pathbuf: PathBuf,
    ast: &AstModule,
) -> anyhow::Result<Option<Range>> {
    let resolved_file = label_into_file(info, literal.as_str(), &current_file_pathbuf, false)?;
    let basename = resolved_file.file_name().and_then(|f| f.to_str()).ok_or(
        ResolveLoadError::ResolvedDoesNotExist(resolved_file.clone()),
    )?;
    let resolved_span = ast
        .find_function_call_with_name(basename)
        .and_then(|r| Some(Range::from(r)));
    Ok(resolved_span)
}

fn label_into_file(
    bazel_info: &Option<BazelInfo>,
    path: &str,
    current_file_path: &PathBuf,
    replace_build_file: bool,
) -> Result<PathBuf, ResolveLoadError> {
    let current_file_dir = current_file_path
        .parent()
        .and_then(|x| Some(PathBuf::from(x)));
    let path_buf = PathBuf::from(path);
    let label = Label::new(path);

    // TODO: not really malformed should we propogate error from label.resolve or just create a new error: CouldntFind Bazel Label
    match (bazel_info, label) {
        (Some(info), Some(label)) => label
            .resolve(info, current_file_dir)
            .and_then(|x| {
                if replace_build_file {
                    Label::replace_fake_file_with_build_target(x)
                } else {
                    Some(x)
                }
            })
            .and_then(|x| Some(x.canonicalize().unwrap_or(x)))
            .ok_or(ResolveLoadError::PathMalformed(path_buf.clone())),

        _ => match (current_file_dir, path_buf.is_absolute()) {
            (_, true) => Ok(path_buf),
            (Some(current_file_dir), false) => Ok(current_file_dir.join(&path_buf)),
            (None, false) => Err(ResolveLoadError::MissingCurrentFilePath(path_buf)),
        },
    }
}

impl LspContext for Context {
    fn parse_file_with_contents(&self, uri: &LspUrl, content: String) -> LspEvalResult {
        match uri {
            LspUrl::File(uri) => {
                let EvalResult { messages, ast } =
                    self.file_with_contents(&uri.to_string_lossy(), content);
                LspEvalResult {
                    diagnostics: messages.map(Diagnostic::from).collect(),
                    ast,
                }
            }
            _ => LspEvalResult::default(),
        }
    }

    fn resolve_load(&self, path: &str, current_file: &LspUrl) -> anyhow::Result<LspUrl> {
        match current_file {
            LspUrl::File(current_file_path) => {
                let resolved_file =
                    label_into_file(&self.bazel_info, path, current_file_path, true)?;
                Ok(Url::from_file_path(resolved_file).unwrap().try_into()?)
            }
            _ => Err(
                ResolveLoadError::WrongScheme("file://".to_owned(), current_file.clone()).into(),
            ),
        }
    }

    fn resolve_string_literal(
        &self,
        literal: &str,
        current_file: &LspUrl,
    ) -> anyhow::Result<Option<StringLiteralResult>> {
        let current_file_pathbuf = current_file.path().to_path_buf();
        self.resolve_load(literal, current_file).map(|url| {
            let p = url.path();
            // TODO: we can always give literal location finder
            // TODO: but if its a file it will always try to resolve the location but won't be able to and an error will be printed
            if self.bazel_info.is_some() && p.ends_with("BUILD") || p.ends_with("BUILD.bazel") {
                let info = self.bazel_info.clone();
                let literal_copy = literal.to_owned();
                Some(StringLiteralResult {
                    url,
                    location_finder: Some(box move |ast: &AstModule, _url| {
                        find_location_in_build_file(&info, literal_copy, current_file_pathbuf, ast)
                    }),
                })
            } else {
                Some(StringLiteralResult {
                    url,
                    location_finder: None,
                })
            }
        })
    }

    fn get_load_contents(&self, uri: &LspUrl) -> anyhow::Result<Option<String>> {
        match uri {
            LspUrl::File(path) => match path.is_absolute() {
                true => match fs::read_to_string(&path) {
                    Ok(contents) => Ok(Some(contents)),
                    Err(e)
                        if e.kind() == io::ErrorKind::NotFound
                            || e.kind() == io::ErrorKind::NotADirectory =>
                    {
                        Ok(None)
                    }
                    Err(e) => Err(e.into()),
                },
                false => Err(LoadContentsError::NotAbsolute(uri.clone()).into()),
            },
            LspUrl::Starlark(_) => Ok(self.builtin_docs.get(uri).cloned()),
            _ => Err(LoadContentsError::WrongScheme("file://".to_owned(), uri.clone()).into()),
        }
    }

    fn get_url_for_global_symbol(
        &self,
        _current_file: &LspUrl,
        symbol: &str,
    ) -> anyhow::Result<Option<LspUrl>> {
        Ok(self.builtin_symbols.get(symbol).cloned())
    }
}

pub(crate) fn globals() -> Globals {
    Globals::extended()
}

pub(crate) fn dialect() -> Dialect {
    Dialect::Extended
}
