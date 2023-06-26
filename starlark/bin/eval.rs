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

use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::io;
use std::iter;
use std::path::Path;
use std::path::PathBuf;

use itertools::Either;
use lsp_types::Diagnostic;
use lsp_types::Url;
use starlark::build_system::try_resolve_build_system;
use starlark::build_system::BuildSystem;
use starlark::build_system::BuildSystemHint;
use starlark::docs::get_registered_starlark_docs;
use starlark::docs::render_docs_as_code;
use starlark::docs::Doc;
use starlark::docs::DocItem;
use starlark::environment::FrozenModule;
use starlark::environment::GlobalSymbol;
use starlark::environment::Globals;
use starlark::environment::Module;
use starlark::errors::EvalMessage;
use starlark::eval::Evaluator;
use starlark::lsp::server::LspContext;
use starlark::lsp::server::LspEvalResult;
use starlark::lsp::server::LspUrl;
use starlark::lsp::server::StringLiteralResult;
use starlark::syntax::AstModule;
use starlark::syntax::Dialect;

#[derive(Debug)]
pub(crate) enum ContextMode {
    Check,
    Run,
}

#[derive(Debug, thiserror::Error)]
enum ContextError {
    /// The provided Url was not absolute and it needs to be.
    #[error("Path for URL `{}` was not absolute", .0)]
    NotAbsolute(LspUrl),
    /// The scheme provided was not correct or supported.
    #[error("Url `{}` was expected to be of type `{}`", .1, .0)]
    WrongScheme(String, LspUrl),
}

#[derive(Debug)]
pub(crate) struct Context {
    pub(crate) mode: ContextMode,
    pub(crate) print_non_none: bool,
    pub(crate) prelude: Vec<FrozenModule>,
    pub(crate) module: Option<Module>,
    pub(crate) builtin_docs: HashMap<LspUrl, String>,
    pub(crate) builtin_symbols: HashMap<String, LspUrl>,
    pub(crate) globals: Globals,
    pub(crate) build_system: Option<Box<dyn BuildSystem>>,
}

/// The outcome of evaluating (checking, parsing or running) given starlark code.
pub(crate) struct EvalResult<T: Iterator<Item = EvalMessage>> {
    /// The diagnostic and error messages from evaluating a given piece of starlark code.
    pub messages: T,
    /// If the code is only parsed, not run, and there were no errors, this will contain
    /// the parsed module. Otherwise, it will be `None`
    pub ast: Option<AstModule>,
}

/// Errors when [`LspContext::resolve_load()`] cannot resolve a given path.
#[derive(thiserror::Error, Debug)]
enum ResolveLoadError {
    /// Attempted to resolve a relative path, but no current_file_path was provided,
    /// so it is not known what to resolve the path against.
    #[error("Relative path `{}` provided, but current_file_path could not be determined", .0)]
    MissingCurrentFilePath(String),
    /// The scheme provided was not correct or supported.
    #[error("Url `{}` was expected to be of type `{}`", .1, .0)]
    WrongScheme(String, LspUrl),
    /// Received a load for an absolute path from the root of the workspace, but the
    /// path to the workspace root was not provided.
    #[error("Path `//{}` is absolute from the root of the workspace, but no workspace root was provided", .0)]
    MissingWorkspaceRoot(String),
    /// Unable to parse the given path.
    #[error("Unable to parse the load path `{}`", .0)]
    CannotParsePath(String),
    /// Cannot resolve path containing workspace without information from the build system.
    #[error("Cannot resolve path `{}` without build system info", .0)]
    MissingBuildSystem(String),
}

/// Errors when [`LspContext::render_as_load()`] cannot render a given path.
#[derive(thiserror::Error, Debug)]
enum RenderLoadError {
    /// Attempted to get the filename of a path that does not seem to contain a filename.
    #[error("Path `{}` provided, which does not seem to contain a filename", .0.display())]
    MissingTargetFilename(PathBuf),
    /// The scheme provided was not correct or supported.
    #[error("Urls `{}` and `{}` was expected to be of type `{}`", .1, .2, .0)]
    WrongScheme(String, LspUrl, LspUrl),
}

impl Context {
    pub(crate) fn new(
        mode: ContextMode,
        print_non_none: bool,
        prelude: &[PathBuf],
        module: bool,
        build_system_hint: Option<BuildSystemHint>,
    ) -> anyhow::Result<Self> {
        let globals = globals();
        let prelude: Vec<_> = prelude
            .iter()
            .map(|x| {
                let env = Module::new();
                {
                    let mut eval = Evaluator::new(&env);
                    let module = AstModule::parse_file(x, &dialect())?;
                    eval.eval_module(module, &globals)?;
                }
                env.freeze()
            })
            .collect::<anyhow::Result<_>>()?;

        let module = if module {
            Some(Self::new_module(&prelude))
        } else {
            None
        };
        let mut builtins: HashMap<LspUrl, Vec<Doc>> = HashMap::new();
        let mut builtin_symbols: HashMap<String, LspUrl> = HashMap::new();
        for doc in get_registered_starlark_docs() {
            let uri = Self::url_for_doc(&doc);
            builtin_symbols.insert(doc.id.name.clone(), uri.clone());
            builtins.entry(uri).or_default().push(doc);
        }
        let builtin_docs = builtins
            .into_iter()
            .map(|(u, ds)| (u, render_docs_as_code(&ds)))
            .collect();

        let build_system =
            try_resolve_build_system(std::env::current_dir().ok().as_ref(), build_system_hint);

        Ok(Self {
            mode,
            print_non_none,
            prelude,
            module,
            builtin_docs,
            builtin_symbols,
            globals,
            build_system,
        })
    }

    fn url_for_doc(doc: &Doc) -> LspUrl {
        let url = match &doc.item {
            DocItem::Module(_) => Url::parse("starlark:/native/builtins.bzl").unwrap(),
            DocItem::Object(_) => {
                Url::parse(&format!("starlark:/native/builtins/{}.bzl", doc.id.name)).unwrap()
            }
            DocItem::Function(_) | DocItem::Property(_) => {
                Url::parse("starlark:/native/builtins.bzl").unwrap()
            }
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
        let globals = if self.prelude.is_empty() {
            None
        } else {
            let mut globals = HashSet::new();
            for modu in &self.prelude {
                for name in modu.names() {
                    globals.insert(name.as_str().to_owned());
                }
            }

            for global_symbol in self.builtin_symbols.keys() {
                globals.insert(global_symbol.to_owned());
            }

            Some(globals)
        };

        module
            .lint(globals.as_ref())
            .into_iter()
            .map(EvalMessage::from)
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

    fn resolve_load(
        &self,
        path: &str,
        current_file: &LspUrl,
        workspace_root: Option<&Path>,
    ) -> anyhow::Result<LspUrl> {
        let original_path = path;
        if let Some((repository, path)) = path.split_once("//") {
            // The repository may be prefixed with an '@', but it's optional in Buck2.
            let repository = if let Some(without_at) = repository.strip_prefix('@') {
                without_at
            } else {
                repository
            };

            // Check if the repository refers to the workspace root, or if not, if it is a known
            // repository, and what its path is.
            let repository_root = if repository.is_empty() {
                workspace_root.map(Cow::Borrowed)
            } else if let Some(build_system) = &self.build_system {
                if matches!(build_system.root_repository_name(), Some(name) if name == repository) {
                    workspace_root.map(Cow::Borrowed)
                } else {
                    build_system.repository_path(repository)
                }
            } else {
                return Err(ResolveLoadError::MissingBuildSystem(path.to_owned()).into());
            };

            // Resolve from the root of the repository.
            match (path.split_once(':'), repository_root) {
                (Some((subfolder, filename)), Some(repository_root)) => {
                    let mut result = repository_root.into_owned();
                    result.push(subfolder);
                    result.push(filename);
                    Ok(Url::from_file_path(result).unwrap().try_into()?)
                }
                (Some(_), None) => {
                    Err(ResolveLoadError::MissingWorkspaceRoot(original_path.to_owned()).into())
                }
                (None, _) => {
                    Err(ResolveLoadError::CannotParsePath(original_path.to_string()).into())
                }
            }
        } else if let Some((folder, filename)) = path.split_once(':') {
            // Resolve relative paths from the current file.
            match current_file {
                LspUrl::File(current_file_path) => {
                    let current_file_dir = current_file_path.parent();
                    let absolute_path = match current_file_dir {
                        Some(current_file_dir) => {
                            let mut result = current_file_dir.to_owned();
                            result.push(folder);
                            result.push(filename);
                            Ok(result)
                        }
                        None => Err(ResolveLoadError::MissingCurrentFilePath(path.to_owned())),
                    }?;
                    Ok(Url::from_file_path(absolute_path).unwrap().try_into()?)
                }
                _ => Err(
                    ResolveLoadError::WrongScheme("file://".to_owned(), current_file.clone())
                        .into(),
                ),
            }
        } else {
            Err(ResolveLoadError::CannotParsePath(path.to_owned()).into())
        }
    }

    fn render_as_load(
        &self,
        target: &LspUrl,
        current_file: &LspUrl,
        workspace_root: Option<&Path>,
    ) -> anyhow::Result<String> {
        match (target, current_file) {
            (LspUrl::File(target_path), LspUrl::File(current_file_path)) => {
                let target_package = target_path.parent();
                let current_file_package = current_file_path.parent();
                let target_filename = target_path.file_name();

                // If both are in the same package, return a relative path.
                if matches!((target_package, current_file_package), (Some(a), Some(b)) if a == b) {
                    return match target_filename {
                        Some(filename) => Ok(format!(":{}", filename.to_string_lossy())),
                        None => {
                            Err(RenderLoadError::MissingTargetFilename(target_path.clone()).into())
                        }
                    };
                }

                let target_path = workspace_root
                    .and_then(|root| target_path.strip_prefix(root).ok())
                    .unwrap_or(target_path);

                Ok(format!(
                    "//{}:{}",
                    target_path
                        .parent()
                        .map(|path| path.to_string_lossy())
                        .unwrap_or_default(),
                    target_filename
                        .unwrap_or(target_path.as_os_str())
                        .to_string_lossy()
                ))
            }
            _ => Err(RenderLoadError::WrongScheme(
                "file://".to_owned(),
                target.clone(),
                current_file.clone(),
            )
            .into()),
        }
    }

    fn resolve_string_literal(
        &self,
        literal: &str,
        current_file: &LspUrl,
        workspace_root: Option<&Path>,
    ) -> anyhow::Result<Option<StringLiteralResult>> {
        self.resolve_load(literal, current_file, workspace_root)
            .map(|url| {
                Some(StringLiteralResult {
                    url,
                    location_finder: None,
                })
            })
    }

    fn get_load_contents(&self, uri: &LspUrl) -> anyhow::Result<Option<String>> {
        match uri {
            LspUrl::File(path) => match path.is_absolute() {
                true => match fs::read_to_string(path) {
                    Ok(contents) => Ok(Some(contents)),
                    Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
                    Err(e) => Err(e.into()),
                },
                false => Err(ContextError::NotAbsolute(uri.clone()).into()),
            },
            LspUrl::Starlark(_) => Ok(self.builtin_docs.get(uri).cloned()),
            _ => Err(ContextError::WrongScheme("file://".to_owned(), uri.clone()).into()),
        }
    }

    fn get_url_for_global_symbol(
        &self,
        _current_file: &LspUrl,
        symbol: &str,
    ) -> anyhow::Result<Option<LspUrl>> {
        Ok(self.builtin_symbols.get(symbol).cloned())
    }

    fn get_global_symbols(&self) -> Vec<GlobalSymbol> {
        self.globals.symbols().collect()
    }
}

pub(crate) fn globals() -> Globals {
    Globals::extended()
}

pub(crate) fn dialect() -> Dialect {
    Dialect::Extended
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_context() -> Context {
        Context::new(ContextMode::Run, false, &[], false).unwrap()
    }

    #[test]
    fn resolve_load() {
        let context = make_context();

        // Successful cases
        let current_file = LspUrl::File(PathBuf::from("/absolute/path/from.star"));
        assert_eq!(
            context
                .resolve_load(":relative.star", &current_file, None,)
                .unwrap(),
            LspUrl::File(PathBuf::from("/absolute/path/relative.star"))
        );
        assert_eq!(
            context
                .resolve_load("subpath:relative.star", &current_file, None)
                .unwrap(),
            LspUrl::File(PathBuf::from("/absolute/path/subpath/relative.star"))
        );
        assert_eq!(
            context
                .resolve_load("//:root.star", &current_file, Some(Path::new("/foo/bar")),)
                .unwrap(),
            LspUrl::File(PathBuf::from("/foo/bar/root.star"))
        );
        assert_eq!(
            context
                .resolve_load(
                    "//baz:root.star",
                    &current_file,
                    Some(Path::new("/foo/bar")),
                )
                .unwrap(),
            LspUrl::File(PathBuf::from("/foo/bar/baz/root.star"))
        );

        // Error cases
        let starlark_url = LspUrl::Starlark(PathBuf::new());
        assert!(matches!(
            context
                .resolve_load(":relative.star", &starlark_url, None)
                .expect_err("should return an error")
                .downcast::<ResolveLoadError>()
                .expect("should return correct error type"),
            ResolveLoadError::WrongScheme(scheme, url) if scheme == "file://" && url == starlark_url
        ));
        assert!(matches!(
            context
                .resolve_load("//something-absolute", &starlark_url, Some(Path::new("/foo/bar")))
                .expect_err("should return an error")
                .downcast::<ResolveLoadError>()
                .expect("should return correct error type"),
            ResolveLoadError::CannotParsePath(url) if url == "//something-absolute"
        ));
        assert!(matches!(
            context
                .resolve_load("//something:absolute.star", &starlark_url, None)
                .expect_err("should return an error")
                .downcast::<ResolveLoadError>()
                .expect("should return correct error type"),
            ResolveLoadError::MissingWorkspaceRoot(_)
        ));
    }

    #[test]
    fn render_as_load() {
        let context = make_context();

        assert_eq!(
            context
                .render_as_load(
                    &LspUrl::File(PathBuf::from("/foo/bar/baz/target.star")),
                    &LspUrl::File(PathBuf::from("/foo/bar/baz/current.star")),
                    None
                )
                .expect("should succeed"),
            ":target.star"
        );
        assert_eq!(
            context
                .render_as_load(
                    &LspUrl::File(PathBuf::from("/foo/bar/baz/target.star")),
                    &LspUrl::File(PathBuf::from("/foo/bar/current.star")),
                    Some(Path::new("/foo/bar"))
                )
                .expect("should succeed"),
            "//baz:target.star"
        );
        assert_eq!(
            context
                .render_as_load(
                    &LspUrl::File(PathBuf::from("/foo/bar/target.star")),
                    &LspUrl::File(PathBuf::from("/foo/bar/baz/current.star")),
                    Some(Path::new("/foo/bar"))
                )
                .expect("should succeed"),
            "//:target.star"
        );
    }
}
