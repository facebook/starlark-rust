//! Collection of implementations for completions, and related types.

use std::collections::HashMap;
use std::path::Path;

use lsp_types::CompletionItem;
use lsp_types::CompletionItemKind;
use lsp_types::CompletionTextEdit;
use lsp_types::Documentation;
use lsp_types::MarkupContent;
use lsp_types::MarkupKind;
use lsp_types::Range;
use lsp_types::TextEdit;

use crate::analysis::definition::Definition;
use crate::analysis::definition::DottedDefinition;
use crate::analysis::definition::IdentifierDefinition;
use crate::analysis::definition::LspModule;
use crate::analysis::exported::SymbolKind as ExportedSymbolKind;
use crate::codemap::LineCol;
use crate::codemap::ResolvedSpan;
use crate::docs::render_doc_item;
use crate::docs::DocItem;
use crate::docs::DocParam;
use crate::environment::GlobalSymbolKind;
use crate::lsp::server::Backend;
use crate::lsp::server::LspContext;
use crate::lsp::server::LspUrl;
use crate::syntax::ast::StmtP;
use crate::syntax::symbols::find_symbols_at_location;
use crate::syntax::symbols::SymbolKind;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum StringCompletionMode {
    IncludeNamedTargets,
    FilesOnly,
}

/// Starting point for resolving filesystem completions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FilesystemCompletionRoot<'a> {
    /// A resolved path, e.g. from an opened document.
    Path(&'a Path),
    /// An unresolved path, e.g. from a string literal in a `load` statement.
    String(&'a str),
}

/// Options for resolving filesystem completions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FilesystemCompletionOptions {
    /// Whether to include directories in the results.
    pub directories: bool,
    /// Whether to include files in the results.
    pub files: bool,
    /// Whether to include files of any type in the results, as opposed to only files that are
    /// loadable.
    pub all_files: bool,
    /// Whether to include target names from BUILD files.
    pub targets: bool,
}

/// A filesystem completion, e.g. for a `load` statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FilesystemCompletion {
    /// A regular file system entry, i.e. a directory or file.
    Entry {
        /// The label to show to the user.
        label: String,
        /// The text to insert when accepting the completion.
        insert_text: String,
        /// From where to start the insertion, compared to the start of the string.
        insert_text_offset: usize,
        /// The kind of completion.
        kind: CompletionItemKind,
    },
    /// A BUILD file containing targets buildable using the detected build system.
    BuildFile {
        /// The URI of the build file.
        targets: Vec<String>,
        /// Whether to prefix the generated label with a colon.
        prefix_with_colon: bool,
        /// From where to start the insertion, compared to the start of the string.
        insert_text_offset: usize,
    },
}

impl<T: LspContext> Backend<T> {
    pub(crate) fn default_completion_options(
        &self,
        document_uri: &LspUrl,
        document: &LspModule,
        line: u32,
        character: u32,
        workspace_root: Option<&Path>,
    ) -> impl Iterator<Item = CompletionItem> + '_ {
        let cursor_position = LineCol {
            line: line as usize,
            column: character as usize,
        };

        // Scan through current document
        let mut symbols: HashMap<_, _> = find_symbols_at_location(
            &document.ast.codemap,
            &document.ast.statement,
            cursor_position,
        )
        .into_iter()
        .map(|(key, value)| {
            (
                key,
                CompletionItem {
                    kind: Some(match value.kind {
                        SymbolKind::Method => CompletionItemKind::METHOD,
                        SymbolKind::Variable => CompletionItemKind::VARIABLE,
                    }),
                    detail: value.detail,
                    documentation: value.doc.map(|doc| {
                        Documentation::MarkupContent(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: render_doc_item(&value.name, &doc),
                        })
                    }),
                    label: value.name,
                    ..Default::default()
                },
            )
        })
        .collect();

        // Discover exported symbols from other documents
        let docs = self.last_valid_parse.read().unwrap();
        if docs.len() > 1 {
            // Find the position of the last load in the current file.
            let mut last_load = None;
            let mut loads = HashMap::new();
            document.ast.statement.visit_stmt(|node| {
                if let StmtP::Load(load) = &node.node {
                    last_load = Some(node.span);
                    loads.insert(load.module.node.clone(), (load.args.clone(), node.span));
                }
            });
            let last_load = last_load.map(|span| document.ast.codemap.resolve_span(span));

            symbols.extend(
                self.get_all_exported_symbols(
                    Some(document_uri),
                    &symbols,
                    workspace_root,
                    document_uri,
                    |module, symbol| {
                        Self::get_load_text_edit(
                            module,
                            symbol,
                            document,
                            last_load,
                            loads.get(module),
                        )
                    },
                )
                .into_iter()
                .map(|item| (item.label.clone(), item)),
            );
        }

        symbols
            .into_values()
            .chain(self.get_global_symbol_completion_items())
            .chain(Self::get_keyword_completion_items())
    }

    pub(crate) fn string_completion_options<'a>(
        &'a self,
        mode: StringCompletionMode,
        document_uri: &LspUrl,
        current_value: &str,
        current_span: ResolvedSpan,
        workspace_root: Option<&Path>,
    ) -> impl Iterator<Item = CompletionItem> + 'a {
        // Figure out if we're just completing repository names for now, e.g.:
        // "" (empty string)
        // "@" (we want a repository)
        // "@part" (partially typed repository)
        // "foo" (might be relative, might be a repository)
        // But not:
        // "//<anything>" (no repository)
        // ":<anything>" (relative path)
        // "@repository//<anything>" (repository part is complete)
        let render_at_prefix =
            self.context.use_at_repository_prefix() || current_value.starts_with('@');
        let want_repository = current_value.is_empty()
            || current_value == "@"
            || (current_value.starts_with('@') && !current_value.contains('/'))
            || (!render_at_prefix && !current_value.contains('/') && !current_value.contains(':'));

        let mut names = if want_repository {
            self.context
                .get_repository_names()
                .into_iter()
                .map(|name| {
                    let name_with_at = if render_at_prefix {
                        format!("@{}", name)
                    } else {
                        name.to_string()
                    };
                    let insert_text = format!("{}//", &name_with_at);

                    FilesystemCompletion::Entry {
                        label: name_with_at,
                        insert_text,
                        insert_text_offset: 0,
                        kind: CompletionItemKind::MODULE,
                    }
                })
                .collect()
        } else {
            vec![]
        };

        // Complete filenames if we're not in the middle of typing a repository name:
        // "@foo" -> don't complete filenames (still typing repository)
        // "@foo/" -> don't complete filenames (need two separating slashes)
        // "@foo//", "@foo//bar -> complete directories (from `//foo`)
        // "@foo//bar/baz" -> complete directories (from `//foo/bar`)
        // "@foo//bar:baz" -> complete filenames (from `//foo/bar`), and target names if `mode` is `IncludeNamedTargets`
        // "foo" -> complete directories and filenames (ambiguous, might be a relative path or a repository)
        let complete_directories = (!current_value.starts_with('@')
            || current_value.contains("//"))
            && !current_value.contains(':');
        let complete_filenames =
            // Still typing repository
            (!current_value.starts_with('@') || current_value.contains("//")) &&
            // Explicitly typing directory
            (!current_value.contains('/') || current_value.contains(':'));
        let complete_targets =
            mode == StringCompletionMode::IncludeNamedTargets && complete_filenames;
        if complete_directories || complete_filenames || complete_targets {
            let complete_from = if complete_directories && complete_filenames {
                // This must mean we don't have a `/` or `:` separator, so we're completing a relative path.
                // Use the document URI's directory as the base.
                document_uri
                    .path()
                    .parent()
                    .map(FilesystemCompletionRoot::Path)
            } else {
                // Complete from the last `:` or `/` in the current value.
                current_value
                    .rfind(if complete_directories { '/' } else { ':' })
                    .map(|pos| &current_value[..pos + 1])
                    .map(FilesystemCompletionRoot::String)
            };

            if let Some(completion_root) = complete_from {
                let other_names = self.context.get_filesystem_entries(
                    completion_root,
                    document_uri,
                    workspace_root,
                    &FilesystemCompletionOptions {
                        directories: complete_directories,
                        files: complete_filenames,
                        // I guess any place we can complete targets we can complete regular files?
                        all_files: complete_targets,
                        targets: complete_targets,
                    },
                );
                match other_names {
                    Ok(other_names) => {
                        for option in other_names {
                            match option {
                                FilesystemCompletion::Entry { .. } => names.push(option),
                                FilesystemCompletion::BuildFile {
                                    targets,
                                    insert_text_offset,
                                    prefix_with_colon,
                                } => names.extend(targets.into_iter().map(|name| {
                                    let insert_text = format!(
                                        "{}{}",
                                        if prefix_with_colon { ":" } else { "" },
                                        &name
                                    );
                                    FilesystemCompletion::Entry {
                                        label: name,
                                        insert_text,
                                        insert_text_offset,
                                        kind: CompletionItemKind::PROPERTY,
                                    }
                                })),
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("Error getting filesystem entries: {:?}", e);
                    }
                }
            }
        }

        names.into_iter().filter_map(move |completion| {
            let FilesystemCompletion::Entry {
                label,
                insert_text,
                insert_text_offset,
                kind,
            } = completion else {
                eprintln!("Unexpected filesystem completion: {:?}", completion);
                return None;
            };
            let mut range: Range = current_span.into();
            range.start.character += insert_text_offset as u32;

            Some(CompletionItem {
                label,
                insert_text: Some(insert_text.clone()),
                text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                    range,
                    new_text: insert_text,
                })),
                kind: Some(kind),
                ..Default::default()
            })
        })
    }

    pub(crate) fn exported_symbol_options(
        &self,
        load_path: &str,
        current_span: ResolvedSpan,
        previously_loaded: &[String],
        document_uri: &LspUrl,
        workspace_root: Option<&Path>,
    ) -> Vec<CompletionItem> {
        self.context
            .resolve_load(load_path, document_uri, workspace_root)
            .and_then(|url| self.get_ast_or_load_from_disk(&url))
            .into_iter()
            .flatten()
            .flat_map(|ast| {
                ast.get_exported_symbols()
                    .into_iter()
                    .filter(|symbol| !previously_loaded.iter().any(|s| s == &symbol.name))
                    .map(|symbol| {
                        let mut item: CompletionItem = symbol.into();
                        item.insert_text = Some(item.label.clone());
                        item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
                            range: current_span.into(),
                            new_text: item.label.clone(),
                        }));
                        item
                    })
            })
            .collect()
    }

    pub(crate) fn parameter_name_options(
        &self,
        function_name_span: &ResolvedSpan,
        document: &LspModule,
        document_uri: &LspUrl,
        workspace_root: Option<&Path>,
    ) -> impl Iterator<Item = CompletionItem> {
        match document.find_definition_at_location(
            function_name_span.begin_line as u32,
            function_name_span.begin_column as u32,
        ) {
            Definition::Identifier(identifier) => self
                .parameter_name_options_for_identifier_definition(
                    &identifier,
                    document,
                    document_uri,
                    workspace_root,
                )
                .unwrap_or_default(),
            Definition::Dotted(DottedDefinition {
                root_definition_location,
                ..
            }) => self
                .parameter_name_options_for_identifier_definition(
                    &root_definition_location,
                    document,
                    document_uri,
                    workspace_root,
                )
                .unwrap_or_default(),
        }
        .into_iter()
        .flatten()
    }

    fn parameter_name_options_for_identifier_definition(
        &self,
        identifier_definition: &IdentifierDefinition,
        document: &LspModule,
        document_uri: &LspUrl,
        workspace_root: Option<&Path>,
    ) -> anyhow::Result<Option<Vec<CompletionItem>>> {
        Ok(match identifier_definition {
            IdentifierDefinition::Location {
                destination, name, ..
            } => {
                // Can we resolve it again at that location?
                // TODO: This seems very inefficient. Once the document starts
                // holding the `Scope` including AST nodes, this indirection
                // should be removed.
                find_symbols_at_location(
                    &document.ast.codemap,
                    &document.ast.statement,
                    LineCol {
                        line: destination.begin_line,
                        column: destination.begin_column,
                    },
                )
                .remove(name)
                .and_then(|symbol| match symbol.kind {
                    SymbolKind::Method => symbol.doc,
                    SymbolKind::Variable => None,
                })
                .and_then(|docs| match docs {
                    DocItem::Function(doc_function) => Some(
                        doc_function
                            .params
                            .into_iter()
                            .filter_map(|param| match param {
                                DocParam::Arg { name, .. } => Some(CompletionItem {
                                    label: name,
                                    kind: Some(CompletionItemKind::PROPERTY),
                                    ..Default::default()
                                }),
                                _ => None,
                            })
                            .collect(),
                    ),
                    _ => None,
                })
            }
            IdentifierDefinition::LoadedLocation { path, name, .. } => {
                let load_uri = self.resolve_load_path(path, document_uri, workspace_root)?;
                self.get_ast_or_load_from_disk(&load_uri)?
                    .and_then(|ast| ast.find_exported_symbol(name))
                    .and_then(|symbol| match symbol.kind {
                        ExportedSymbolKind::Any => None,
                        ExportedSymbolKind::Function { argument_names } => Some(
                            argument_names
                                .into_iter()
                                .map(|name| CompletionItem {
                                    label: name,
                                    kind: Some(CompletionItemKind::PROPERTY),
                                    ..Default::default()
                                })
                                .collect(),
                        ),
                    })
            }
            IdentifierDefinition::Unresolved { name, .. } => {
                // Maybe it's a global symbol.
                match self
                    .context
                    .get_global_symbols()
                    .into_iter()
                    .find(|symbol| symbol.name == name)
                {
                    Some(symbol) if symbol.kind == GlobalSymbolKind::Function => {
                        match symbol.documentation {
                            Some(DocItem::Function(doc_function)) => Some(
                                doc_function
                                    .params
                                    .into_iter()
                                    .filter_map(|param| match param {
                                        DocParam::Arg { name, .. } => Some(CompletionItem {
                                            label: name,
                                            kind: Some(CompletionItemKind::PROPERTY),
                                            ..Default::default()
                                        }),
                                        _ => None,
                                    })
                                    .collect(),
                            ),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            // None of these can be functions, so can't have any parameters.
            IdentifierDefinition::LoadPath { .. }
            | IdentifierDefinition::StringLiteral { .. }
            | IdentifierDefinition::NotFound => None,
        })
    }

    pub(crate) fn type_completion_options() -> impl Iterator<Item = CompletionItem> {
        ["str.type", "int.type", "bool.type", "None", "\"float\""]
            .into_iter()
            .map(|type_| CompletionItem {
                label: type_.to_string(),
                kind: Some(CompletionItemKind::TYPE_PARAMETER),
                ..Default::default()
            })
    }
}
