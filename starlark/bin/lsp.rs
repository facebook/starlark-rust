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

use crate::{
    eval::Context,
    types::{Message, Severity},
};
use tower_lsp::{jsonrpc::Result, lsp_types::*, Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
    client: Client,
    starlark: Context,
}

fn to_severity(x: Severity) -> DiagnosticSeverity {
    match x {
        Severity::Error => DiagnosticSeverity::Error,
        Severity::Warning => DiagnosticSeverity::Warning,
        Severity::Advice => DiagnosticSeverity::Hint,
        Severity::Disabled => DiagnosticSeverity::Information,
    }
}

fn to_diagnostic(x: Message) -> Diagnostic {
    let range = match x.span {
        Some(s) => Range::new(
            Position::new((s.begin.line - 1) as u64, (s.begin.column - 1) as u64),
            Position::new((s.end.line - 1) as u64, (s.end.column - 1) as u64),
        ),
        _ => Range::default(),
    };
    Diagnostic::new(
        range,
        Some(to_severity(x.severity)),
        Some(NumberOrString::String(x.name)),
        None,
        x.description,
        None,
        None,
    )
}

impl Backend {
    async fn validate(&self, uri: Url, version: Option<i64>, text: String) {
        let diags = self
            .starlark
            .file_with_contents(&uri.to_string(), text)
            .map(to_diagnostic)
            .collect();
        self.client.publish_diagnostics(uri, diags, version).await
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        let mut r = InitializeResult::default();
        r.capabilities.text_document_sync =
            Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Full));
        Ok(r)
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::Info, "Starlark server initialised")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.validate(
            params.text_document.uri,
            Some(params.text_document.version),
            params.text_document.text,
        )
        .await
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // We asked for Sync full, so can just grab all the text from params
        let change = params.content_changes.into_iter().next().unwrap();
        self.validate(
            params.text_document.uri,
            params.text_document.version,
            change.text,
        )
        .await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.client
            .publish_diagnostics(params.text_document.uri, vec![], None)
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

pub async fn server(starlark: Context) {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, messages) = LspService::new(|client| Backend { client, starlark });
    Server::new(stdin, stdout)
        .interleave(messages)
        .serve(service)
        .await;
}
