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

//! Based on the reference lsp-server example at <https://github.com/rust-analyzer/lsp-server/blob/master/examples/goto_def.rs>.

use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

use gazebo::prelude::*;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    notification::{
        DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, LogMessage,
        PublishDiagnostics,
    },
    request::GotoDefinition,
    DefinitionOptions, Diagnostic, DiagnosticSeverity, DidChangeTextDocumentParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, GotoDefinitionParams,
    GotoDefinitionResponse, InitializeParams, Location, LogMessageParams, MessageType,
    NumberOrString, OneOf, Position, PublishDiagnosticsParams, Range, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, Url, WorkDoneProgressOptions,
};
use serde::de::DeserializeOwned;
use starlark::syntax::AstModule;

use crate::{
    eval::Context,
    types::{Message as StarlarkMessage, Severity},
};

struct Backend {
    connection: Connection,
    starlark: Context,
    /// The `AstModule` from the last time that a file was opened / changed and parsed successfully.
    /// Entries are evicted when the file is closed.
    last_valid_parse: RwLock<HashMap<Url, Arc<AstModule>>>,
}

fn to_severity(x: Severity) -> DiagnosticSeverity {
    match x {
        Severity::Error => DiagnosticSeverity::Error,
        Severity::Warning => DiagnosticSeverity::Warning,
        Severity::Advice => DiagnosticSeverity::Hint,
        Severity::Disabled => DiagnosticSeverity::Information,
    }
}

fn to_diagnostic(x: StarlarkMessage) -> Diagnostic {
    let range = match x.span {
        Some(s) => Range::new(
            Position::new(s.begin_line as u32, s.begin_column as u32),
            Position::new(s.end_line as u32, s.end_column as u32),
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

/// The logic implementations of stuff
impl Backend {
    fn server_capabilities() -> ServerCapabilities {
        ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Full)),
            definition_provider: Some(OneOf::Right(DefinitionOptions {
                work_done_progress_options: WorkDoneProgressOptions {
                    work_done_progress: None,
                },
            })),
            ..ServerCapabilities::default()
        }
    }

    fn get_ast(&self, uri: &Url) -> Option<Arc<AstModule>> {
        let last_valid_parse = self.last_valid_parse.read().unwrap();
        last_valid_parse.get(uri).duped()
    }

    fn validate(&self, uri: Url, version: Option<i64>, text: String) {
        let eval_result = self.starlark.file_with_contents(&uri.to_string(), text);
        let diags = eval_result.messages.map(to_diagnostic).collect();
        if let Some(ast) = eval_result.ast {
            let ast = Arc::new(ast);
            let mut last_valid_parse = self.last_valid_parse.write().unwrap();
            last_valid_parse.insert(uri.clone(), ast);
        }
        self.publish_diagnostics(uri, diags, version)
    }

    fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.validate(
            params.text_document.uri,
            Some(params.text_document.version as i64),
            params.text_document.text,
        )
    }

    fn did_change(&self, params: DidChangeTextDocumentParams) {
        // We asked for Sync full, so can just grab all the text from params
        let change = params.content_changes.into_iter().next().unwrap();
        self.validate(
            params.text_document.uri,
            Some(params.text_document.version as i64),
            change.text,
        );
    }

    fn did_close(&self, params: DidCloseTextDocumentParams) {
        {
            let mut last_valid_parse = self.last_valid_parse.write().unwrap();
            last_valid_parse.remove(&params.text_document.uri);
        }
        self.publish_diagnostics(params.text_document.uri, Vec::new(), None)
    }

    /// Go to the definition of the symbol at the current cursor if that definition is in
    /// the same file.
    ///
    /// NOTE: This uses the last valid parse of a file as a basis for symbol locations.
    /// If a file has changed and does result in a valid parse, then symbol locations may
    /// be slightly incorrect.
    fn goto_definition(&self, id: RequestId, params: GotoDefinitionParams) {
        let response = match self.get_ast(&params.text_document_position_params.text_document.uri) {
            Some(ast) => {
                match ast.find_definition(
                    params.text_document_position_params.position.line,
                    params.text_document_position_params.position.character,
                ) {
                    Some(span) => GotoDefinitionResponse::Scalar(Location {
                        uri: params
                            .text_document_position_params
                            .text_document
                            .uri
                            .clone(),
                        range: span.into(),
                    }),
                    None => GotoDefinitionResponse::Array(vec![]),
                }
            }
            None => GotoDefinitionResponse::Array(vec![]),
        };
        self.send_response(new_response(id, response));
    }
}

/// The library style pieces
impl Backend {
    fn send_notification(&self, x: Notification) {
        self.connection
            .sender
            .send(Message::Notification(x))
            .unwrap()
    }

    fn send_response(&self, x: Response) {
        self.connection.sender.send(Message::Response(x)).unwrap()
    }

    fn log_message(&self, typ: MessageType, message: &str) {
        self.send_notification(new_notification::<LogMessage>(LogMessageParams {
            typ,
            message: message.to_owned(),
        }))
    }

    fn publish_diagnostics(&self, uri: Url, diags: Vec<Diagnostic>, version: Option<i64>) {
        self.send_notification(new_notification::<PublishDiagnostics>(
            PublishDiagnosticsParams::new(uri, diags, version.map(|i| i as i32)),
        ));
    }

    fn main_loop(&self, _params: InitializeParams) -> anyhow::Result<()> {
        self.log_message(MessageType::Info, "Starlark server initialised");
        for msg in &self.connection.receiver {
            match msg {
                Message::Request(req) => {
                    // TODO(nmj): Also implement DocumentSymbols so that some logic can
                    //            be handled client side.
                    if let Some(params) = as_request::<GotoDefinition>(&req) {
                        self.goto_definition(req.id, params);
                    } else if self.connection.handle_shutdown(&req)? {
                        return Ok(());
                    }
                    // Currently don't handle any other requests
                }
                Message::Notification(x) => {
                    if let Some(params) = as_notification::<DidOpenTextDocument>(&x) {
                        self.did_open(params)
                    } else if let Some(params) = as_notification::<DidChangeTextDocument>(&x) {
                        self.did_change(params)
                    } else if let Some(params) = as_notification::<DidCloseTextDocument>(&x) {
                        self.did_close(params)
                    }
                }
                Message::Response(_) => {
                    // Don't expect any of these
                }
            }
        }
        Ok(())
    }
}

pub(crate) fn server(starlark: Context) -> anyhow::Result<()> {
    // Note that  we must have our logging only write out to stderr.
    eprintln!("Starting Rust Starlark server");

    let (connection, io_threads) = Connection::stdio();
    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let server_capabilities = serde_json::to_value(&Backend::server_capabilities()).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;
    let initialization_params = serde_json::from_value(initialization_params).unwrap();
    Backend {
        connection,
        starlark,
        last_valid_parse: RwLock::default(),
    }
    .main_loop(initialization_params)?;
    io_threads.join()?;

    eprintln!("Stopping Rust Starlark server");
    Ok(())
}

fn as_notification<T>(x: &Notification) -> Option<T::Params>
where
    T: lsp_types::notification::Notification,
    T::Params: DeserializeOwned,
{
    if x.method == T::METHOD {
        let params = serde_json::from_value(x.params.clone()).unwrap_or_else(|err| {
            panic!(
                "Invalid notification\nMethod: {}\n error: {}",
                x.method, err
            )
        });
        Some(params)
    } else {
        None
    }
}

fn as_request<T>(x: &Request) -> Option<T::Params>
where
    T: lsp_types::request::Request,
    T::Params: DeserializeOwned,
{
    if x.method == T::METHOD {
        let params = serde_json::from_value(x.params.clone())
            .unwrap_or_else(|err| panic!("Invalid request\nMethod: {}\n error: {}", x.method, err));
        Some(params)
    } else {
        None
    }
}

fn new_notification<T>(params: T::Params) -> Notification
where
    T: lsp_types::notification::Notification,
{
    Notification {
        method: T::METHOD.to_owned(),
        params: serde_json::to_value(&params).unwrap(),
    }
}

fn new_response<T>(id: RequestId, params: T) -> Response
where
    T: serde::Serialize,
{
    Response {
        id,
        result: Some(serde_json::to_value(params).unwrap()),
        error: None,
    }
}
