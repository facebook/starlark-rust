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
    DefinitionOptions, Diagnostic, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, GotoDefinitionParams, GotoDefinitionResponse, InitializeParams,
    Location, LogMessageParams, MessageType, OneOf, PublishDiagnosticsParams, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, Url, WorkDoneProgressOptions,
};
use serde::de::DeserializeOwned;
use starlark::syntax::AstModule;

/// The result of evaluating a starlark program for use in the LSP.
pub(crate) struct LspEvalResult {
    /// The list of diagnostic issues that were encountered while evaluating a starlark program.
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// If the program could be parsed, the parsed module.
    pub(crate) ast: Option<AstModule>,
}

/// Various pieces of context to allow the LSP to interact with starlark parsers, etc.
pub(crate) trait LspContext {
    /// Parse a file with the given contents. The filename is used in the diagnostics.
    fn parse_file_with_contents(&self, filename: &str, content: String) -> LspEvalResult;
}

struct Backend<T: LspContext> {
    connection: Connection,
    context: T,
    /// The `AstModule` from the last time that a file was opened / changed and parsed successfully.
    /// Entries are evicted when the file is closed.
    last_valid_parse: RwLock<HashMap<Url, Arc<AstModule>>>,
}

/// The logic implementations of stuff
impl<T: LspContext> Backend<T> {
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
        let eval_result = self
            .context
            .parse_file_with_contents(&uri.to_string(), text);
        if let Some(ast) = eval_result.ast {
            let ast = Arc::new(ast);
            let mut last_valid_parse = self.last_valid_parse.write().unwrap();
            last_valid_parse.insert(uri.clone(), ast);
        }
        self.publish_diagnostics(uri, eval_result.diagnostics, version)
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
impl<T: LspContext> Backend<T> {
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

pub(crate) fn server<T: LspContext>(context: T) -> anyhow::Result<()> {
    // Note that  we must have our logging only write out to stderr.
    eprintln!("Starting Rust Starlark server");

    let (connection, io_threads) = Connection::stdio();
    server_with_connection(connection, context)?;
    // Make sure that the io threads stop properly too.
    io_threads.join()?;

    eprintln!("Stopping Rust Starlark server");
    Ok(())
}

fn server_with_connection<T: LspContext>(connection: Connection, context: T) -> anyhow::Result<()> {
    // Run the server and wait for the main thread to end (typically by trigger LSP Exit event).
    let server_capabilities = serde_json::to_value(&Backend::<T>::server_capabilities()).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;
    let initialization_params = serde_json::from_value(initialization_params).unwrap();
    Backend {
        connection,
        context,
        last_valid_parse: RwLock::default(),
    }
    .main_loop(initialization_params)?;

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

#[cfg(test)]
mod helpers {
    use std::{
        collections::{hash_map::Entry, HashMap, VecDeque},
        time::Duration,
    };

    use lsp_server::Connection;
    use lsp_types::{
        notification::{Exit, Initialized, Notification},
        request::{Initialize, Request, Shutdown},
        ClientCapabilities, GotoCapability, InitializeResult, InitializedParams,
        TextDocumentClientCapabilities, TextDocumentContentChangeEvent, TextDocumentItem,
        VersionedTextDocumentIdentifier,
    };
    use starlark::{errors::EvalMessage, syntax::Dialect};

    use super::*;

    struct TestServerContext {}

    impl LspContext for TestServerContext {
        fn parse_file_with_contents(&self, filename: &str, content: String) -> LspEvalResult {
            match AstModule::parse(filename, content, &Dialect::Extended) {
                Ok(ast) => {
                    let diagnostics = ast.lint(None).into_map(|l| EvalMessage::from(l).into());
                    LspEvalResult {
                        diagnostics,
                        ast: Some(ast),
                    }
                }
                Err(e) => {
                    let diagnostics = vec![EvalMessage::from_anyhow(filename, e).into()];
                    LspEvalResult {
                        diagnostics,
                        ast: None,
                    }
                }
            }
        }
    }

    /// A server for use in testing that provides helpers for sending requests, correlating
    /// responses, and sending / receiving notifications
    pub struct TestServer {
        /// The thread that's actually running the server
        server_thread: Option<std::thread::JoinHandle<()>>,
        client_connection: Connection,
        /// Incrementing counter to automatically generate request IDs when making a request
        req_counter: i32,
        /// Simple incrementing document version counter
        version_counter: i32,
        /// A mapping of the requests that have arrived -> the response. Stored here as
        /// these responses might be interleaved with notifications and the like.
        responses: HashMap<RequestId, Response>,
        /// An ordered queue of all of the notifications that have been received. Drained as
        /// notifications are processed.
        notifications: VecDeque<lsp_server::Notification>,
        /// How long to wait for messages to be received.
        recv_timeout: Duration,
    }

    impl Drop for TestServer {
        fn drop(&mut self) {
            // Need to send both a Shutdown request and an Exit notification in succession
            // so that lsp_server knows to shutdown correctly.
            let req = lsp_server::Request {
                id: self.next_request_id(),
                method: Shutdown::METHOD.to_owned(),
                params: Default::default(),
            };
            if let Err(e) = self.send_request(req) {
                eprintln!("Server was already shutdown: {}", e);
            } else {
                let notif = lsp_server::Notification {
                    method: Exit::METHOD.to_owned(),
                    params: Default::default(),
                };
                if let Err(e) = self.send_notification(notif) {
                    eprintln!("Could not send Exit notification: {}", e);
                }
            }

            if let Some(server_thread) = self.server_thread.take() {
                server_thread.join().expect("test server to join");
            }
        }
    }

    impl TestServer {
        /// Generate a new request ID
        fn next_request_id(&mut self) -> RequestId {
            self.req_counter += 1;
            RequestId::from(self.req_counter)
        }

        fn next_document_version(&mut self) -> i32 {
            self.version_counter += 1;
            self.version_counter
        }

        /// Create a new request object with an automatically generated request ID.
        pub fn new_request<T: Request>(&mut self, params: T::Params) -> lsp_server::Request {
            lsp_server::Request {
                id: self.next_request_id(),
                method: T::METHOD.to_owned(),
                params: serde_json::to_value(params).unwrap(),
            }
        }

        /// Create and start a new LSP server. This sends the initialization messages, and makes
        /// sure that when the server is dropped, the threads are attempted to be stopped.
        pub(crate) fn new() -> anyhow::Result<Self> {
            let (server_connection, client_connection) = Connection::memory();

            let server_thread = std::thread::spawn(|| {
                let ctx = TestServerContext {};
                if let Err(e) = server_with_connection(server_connection, ctx) {
                    eprintln!("Stopped test server thread with error `{:?}`", e);
                }
            });

            let ret = Self {
                server_thread: Some(server_thread),
                client_connection,
                req_counter: 0,
                version_counter: 0,
                responses: Default::default(),
                notifications: Default::default(),
                recv_timeout: Duration::from_secs(2),
            };
            ret.initialize()
        }

        fn initialize(mut self) -> anyhow::Result<Self> {
            let capabilities = ClientCapabilities {
                text_document: Some(TextDocumentClientCapabilities {
                    definition: Some(GotoCapability {
                        dynamic_registration: Some(true),
                        link_support: Some(true),
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            };

            let init = InitializeParams {
                process_id: None,
                root_path: None,
                root_uri: None,
                initialization_options: None,
                capabilities,
                trace: None,
                workspace_folders: None,
                client_info: None,
                locale: None,
            };

            let init_request = self.new_request::<Initialize>(init);
            let initialize_id = self.send_request(init_request)?;

            self.get_response::<InitializeResult>(initialize_id)?;

            self.send_notification(lsp_server::Notification {
                method: Initialized::METHOD.to_owned(),
                params: serde_json::to_value(InitializedParams {})?,
            })?;

            Ok(self)
        }

        /// Send a request to the server, and get back the ID from the original message.
        pub fn send_request(&self, req: lsp_server::Request) -> anyhow::Result<RequestId> {
            let id = req.id.clone();
            self.send(Message::Request(req))?;
            Ok(id)
        }

        /// Send a notification to the server.
        pub fn send_notification(
            &self,
            notification: lsp_server::Notification,
        ) -> anyhow::Result<()> {
            self.send(Message::Notification(notification))
        }

        fn send(&self, message: Message) -> anyhow::Result<()> {
            Ok(self.client_connection.sender.send(message)?)
        }

        /// Receive messages from the server until either the response for the given request ID
        /// has been seen, or until there are no more messages and the receive method times out.
        pub fn get_response<T: DeserializeOwned>(&mut self, id: RequestId) -> anyhow::Result<T> {
            loop {
                self.receive()?;

                match self.responses.get(&id) {
                    Some(Response {
                        error: None,
                        result: Some(result),
                        ..
                    }) => {
                        break Ok(serde_json::from_value::<T>(result.clone())?);
                    }
                    Some(Response {
                        error: Some(err),
                        result: None,
                        ..
                    }) => {
                        break Err(anyhow::anyhow!("Response error: {}", err.message));
                    }
                    Some(msg) => {
                        break Err(anyhow::anyhow!(
                            "Invalid response message for request {}: {:?}",
                            id,
                            msg
                        ));
                    }
                    None => {}
                }
            }
        }

        #[allow(dead_code)]
        pub fn get_notification<T: Notification>(&mut self) -> anyhow::Result<T::Params> {
            loop {
                self.receive()?;
                if let Some(notification) = self.notifications.pop_front() {
                    break Ok(serde_json::from_value(notification.params)?);
                }
            }
        }

        /// Attempt to receive a message and either put it in the `responses` map if it's a
        /// response, or the notifications queue if it's a notification.
        ///
        /// Returns an error if an invalid message is received, or if no message is
        /// received within the timeout.
        fn receive(&mut self) -> anyhow::Result<()> {
            let message = self
                .client_connection
                .receiver
                .recv_timeout(self.recv_timeout)?;
            match message {
                Message::Request(req) => {
                    Err(anyhow::anyhow!("Got a request from the server: {:?}", req))
                }
                Message::Response(response) => match self.responses.entry(response.id.clone()) {
                    Entry::Occupied(existing) => Err(anyhow::anyhow!(
                        "Got a duplicate response for request ID {:?}: Existing: {:?}, New: {:?}",
                        response.id,
                        existing.get(),
                        response
                    )),
                    Entry::Vacant(entry) => {
                        entry.insert(response);
                        Ok(())
                    }
                },
                Message::Notification(notification) => {
                    self.notifications.push_back(notification);
                    Ok(())
                }
            }
        }

        /// Send a notification saying that a file was opened with the given contents.
        pub fn open_file(&mut self, uri: Url, contents: String) -> anyhow::Result<()> {
            let open_params = DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri,
                    language_id: String::new(),
                    version: self.next_document_version(),
                    text: contents,
                },
            };
            let open_notification = new_notification::<DidOpenTextDocument>(open_params);
            self.send_notification(open_notification)?;
            Ok(())
        }

        /// Send a notification saying that a file was changed with the given contents.
        pub fn change_file(&mut self, uri: Url, contents: String) -> anyhow::Result<()> {
            let change_params = DidChangeTextDocumentParams {
                text_document: VersionedTextDocumentIdentifier {
                    uri,
                    version: self.next_document_version(),
                },
                content_changes: vec![TextDocumentContentChangeEvent {
                    range: None,
                    range_length: None,
                    text: contents,
                }],
            };
            let change_notification = new_notification::<DidChangeTextDocument>(change_params);
            self.send_notification(change_notification)?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    use lsp_types::{
        request::GotoDefinition, GotoDefinitionParams, GotoDefinitionResponse, Location, Position,
        Range, TextDocumentIdentifier, TextDocumentPositionParams, Url,
    };

    use super::helpers::TestServer;

    #[test]
    fn sends_empty_goto_definition_on_nonexistent_file() -> anyhow::Result<()> {
        let mut server = TestServer::new()?;
        let req = server.new_request::<GotoDefinition>(GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: Url::parse("file:///tmp/nonexistent")?,
                },
                position: Default::default(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });

        let request_id = server.send_request(req)?;
        let response: GotoDefinitionResponse = server.get_response(request_id)?;
        match response {
            GotoDefinitionResponse::Array(definitions) if definitions.is_empty() => Ok(()),
            response => Err(anyhow::anyhow!(
                "Expected empty definitions, got `{:?}`",
                response
            )),
        }
    }

    #[test]
    fn sends_empty_goto_definition_on_non_access_symbol() -> anyhow::Result<()> {
        let uri = Url::parse("file:///tmp/file.star")?;

        let mut server = TestServer::new()?;
        let contents = "y = 1\ndef nothing():\n    pass\nprint(nothing())\n";
        server.open_file(uri.clone(), contents.to_owned())?;

        let goto_definition = server.new_request::<GotoDefinition>(GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position {
                    line: 1,
                    character: 6,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });

        let request_id = server.send_request(goto_definition)?;
        let response = server.get_response::<GotoDefinitionResponse>(request_id)?;
        match response {
            GotoDefinitionResponse::Array(definitions) if definitions.is_empty() => Ok(()),
            response => Err(anyhow::anyhow!(
                "Expected empty definitions, got `{:?}`",
                response
            )),
        }
    }

    #[test]
    fn goes_to_definition() -> anyhow::Result<()> {
        let uri = Url::parse("file:///tmp/file.star")?;
        let expected_location = Location {
            uri: uri.clone(),
            range: Range {
                start: Position {
                    line: 1,
                    character: 4,
                },
                end: Position {
                    line: 1,
                    character: 11,
                },
            },
        };

        let mut server = TestServer::new()?;
        let contents = "y = 1\ndef nothing():\n    pass\nprint(nothing())\n";
        server.open_file(uri.clone(), contents.to_owned())?;

        let goto_definition = server.new_request::<GotoDefinition>(GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position {
                    line: 3,
                    character: 6,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });

        let request_id = server.send_request(goto_definition)?;
        let response = server.get_response::<GotoDefinitionResponse>(request_id)?;
        match response {
            GotoDefinitionResponse::Scalar(location) => {
                assert_eq!(expected_location, location);
                Ok(())
            }
            _ => Err(anyhow::anyhow!("Got invalid message type: {:?}", response)),
        }
    }

    #[test]
    fn returns_old_definitions_if_current_file_does_not_parse() -> anyhow::Result<()> {
        let uri = Url::parse("file:///tmp/file.star")?;
        let expected_location = Location {
            uri: uri.clone(),
            range: Range {
                start: Position {
                    line: 1,
                    character: 4,
                },
                end: Position {
                    line: 1,
                    character: 11,
                },
            },
        };

        let mut server = TestServer::new()?;
        let contents = "y = 1\ndef nothing():\n    pass\nprint(nothing())\n";
        server.open_file(uri.clone(), contents.to_owned())?;
        server.change_file(uri.clone(), "\"invalid parse".to_owned())?;

        let goto_definition = server.new_request::<GotoDefinition>(GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position {
                    line: 3,
                    character: 6,
                },
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });

        let request_id = server.send_request(goto_definition)?;
        let response = server.get_response::<GotoDefinitionResponse>(request_id)?;
        match response {
            GotoDefinitionResponse::Scalar(location) => {
                assert_eq!(expected_location, location);
                Ok(())
            }
            _ => Err(anyhow::anyhow!("Got invalid message type: {:?}", response)),
        }
    }
}
