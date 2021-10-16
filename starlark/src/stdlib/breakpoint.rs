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

use std::sync::Mutex;

use anyhow::anyhow;
use itertools::Itertools;
use once_cell::sync::Lazy;
use rustyline::{error::ReadlineError, Editor};

use crate::{
    self as starlark,
    environment::GlobalsBuilder,
    eval::Evaluator,
    syntax::{AstModule, Dialect},
    values::none::NoneType,
};

// A breakpoint takes over the console UI, so having two going at once confuses everything.
// Have a global mutex to ensure one at a time.
static BREAKPOINT_MUTEX: Lazy<Mutex<State>> = Lazy::new(|| Mutex::new(State::Allow));

/// `breakpoint` function uses this trait to perform console IO.
pub(crate) trait BreakpointConsole {
    /// Return `None` on EOF.
    fn read_line(&mut self) -> anyhow::Result<Option<String>>;
    fn println(&mut self, line: &str);
}

/// Breakpoint handler implemented with `rustyline`.
pub(crate) struct RealBreakpointConsole {
    editor: Editor<()>,
}

impl BreakpointConsole for RealBreakpointConsole {
    fn read_line(&mut self) -> anyhow::Result<Option<String>> {
        match self.editor.readline("$> ") {
            Ok(line) => {
                self.editor.add_history_entry(line.as_str());
                Ok(Some(line))
            }
            // User pressed EOF - disconnected terminal, or similar
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => Ok(None),
            Err(e) => Err(e.into()),
        }
    }

    fn println(&mut self, line: &str) {
        eprintln!("{}", line);
    }
}

impl RealBreakpointConsole {
    pub(crate) fn factory() -> Box<dyn Fn() -> Box<dyn BreakpointConsole>> {
        box || box RealBreakpointConsole {
            editor: Editor::new(),
        }
    }
}

/// Is debugging allowed or not? After the user hits Ctrl-C they probably
/// just want to stop hard, so don't keep dropping them into breakpoints.
#[derive(PartialEq, Eq)]
enum State {
    Allow, // More breakpoints are fine
    Stop,  // No more breakpoints
}

/// We've run a breakpoint command, what should we do.
enum Next {
    Again,  // Accept another breakpoint command
    Resume, // Continue running
    Fail,   // Stop running
}

fn cmd_help(_eval: &mut Evaluator, rl: &mut dyn BreakpointConsole) -> anyhow::Result<Next> {
    for (name, msg, _) in COMMANDS {
        rl.println(&format!("* :{}, {}", name[0], msg))
    }
    Ok(Next::Again)
}

fn cmd_variables(eval: &mut Evaluator, rl: &mut dyn BreakpointConsole) -> anyhow::Result<Next> {
    fn truncate(mut s: String, n: usize) -> String {
        if s.len() > n {
            s.truncate(n);
            s.push_str("...");
        }
        s
    }

    for (name, value) in eval.local_variables() {
        rl.println(&format!("* {} = {}", name, truncate(value.to_string(), 80)))
    }
    Ok(Next::Again)
}

fn cmd_stack(eval: &mut Evaluator, rl: &mut dyn BreakpointConsole) -> anyhow::Result<Next> {
    for x in eval.call_stack() {
        rl.println(&format!("* {}", x))
    }
    Ok(Next::Again)
}

fn cmd_resume(_eval: &mut Evaluator, _rl: &mut dyn BreakpointConsole) -> anyhow::Result<Next> {
    Ok(Next::Resume)
}

fn cmd_fail(_eval: &mut Evaluator, _rl: &mut dyn BreakpointConsole) -> anyhow::Result<Next> {
    Ok(Next::Fail)
}

const COMMANDS: &[(
    &[&str], // Possible names
    &str,    // Help text
    fn(eval: &mut Evaluator, &mut dyn BreakpointConsole) -> anyhow::Result<Next>,
)] = &[
    (&["help", "?"], "Show this help message", cmd_help),
    (&["vars"], "Show all local variables", cmd_variables),
    (&["stack"], "Show the stack trace", cmd_stack),
    (&["resume", "quit", "exit"], "Resume execution", cmd_resume),
    (&["fail"], "Abort with a failure message", cmd_fail),
];

fn pick_command(
    x: &str,
    rl: &mut dyn BreakpointConsole,
) -> Option<fn(eval: &mut Evaluator, &mut dyn BreakpointConsole) -> anyhow::Result<Next>> {
    // If we can find a command that matches perfectly, do that
    // Otherwise return the longest match, but if they are multiple, show a warning
    let mut poss = Vec::new();
    for (names, _, cmd) in COMMANDS {
        for n in *names {
            if *n == x {
                return Some(*cmd);
            }
            if n.starts_with(x) {
                poss.push((n, cmd));
                break;
            }
        }
    }
    match poss.as_slice() {
        [] => rl.println("Unrecognised command, type :help for all commands"),
        [x] => return Some(*x.1),
        xs => rl.println(&format!(
            "Ambiguous command, could have been any of: {}",
            xs.iter().map(|x| x.0).join(" ")
        )),
    }
    None
}

fn breakpoint_loop(
    eval: &mut Evaluator,
    mut rl: Box<dyn BreakpointConsole>,
) -> anyhow::Result<State> {
    loop {
        let readline = rl.read_line()?;
        match readline {
            Some(line) => {
                if let Some(line) = line.strip_prefix(':') {
                    if let Some(cmd) = pick_command(line.trim_end(), &mut *rl) {
                        match cmd(eval, &mut *rl)? {
                            Next::Again => {}
                            Next::Resume => return Ok(State::Allow),
                            Next::Fail => return Err(anyhow!("Selected :fail at breakpoint()")),
                        }
                    }
                } else {
                    let ast = AstModule::parse("interactive", line, &Dialect::Extended);
                    let res = ast.and_then(|ast| eval.eval_statements(ast));
                    match res {
                        Err(e) => {
                            rl.println(&format!("{:#}", e));
                        }
                        Ok(v) => {
                            if !v.is_none() {
                                rl.println(&format!("{}", v))
                            }
                        }
                    }
                }
            }
            None => return Ok(State::Stop),
        }
    }
}

const BREAKPOINT_HIT_MESSAGE: &str = "BREAKPOINT HIT! :resume to continue, :help for all options";

#[starlark_module]
pub fn global(builder: &mut GlobalsBuilder) {
    fn breakpoint() -> NoneType {
        {
            let mut guard = BREAKPOINT_MUTEX.lock().unwrap();
            if *guard == State::Allow {
                let mut rl = (eval.breakpoint_handler)();
                rl.println(BREAKPOINT_HIT_MESSAGE);
                *guard = breakpoint_loop(eval, rl)?;
            }
        }
        Ok(NoneType)
    }
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, env, rc::Rc};

    use gazebo::dupe::Dupe;

    use super::*;
    use crate::{
        assert::Assert,
        environment::{Globals, Module},
    };

    #[test]
    // Test with: BREAKPOINT=1 cargo test -p starlark breakpoint -- --nocapture
    fn test_breakpoint_real() {
        if env::var("BREAKPOINT") != Ok("1".to_owned()) {
            return;
        }

        let mut a = Assert::new();
        a.globals_add(global);
        a.pass("x = [1,2,3]; breakpoint(); print(x)");
    }

    #[test]
    fn test_breakpoint_mock() {
        let module = Module::new();
        let globals = Globals::extended();
        let mut eval = Evaluator::new(&module, &globals);
        let printed_lines = Rc::new(RefCell::new(Vec::new()));
        let printed_lines_copy = printed_lines.dupe();
        eval.breakpoint_handler = box move || {
            struct Handler {
                printed_lines: Rc<RefCell<Vec<String>>>,
                called: bool,
            }

            impl BreakpointConsole for Handler {
                fn read_line(&mut self) -> anyhow::Result<Option<String>> {
                    let called = self.called;
                    self.called = true;
                    if !called {
                        Ok(Some("x".to_owned()))
                    } else {
                        Ok(None)
                    }
                }

                fn println(&mut self, line: &str) {
                    self.printed_lines.borrow_mut().push(line.to_owned());
                }
            }

            box Handler {
                printed_lines: printed_lines.dupe(),
                called: false,
            }
        };
        eval.eval_module(
            AstModule::parse(
                "x.star",
                "x = [1,2,3]; breakpoint()".to_owned(),
                &Dialect::Extended,
            )
            .unwrap(),
        )
        .unwrap();

        assert_eq!(
            vec![BREAKPOINT_HIT_MESSAGE, "[1, 2, 3]"],
            *printed_lines_copy.borrow()
        );
    }
}
