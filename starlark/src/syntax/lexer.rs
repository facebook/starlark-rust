/*
 * Copyright 2018 The Starlark in Rust Authors.
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

use crate::{errors::Diagnostic, syntax::dialect::Dialect};
use codemap::{CodeMap, Span};
use logos::Logos;
use std::{char, fmt, fmt::Display, iter::Peekable, sync::Arc};

/// Errors that can be generated during lexing
#[derive(Debug, Clone, PartialEq, Copy)]
pub enum LexerError {
    Indentation(u64, u64),
    InvalidCharacter(u64),
    InvalidTab(u64),
    UnfinishedStringLiteral(u64, u64),
    InvalidEscapeSequence(u64, u64),
    WrappedError { span: Span, message: &'static str },
}

impl LexerError {
    /// Convert the error to a codemap diagnostic.
    ///
    /// To build this diagnostic, the method needs the file span corresponding
    /// to the parsed file.
    pub(crate) fn add_span(self, span: Span, codemap: Arc<CodeMap>) -> Diagnostic {
        let span = match self {
            LexerError::Indentation(x, y)
            | LexerError::UnfinishedStringLiteral(x, y)
            | LexerError::InvalidEscapeSequence(x, y) => span.subspan(x, y),
            LexerError::InvalidTab(x) | LexerError::InvalidCharacter(x) => span.subspan(x, x),
            LexerError::WrappedError { span, .. } => span,
        };
        let mut e = Diagnostic::new(
            match self {
                LexerError::Indentation(..) => "Parse error: ncorrect indentation",
                LexerError::InvalidCharacter(..) => {
                    "Parse error: Character not valid at present location"
                }
                LexerError::UnfinishedStringLiteral(..) => "Parse error: unfinished string literal",
                LexerError::InvalidEscapeSequence(..) => {
                    "Parse error: invalid string escape sequence"
                }
                LexerError::InvalidTab(..) => "Parse error: tabs are not allowed in the dialect",
                LexerError::WrappedError { message, .. } => message,
            }
            .to_owned(),
        );
        e.set_span(span, codemap);
        e
    }
}

struct Lexer2<'a> {
    indent_levels: Vec<usize>,
    parens: isize, // Number of parens we have seen
    lexer: logos::Lexer<'a, Token>,
    /// When not 0, the number of ident/dedent tokens we need to issue
    indent: isize,
    indent_start: u64,
    last_new_line: bool,
    done: bool,
    dialect_allow_tabs: bool,
    // We've seen an invalid tab
    invalid_tab: bool,
}

fn enumerate_chars(x: impl Iterator<Item = char>) -> impl Iterator<Item = (usize, char)> {
    x.scan(0, |state, c| {
        *state += c.len_utf8();
        Some((*state, c))
    })
}

impl<'a> Lexer2<'a> {
    pub fn new(input: &'a str, dialect: &Dialect) -> Result<Self, LexerError> {
        let lexer = Token::lexer(input);
        let mut lexer2 = Self {
            indent_levels: Vec::with_capacity(100), // Probably more than is ever needed
            lexer,
            parens: 0,
            indent_start: 0,
            indent: 0,
            last_new_line: true,
            done: false,
            dialect_allow_tabs: dialect.enable_tabs,
            invalid_tab: false,
        };
        lexer2.calculate_indent()?;
        Ok(lexer2)
    }

    /// We have just seen a newline, read how many indents we have
    /// and then set self.indent properly
    #[allow(clippy::while_let_on_iterator)] // Buggy hint
    #[allow(clippy::comparison_chain)] // Buggy hint
    fn calculate_indent(&mut self) -> Result<(), LexerError> {
        // consume tabs and spaces, output the indentation levels
        let xs = self.lexer.remainder().as_bytes();
        let mut spaces = 0;
        let mut tabs = 0;
        let mut skip = 0;
        let mut it = xs.iter();
        self.last_new_line = true;
        self.indent_start = self.lexer.span().start as u64;
        while let Some(x) = it.next() {
            match *x as char {
                ' ' => {
                    self.last_new_line = false;
                    spaces += 1;
                }
                '\t' => {
                    self.last_new_line = false;
                    tabs += 1;
                }

                '\n' => {
                    // A line that is entirely blank gets emitted as a newline, and then
                    // we don't consume the subsequent newline character.
                    // (not sure this is necessary)
                    self.lexer.bump(spaces + tabs + skip);
                    self.last_new_line = true;
                    return Ok(());
                }
                '#' => {
                    // A line that is all comments doesn't get emitted at all
                    // Skip until the next newline
                    // Remove skip now, so we can freely add it on later
                    skip += 1 + spaces + tabs;
                    spaces = 0;
                    tabs = 0;
                    while let Some(x) = it.next() {
                        skip += 1;
                        if *x as char == '\n' {
                            self.last_new_line = true;
                            break; // only the inner loop
                        } else {
                            self.last_new_line = false;
                        }
                    }
                    self.indent_start = self.lexer.span().start as u64 + skip as u64;
                }
                _ => break,
            }
        }
        self.lexer.bump(spaces + tabs + skip);
        let indent = spaces + tabs * 8;
        if tabs > 0 && !self.dialect_allow_tabs {
            self.invalid_tab = true;
            return Ok(());
        }
        let now = self.indent_levels.last().copied().unwrap_or(0);

        self.indent = if now == indent {
            0
        } else if indent > now {
            self.indent_levels.push(indent);
            1
        } else {
            let mut dedents = 1;
            self.indent_levels.pop().unwrap();
            loop {
                let now = self.indent_levels.last().copied().unwrap_or(0);
                if now == indent {
                    break;
                } else if now > indent {
                    dedents += 1;
                    self.indent_levels.pop().unwrap();
                } else {
                    let pos = self.lexer.span();
                    return Err(LexerError::Indentation(pos.start as u64, pos.end as u64));
                }
            }
            -dedents
        };
        return Ok(());
    }

    fn wrap(&mut self, token: Token) -> Option<Result<(u64, Token, u64), LexerError>> {
        let span = self.lexer.span();
        if token != Token::Newline && token != Token::Dedent {
            self.last_new_line = false;
        }
        Some(Ok((span.start as u64, token, span.end as u64)))
    }

    fn consume_int_r(
        it: &mut Peekable<impl Iterator<Item = (usize, char)>>,
        radix: u32,
    ) -> Result<i32, ()> {
        let mut number = String::new();
        while it.peek().map_or(false, |x| x.1.is_digit(radix)) {
            number.push(it.next().unwrap().1);
        }
        let val = i32::from_str_radix(&number, radix);
        match val {
            Err(_) => Err(()),
            Ok(v) => Ok(v),
        }
    }

    // We have seen a '\' character, now parse what comes next
    fn escape(
        it: &mut Peekable<impl Iterator<Item = (usize, char)>>,
        pos: usize,
        res: &mut String,
    ) -> Result<(), LexerError> {
        if let Some((pos2, c2)) = it.next() {
            match c2 {
                'n' => {
                    res.push('\n');
                    Ok(())
                }
                'r' => {
                    res.push('\r');
                    Ok(())
                }
                't' => {
                    res.push('\t');
                    Ok(())
                }
                '0' => {
                    if it.peek().map_or(false, |x| x.1.is_digit(8)) {
                        if let Ok(r) = Self::consume_int_r(it, 8) {
                            res.push(char::from_u32(r as u32).unwrap());
                            Ok(())
                        } else {
                            Err(LexerError::InvalidEscapeSequence(pos as u64, pos2 as u64))
                        }
                    } else {
                        res.push('\0');
                        Ok(())
                    }
                }
                'x' => {
                    if let Ok(r) = Self::consume_int_r(it, 16) {
                        res.push(char::from_u32(r as u32).unwrap());
                        Ok(())
                    } else {
                        Err(LexerError::InvalidEscapeSequence(pos as u64, pos2 as u64))
                    }
                }
                '1'..='9' => Err(LexerError::InvalidEscapeSequence(pos as u64, pos2 as u64)),
                'u' => match it.next() {
                    Some((_, '{')) => {
                        if let Ok(r) = Self::consume_int_r(it, 16) {
                            if let Some((_, '}')) = it.next() {
                                res.push(char::from_u32(r as u32).unwrap());
                                return Ok(());
                            }
                        }
                        Err(LexerError::InvalidEscapeSequence(pos as u64, pos2 as u64))
                    }
                    _ => Err(LexerError::InvalidEscapeSequence(pos as u64, pos2 as u64)),
                },
                '"' | '\'' | '\\' => {
                    res.push(c2);
                    Ok(())
                }
                '\n' => Ok(()),
                _ => {
                    res.push('\\');
                    res.push(c2);
                    Ok(())
                }
            }
        } else {
            Err(LexerError::UnfinishedStringLiteral(pos as u64, pos as u64))
        }
    }

    // String parsing is a hot-spot, so parameterise by a `stop` function which gets
    // specialised for each variant
    fn string(
        &mut self,
        triple: bool,
        raw: bool,
        mut stop: impl FnMut(char) -> bool,
    ) -> Option<Result<(u64, Token, u64), LexerError>> {
        self.last_new_line = false;

        // We have seen an openning quote, which is either ' or "
        // If triple is true, it was a triple quote
        // stop lets us know when a string ends.

        let mut s = self.lexer.remainder().as_bytes();
        if triple {
            s = &s[2..];
        }

        let mut res = String::new();
        let mut adjust = 0;
        let mut s_rest = self.lexer.remainder();
        let start = self.lexer.span().start as u64 + if raw { 1 } else { 0 };
        // Take the fast path as long as the result is a slice of the original, with no changes.
        for (i, c) in s.iter().map(|c| *c as char).enumerate() {
            if stop(c) {
                let str = if triple {
                    self.lexer.remainder()[2..i].to_owned()
                } else {
                    self.lexer.remainder()[..i].to_owned()
                };
                self.lexer.bump(i + 1 + if triple { 2 } else { 0 });
                return Some(Ok((
                    start,
                    Token::StringLiteral(str),
                    start + i as u64 + if triple { 4 } else { 2 },
                )));
            } else if c == '\\' || c == '\r' || (c == '\n' && !triple) {
                res = String::with_capacity(i + 10);
                res.push_str(
                    &self.lexer.remainder()
                        [if triple { 2 } else { 0 }..if triple { 2 } else { 0 } + i],
                );
                adjust = i;
                s_rest = &self.lexer.remainder()[if triple { 2 } else { 0 } + i..];
                break;
            }
        }

        // We bailed out of the fast path, that means we now accumulate character by character,
        // might have an error, run out of characters or be dealing with escape characters.
        let mut it = enumerate_chars(s_rest.chars()).peekable();
        while let Some((i, c)) = it.next() {
            if stop(c) {
                self.lexer.bump(adjust + i + if triple { 2 } else { 0 });
                if triple {
                    res.truncate(res.len() - 2);
                }
                return Some(Ok((
                    start,
                    Token::StringLiteral(res),
                    start + adjust as u64 + i as u64 + if triple { 3 } else { 1 },
                )));
            }
            match c {
                '\n' if !triple => {
                    break; // Will raise an error about out of chars
                }
                '\r' => {
                    // We just ignore these in all modes
                }
                '\\' => {
                    if raw {
                        match it.next() {
                            Some((_, c)) => {
                                if c == '\'' || c == '"' {
                                    res.push(c);
                                } else {
                                    res.push('\\');
                                    res.push(c);
                                }
                            }
                            _ => break, // Out of chars
                        }
                    } else if let Err(e) = Self::escape(&mut it, i, &mut res) {
                        return Some(Err(e));
                    }
                }
                c => res.push(c),
            }
        }

        // We ran out of characters
        Some(Err(LexerError::UnfinishedStringLiteral(start, start + 1)))
    }

    pub fn next(&mut self) -> Option<Result<(u64, Token, u64), LexerError>> {
        if self.invalid_tab {
            Some(Err(LexerError::InvalidTab(self.lexer.span().start as u64)))
        } else if self.indent > 0 {
            self.indent -= 1;
            let span = self.lexer.span();
            self.last_new_line = false;
            Some(Ok((
                self.indent_start as u64 + 1,
                Token::Indent,
                span.end as u64,
            )))
        } else if self.indent < 0 {
            self.indent += 1;
            let span = self.lexer.span();
            Some(Ok((
                self.indent_start as u64 + 1,
                Token::Dedent,
                span.end as u64,
            )))
        } else if self.done {
            None
        } else {
            match self.lexer.next() {
                None => {
                    self.done = true;
                    if self.last_new_line {
                        assert!(self.indent_levels.is_empty());
                        None
                    } else {
                        self.indent_start = self.lexer.span().end as u64 - 1;
                        self.indent = -(self.indent_levels.len() as isize);
                        self.indent_levels.clear();
                        self.wrap(Token::Newline)
                    }
                }
                Some(token) => match token {
                    Token::Comment => {
                        self.last_new_line = false;
                        // Ideally wouldn't be recursive here, should be a tailcall
                        self.next()
                    }
                    Token::Tabs => {
                        self.invalid_tab = !self.dialect_allow_tabs;
                        // Ideally wouldn't be recursive here, should be a tailcall
                        self.next()
                    }
                    Token::Newline => {
                        if self.parens == 0 {
                            let span = self.lexer.span();
                            if let Err(e) = self.calculate_indent() {
                                return Some(Err(e));
                            }
                            Some(Ok((span.start as u64, Token::Newline, span.end as u64)))
                        } else {
                            // Ideally wouldn't be recursive here, should be a tailcall
                            self.next()
                        }
                    }
                    Token::Error => Some(Err(LexerError::InvalidCharacter(
                        self.lexer.span().start as u64,
                    ))),
                    Token::RawDoubleQuote => {
                        let raw = self.lexer.span().len() == 2;
                        if self.lexer.remainder().starts_with("\"\"") {
                            let mut qs = 0;
                            self.string(true, raw, |c| {
                                if c == '\"' {
                                    qs += 1;
                                    qs == 3
                                } else {
                                    qs = 0;
                                    false
                                }
                            })
                        } else {
                            self.string(false, raw, |c| c == '\"')
                        }
                    }
                    Token::RawSingleQuote => {
                        let raw = self.lexer.span().len() == 2;
                        if self.lexer.remainder().starts_with("''") {
                            let mut qs = 0;
                            self.string(true, raw, |c| {
                                if c == '\'' {
                                    qs += 1;
                                    qs == 3
                                } else {
                                    qs = 0;
                                    false
                                }
                            })
                        } else {
                            self.string(false, raw, |c| c == '\'')
                        }
                    }
                    Token::OpeningCurly | Token::OpeningRound | Token::OpeningSquare => {
                        self.parens += 1;
                        self.wrap(token)
                    }
                    Token::ClosingCurly | Token::ClosingRound | Token::ClosingSquare => {
                        self.parens -= 1;
                        self.wrap(token)
                    }
                    _ => self.wrap(token),
                },
            }
        }
    }
}

/// All token that can be generated by the lexer
#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token {
    #[regex(" +", logos::skip)] // Whitespace
    #[token("\\\n", logos::skip)] // Escaped newline
    #[token("\\\r\n", logos::skip)] // Escaped newline (Windows line ending)
    #[error]
    Error,

    #[regex("\t+")] // Tabs (might be an error)
    Tabs,

    // Only included to get the trailing newline correct
    #[regex(r#"#[^\n]*"#, logos::skip)]
    Comment,

    // Indentation block & meaningfull spaces
    Indent, // New indentation block
    Dedent, // Leaving an indentation block
    #[regex(r"(\r)?\n")]
    Newline, // Newline outside a string

    // Some things the lexer can't deal with well, so we step in and generate
    // things ourselves
    #[token("'")]
    #[token("r'")]
    RawSingleQuote,
    #[token("\"")]
    #[token("r\"")]
    RawDoubleQuote,

    #[regex(
        "as|import|is|class|nonlocal|del|raise|except|try|finally|while|from|with|global|yield"
    , |lex| lex.slice().to_owned())]
    Reserved(String), // One of the reserved keywords

    #[regex(
        "[a-zA-Z_][a-zA-Z0-9_]*"
    , |lex| lex.slice().to_owned())]
    Identifier(String), // An identifier

    #[regex(
        "[0-9]+"
    , |lex|
        if lex.slice().len() > 1 && &lex.slice()[0..1] == "0" {
            // Hack to make it return an error
            "".parse()
        } else {
            lex.slice().parse()
        }
    )]
    #[regex(
        "0[xX][A-Fa-f0-9]+"
    , |lex| i32::from_str_radix(&lex.slice()[2..], 16))]
    #[regex(
        "0[bB][01]+"
    , |lex| i32::from_str_radix(&lex.slice()[2..], 2))]
    #[regex(
        "0[oO][0-7]+"
    , |lex| i32::from_str_radix(&lex.slice()[2..], 8))]
    IntegerLiteral(i32), // An integer literal (123, 0x1, 0b1011, 0o755, ...)

    StringLiteral(String), // A string literal

    // Keywords
    #[token("and")]
    And,
    #[token("else")]
    Else,
    #[token("load")]
    Load,
    #[token("break")]
    Break,
    #[token("for")]
    For,
    #[token("not")]
    Not,
    #[token("continue")]
    Continue,
    #[token("if")]
    If,
    #[token("or")]
    Or,
    #[token("def")]
    Def,
    #[token("in")]
    In,
    #[token("pass")]
    Pass,
    #[token("elif")]
    Elif,
    #[token("return")]
    Return,
    #[token("lambda")]
    Lambda,
    // Symbols
    #[token(",")]
    Comma,
    #[token(";")]
    Semicolon,
    #[token(":")]
    Colon,
    #[token("+=")]
    PlusEqual,
    #[token("-=")]
    MinusEqual,
    #[token("*=")]
    StarEqual,
    #[token("/=")]
    SlashEqual,
    #[token("//=")]
    DoubleSlashEqual,
    #[token("%=")]
    PercentEqual,
    #[token("==")]
    DoubleEqual,
    #[token("!=")]
    BangEqual,
    #[token("<=")]
    LessEqual,
    #[token(">=")]
    GreaterEqual,
    #[token("**")]
    DoubleStar,
    #[token("->")]
    RightArrow,
    #[token("=")]
    Equal,
    #[token("<")]
    LessThan,
    #[token(">")]
    GreaterThan,
    #[token("-")]
    Minus,
    #[token("+")]
    Plus,
    #[token("*")]
    Star,
    #[token("%")]
    Percent,
    #[token("/")]
    Slash,
    #[token("//")]
    DoubleSlash,
    #[token(".")]
    Dot,
    #[token("|")]
    Pipe,

    // Brackets
    #[token("[")]
    OpeningSquare,
    #[token("{")]
    OpeningCurly,
    #[token("(")]
    OpeningRound,
    #[token("]")]
    ClosingSquare,
    #[token("}")]
    ClosingCurly,
    #[token(")")]
    ClosingRound,
}

impl Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Error => write!(f, "lexical error"),
            Token::Indent => write!(f, "new indentation block"),
            Token::Dedent => write!(f, "end of indentation block"),
            Token::Newline => write!(f, "new line"),
            Token::And => write!(f, "keyword 'and'"),
            Token::Else => write!(f, "keyword 'else'"),
            Token::Load => write!(f, "keyword 'load'"),
            Token::Break => write!(f, "keyword 'break'"),
            Token::For => write!(f, "keyword 'for'"),
            Token::Not => write!(f, "keyword 'not'"),
            Token::Continue => write!(f, "keyword 'continue'"),
            Token::If => write!(f, "keyword 'if'"),
            Token::Or => write!(f, "keyword 'or'"),
            Token::Def => write!(f, "keyword 'def'"),
            Token::In => write!(f, "keyword 'in'"),
            Token::Pass => write!(f, "keyword 'pass'"),
            Token::Elif => write!(f, "keyword 'elif'"),
            Token::Return => write!(f, "keyword 'return'"),
            Token::Lambda => write!(f, "keyword 'lambda'"),
            Token::Comma => write!(f, "symbol ','"),
            Token::Semicolon => write!(f, "symbol ';'"),
            Token::Colon => write!(f, "symbol ':'"),
            Token::PlusEqual => write!(f, "symbol '+='"),
            Token::MinusEqual => write!(f, "symbol '-='"),
            Token::StarEqual => write!(f, "symbol '*='"),
            Token::SlashEqual => write!(f, "symbol '/='"),
            Token::DoubleSlashEqual => write!(f, "symbol '//='"),
            Token::PercentEqual => write!(f, "symbol '%='"),
            Token::DoubleEqual => write!(f, "symbol '=='"),
            Token::BangEqual => write!(f, "symbol '!='"),
            Token::LessEqual => write!(f, "symbol '<='"),
            Token::GreaterEqual => write!(f, "symbol '>='"),
            Token::DoubleStar => write!(f, "symbol '**'"),
            Token::RightArrow => write!(f, "symbol '->'"),
            Token::Equal => write!(f, "symbol '='"),
            Token::LessThan => write!(f, "symbol '<'"),
            Token::GreaterThan => write!(f, "symbol '>'"),
            Token::Minus => write!(f, "symbol '-'"),
            Token::Plus => write!(f, "symbol '+'"),
            Token::Star => write!(f, "symbol '*'"),
            Token::Percent => write!(f, "symbol '%'"),
            Token::Slash => write!(f, "symbol '/'"),
            Token::DoubleSlash => write!(f, "symbol '//'"),
            Token::Dot => write!(f, "symbol '.'"),
            Token::Pipe => write!(f, "symbol '|'"),
            Token::OpeningSquare => write!(f, "symbol '['"),
            Token::OpeningCurly => write!(f, "symbol '{{'"),
            Token::OpeningRound => write!(f, "symbol '('"),
            Token::ClosingSquare => write!(f, "symbol ']'"),
            Token::ClosingCurly => write!(f, "symbol '}}'"),
            Token::ClosingRound => write!(f, "symbol ')'"),
            Token::Reserved(s) => write!(f, "reserved keyword '{}'", s),
            Token::Identifier(s) => write!(f, "identifier '{}'", s),
            Token::IntegerLiteral(i) => write!(f, "integer literal '{}'", i),
            Token::StringLiteral(s) => write!(f, "string literal '{}'", s),
            Token::RawSingleQuote => write!(f, "starting '"),
            Token::RawDoubleQuote => write!(f, "starting \""),
            Token::Comment => write!(f, "comment"),
            Token::Tabs => Ok(()),
        }
    }
}

pub type LexerItem = Result<(u64, Token, u64), LexerError>;

/// An iterator over a string slice that convert it to a list of token, i.e. the
/// lexer.
#[derive(Debug)]
pub struct Lexer {
    input: String,
    /// Byte offset of the next char in `input`
    pos_bytes: usize,
    offset: u64,
    process_end_of_file: bool,
    last_new_line: bool,
    last_pos: u64,
    last_next: Option<(u64, char)>,
    indentation_stack: Vec<u32>,
    parentheses: i32,
    backlog: Vec<LexerItem>,
    enable_tabs: bool,
}

impl Lexer {
    /// Create a new lexer from a string slice
    pub fn new(input: &str, dialect: &Dialect) -> Self {
        if true {
            fn eq(
                x: &Option<Result<(u64, Token, u64), LexerError>>,
                y: &Option<Result<(u64, Token, u64), LexerError>>,
            ) -> bool {
                match (x, y) {
                    (Some(Ok((_, x, _))), Some(Ok((_, y, _))))
                        if x == y && [Token::Newline, Token::Indent, Token::Dedent].contains(x) =>
                    {
                        true
                    }
                    (Some(Err(_)), Some(Err(_))) => true,
                    _ => x == y,
                }
            }

            let mut l1 = Lexer::new_unchecked(input, dialect);
            let mut l2 = Lexer2::new(input, dialect).unwrap();
            loop {
                let s1 = l1.next();
                let s2 = l2.next();
                if !eq(&s1, &s2) {
                    println!("{}", input);
                    panic!("Lexemes not equal OLD {:?} vs NEW {:?}", s1, s2);
                }
                // println!("EQUAL: {:?}", s1);
                if s1.map_or(true, |x| x.is_err()) {
                    break;
                }
            }
        }

        Self::new_unchecked(input, dialect)
    }

    pub fn new_unchecked(input: &str, dialect: &Dialect) -> Self {
        let input = input.to_owned();
        Lexer {
            input,
            pos_bytes: 0,
            offset: 0,
            process_end_of_file: true,
            last_new_line: true,
            last_pos: 0,
            last_next: None,
            indentation_stack: Vec::new(),
            parentheses: 0,
            backlog: Vec::new(),
            enable_tabs: dialect.enable_tabs,
        }
    }

    /// Enqueue a
    fn is_nl(c: char) -> bool {
        match c {
            '\n' | '\r' | '\u{2028}' | '\u{2029}' => true,
            _ => false,
        }
    }

    fn peek(&mut self) -> Option<(u64, char)> {
        match self.input[self.pos_bytes..].chars().next() {
            Some(c) => Some((self.pos_bytes as u64 + self.offset, c)),
            None => None,
        }
    }

    fn pop(&mut self) -> Option<(u64, char)> {
        let mut char_indices = self.input[self.pos_bytes..].char_indices();
        self.last_next = match char_indices.next() {
            Some((_, c)) => {
                let pos = self.pos_bytes;
                self.pos_bytes = match char_indices.next() {
                    Some((len, _)) => self.pos_bytes + len,
                    None => self.input.len(),
                };
                self.last_new_line = Lexer::is_nl(c);
                Some((pos as u64 + self.offset, c))
            }
            None => {
                self.last_new_line = false;
                None
            }
        };
        self.last_next
    }

    fn terminate(&mut self) {
        self.pos_bytes = self.input.len();
        self.indentation_stack.clear();
        self.parentheses = 0;
    }

    fn next_char(&mut self) -> char {
        self.pop().unwrap_or((0, '\0')).1
    }

    fn peek_char(&mut self) -> char {
        self.peek().unwrap_or((0, '\0')).1
    }

    fn return_none(&mut self) -> Option<LexerItem> {
        // Emit a newline and N DEDENT at EOF
        let p = self.end_pos();
        if !self.last_new_line {
            self.last_new_line = true;
            Some(Ok((p.1, Token::Newline, p.1)))
        } else if self.ihead() > 0 && self.process_end_of_file {
            self.indentation_stack.pop();
            Some(Ok((p.1, Token::Dedent, p.1)))
        } else {
            None
        }
    }

    fn ihead(&self) -> u32 {
        *self.indentation_stack.last().unwrap_or(&0)
    }

    fn begin(&mut self) {
        if let Some((i, ..)) = self.peek() {
            self.last_pos = i;
        }
    }

    fn end_pos(&mut self) -> (u64, u64) {
        if let Some((end, ..)) = self.peek() {
            (self.last_pos, end)
        } else if let Some((i, c)) = self.last_next {
            (self.last_pos, i + (c.len_utf8() as u64))
        } else {
            (self.last_pos, self.last_pos)
        }
    }

    fn end(&mut self, res: Token) -> Option<LexerItem> {
        let p = self.end_pos();
        assert!(p.0 <= p.1, "{} > {}", p.0, p.1);
        Some(Ok((p.0, res, p.1)))
    }

    fn consume(&mut self, res: Token) -> Option<LexerItem> {
        self.pop();
        self.end(res)
    }

    fn invalid(&mut self) -> Option<LexerItem> {
        let p = self.end_pos();
        Some(Err(LexerError::InvalidCharacter(p.1)))
    }

    fn internal_next(&mut self) -> Option<LexerItem> {
        if !self.backlog.is_empty() {
            return self.backlog.pop();
        }
        if self.peek().is_none() {
            return self.return_none();
        }
        let r = self.consume_token();
        if let Some(Err(_)) = r {
            // In case of errors, consume the whole input so we stop on next call
            self.terminate();
        } else if r.is_none() {
            return self.return_none();
        }
        r
    }
}

impl Iterator for Lexer {
    type Item = LexerItem;

    fn next(&mut self) -> Option<Self::Item> {
        self.internal_next()
    }
}

// Consumers to actually consume token
impl Lexer {
    fn token_from_identifier(identifier: &str) -> Token {
        match identifier {
            "and" => Token::And,
            "else" => Token::Else,
            "load" => Token::Load,
            "break" => Token::Break,
            "for" => Token::For,
            "not" => Token::Not,
            "continue" => Token::Continue,
            "if" => Token::If,
            "or" => Token::Or,
            "def" => Token::Def,
            "in" => Token::In,
            "pass" => Token::Pass,
            "elif" => Token::Elif,
            "return" => Token::Return,
            "lambda" => Token::Lambda,
            "as" | "import" | "is" | "class" | "nonlocal" | "del" | "raise" | "except" | "try"
            | "finally" | "while" | "from" | "with" | "global" | "yield" => {
                Token::Reserved(identifier.to_owned())
            }
            _ => Token::Identifier(identifier.to_owned()),
        }
    }

    fn skip_comment(&mut self) {
        assert_eq!(self.next_char(), '#');
        loop {
            match self.peek_char() {
                '\n' | '\r' | '\u{2028}' | '\u{2029}' | '\0' => return,
                _ => {
                    self.pop();
                }
            }
        }
    }

    fn skip_spaces(&mut self, newline: bool) -> Option<LexerItem> {
        loop {
            match self.peek_char() {
                '\n' | '\r' | '\u{2028}' | '\u{2029}' => {
                    if newline {
                        self.pop();
                    } else {
                        return None;
                    }
                }
                '\\' => {
                    self.pop();
                    if self.peek_char() != '\n' {
                        return self.invalid();
                    } else {
                        self.pop();
                    }
                }
                ' ' => {
                    self.pop();
                }
                '\t' => {
                    if self.enable_tabs {
                        self.pop();
                    } else {
                        return Some(Err(LexerError::InvalidTab(self.end_pos().1)));
                    }
                }
                '#' => self.skip_comment(),
                _ => return None,
            };
        }
    }

    fn consume_spaces(&mut self) -> Result<u32, LexerError> {
        let mut result = 0;
        loop {
            match self.peek_char() {
                '\t' => {
                    if !self.enable_tabs {
                        return Err(LexerError::InvalidTab(self.end_pos().1));
                    }
                    result += 8 - (result % 8);
                }
                ' ' => result += 1,
                _ => return Ok(result),
            };
            self.pop();
        }
    }

    fn consume_indentation(&mut self) -> Option<LexerItem> {
        loop {
            self.begin();
            let spaces = match self.consume_spaces() {
                Ok(spaces) => spaces,
                Err(e) => {
                    return Some(Err(e));
                }
            };
            let p = self.peek_char();
            if Lexer::is_nl(p) {
                // ignore because it is an empty line, but still return new line
                return None;
            } else if p == '#' {
                // Ignore the comment and start again
                self.skip_comment();
                self.consume_nl();
                continue;
            } else if spaces > self.ihead() {
                self.indentation_stack.push(spaces);
                return self.end(Token::Indent);
            } else if spaces == self.ihead() {
                return None;
            } else {
                let mut step = 0;
                while spaces < self.ihead() {
                    self.indentation_stack.pop();
                    step += 1;
                }
                if spaces == self.ihead() {
                    let r = self.end(Token::Dedent);
                    while step > 1 {
                        self.backlog.push(r.clone().unwrap());
                        step -= 1;
                    }
                    return r;
                } else {
                    let p = self.end_pos();
                    return Some(Err(LexerError::Indentation(p.0, p.1)));
                }
            }
        }
    }

    fn consume_nl(&mut self) -> Option<LexerItem> {
        self.begin();
        match (self.next_char(), self.peek_char()) {
            ('\n', '\r') | ('\r', '\n') => self.consume(Token::Newline),
            _ => self.end(Token::Newline),
        }
    }

    fn consume_identifier_queue(&mut self, head: &str) -> Option<LexerItem> {
        let mut result = head.to_owned();
        while self.peek_char().is_alphabetic()
            || self.peek_char().is_digit(10)
            || self.peek_char() == '_'
        {
            result.push(self.next_char());
        }
        assert!(!result.is_empty());
        self.end(Self::token_from_identifier(&result))
    }

    fn consume_identifier(&mut self) -> Option<LexerItem> {
        self.begin();
        assert!(!self.peek_char().is_digit(10));
        self.consume_identifier_queue("")
    }

    fn consume_int_r(&mut self, radix: u32) -> Result<i32, ()> {
        let mut number = String::new();
        while self.peek_char().is_digit(radix) {
            number.push(self.next_char());
        }
        let val = i32::from_str_radix(&number, radix);
        match val {
            Err(_) => Err(()),
            Ok(v) => Ok(v),
        }
    }

    fn consume_int_radix(&mut self, radix: u32) -> Option<LexerItem> {
        let val = self.consume_int_r(radix);
        match val {
            Err(_) => self.invalid(),
            Ok(v) => self.end(Token::IntegerLiteral(v)),
        }
    }

    fn consume_int(&mut self) -> Option<LexerItem> {
        self.begin();
        let cur = self.peek_char();
        if cur == '0' {
            self.pop();
            let cur = self.peek_char();
            match cur {
                'o' | 'O' => {
                    self.pop();
                    self.consume_int_radix(8)
                }
                'x' | 'X' => {
                    self.pop();
                    self.consume_int_radix(16)
                }
                'b' | 'B' => {
                    self.pop();
                    self.consume_int_radix(2)
                }
                c if !c.is_numeric() => self.end(Token::IntegerLiteral(0)),
                _ => self.invalid(),
            }
        } else {
            self.consume_int_radix(10)
        }
    }

    fn consume_escape_sequence(&mut self, _triple: bool) -> Result<Option<char>, LexerError> {
        if let Some((pos, c)) = self.pop() {
            assert_eq!(c, '\\');
            if let Some((pos2, c2)) = self.peek() {
                match c2 {
                    'n' => {
                        self.pop();
                        Ok(Some('\n'))
                    }
                    'r' => {
                        self.pop();
                        Ok(Some('\r'))
                    }
                    't' => {
                        self.pop();
                        Ok(Some('\t'))
                    }
                    '0' => {
                        self.pop();
                        if self.peek_char().is_digit(8) {
                            if let Ok(r) = self.consume_int_r(8) {
                                Ok(Some(char::from_u32(r as u32).unwrap()))
                            } else {
                                let p = self.end_pos();
                                Err(LexerError::InvalidEscapeSequence(pos, p.1))
                            }
                        } else {
                            Ok(Some('\0'))
                        }
                    }
                    'x' => {
                        self.pop();
                        if let Ok(r) = self.consume_int_r(16) {
                            Ok(Some(char::from_u32(r as u32).unwrap()))
                        } else {
                            let p = self.end_pos();
                            Err(LexerError::InvalidEscapeSequence(pos, p.1))
                        }
                    }
                    '1'..='9' => {
                        self.pop();
                        Err(LexerError::InvalidEscapeSequence(pos, pos2 + 1))
                    }
                    '\n' => {
                        self.pop();
                        // if triple {
                        Ok(None)
                        /*
                        } else {
                            Err(LexerError::InvalidEscapeSequence(pos, pos2 + 1))
                        }*/
                    }
                    'u' => {
                        self.pop();
                        let c = self.next_char();
                        if c != '{' {
                            let p = self.end_pos();
                            Err(LexerError::InvalidEscapeSequence(pos, p.1))
                        } else if let Ok(r) = self.consume_int_r(16) {
                            let c = self.next_char();
                            if c != '}' {
                                let p = self.end_pos();
                                Err(LexerError::InvalidEscapeSequence(pos, p.1))
                            } else {
                                Ok(Some(char::from_u32(r as u32).unwrap()))
                            }
                        } else {
                            let p = self.end_pos();
                            Err(LexerError::InvalidEscapeSequence(pos, p.1))
                        }
                    }
                    '"' | '\'' | '\\' => {
                        self.pop();
                        Ok(Some(c2))
                    }
                    _ => Ok(Some('\\')),
                }
            } else {
                Err(LexerError::InvalidEscapeSequence(pos, pos + 1))
            }
        } else {
            panic!("This is a bug");
        }
    }

    fn consume_string(&mut self, raw: bool) -> Option<LexerItem> {
        self.begin();
        let mut res = String::new();
        let quote = self.next_char();
        let mut triple = false;
        if self.peek_char() == quote {
            self.next_char();
            if self.peek_char() == quote {
                self.next_char();
                triple = true;
            } else {
                return self.end(Token::StringLiteral(res));
            }
        }
        loop {
            match self.peek_char() {
                '\\' => {
                    if raw {
                        self.pop();
                        if self.peek_char() == quote {
                            self.pop();
                            res.push(quote);
                        } else {
                            res.push('\\');
                        }
                    } else {
                        match self.consume_escape_sequence(triple) {
                            Ok(Some(x)) => res.push(x),
                            Ok(None) => {}
                            Err(c) => return Some(Err(c)),
                        }
                    }
                }
                '\n' | '\r' | '\u{2028}' | '\u{2029}' => {
                    if triple {
                        res.push(self.next_char());
                    } else {
                        let p = self.end_pos();
                        return Some(Err(LexerError::UnfinishedStringLiteral(p.0, p.1)));
                    }
                }
                '\0' => {
                    let p = self.end_pos();
                    return Some(Err(LexerError::UnfinishedStringLiteral(p.0, p.1)));
                }
                x if x == quote => {
                    self.pop();
                    if triple {
                        if self.peek_char() == quote {
                            self.pop();
                            if self.peek_char() == quote {
                                self.pop();
                                break;
                            } else {
                                res.push(quote);
                                res.push(quote);
                            }
                        } else {
                            res.push(quote);
                        }
                    } else {
                        break;
                    }
                }
                x => {
                    self.pop();
                    res.push(x);
                }
            }
        }
        self.end(Token::StringLiteral(res))
    }

    fn consume_token(&mut self) -> Option<LexerItem> {
        if self.last_new_line && self.parentheses == 0 {
            if let Some(r) = self.consume_indentation() {
                return Some(r);
            }
        } else {
            let skip_newline = self.parentheses > 0;
            if let Some(x) = self.skip_spaces(skip_newline) {
                return Some(x);
            }
        }
        self.begin();
        match self.peek_char() {
            '\0' => None,
            '\n' | '\r' | '\u{2028}' | '\u{2029}' => self.consume_nl(),
            '\'' | '"' => self.consume_string(false),
            'r' => {
                self.pop();
                let p = self.peek_char();
                if p == '\'' || p == '"' {
                    self.consume_string(true)
                } else {
                    self.consume_identifier_queue("r")
                }
            }
            '0'..='9' => self.consume_int(),
            '_' => self.consume_identifier(),
            c if c.is_alphabetic() => self.consume_identifier(),
            ',' => self.consume(Token::Comma),
            ';' => self.consume(Token::Semicolon),
            ':' => self.consume(Token::Colon),
            '+' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::PlusEqual)
                } else {
                    self.end(Token::Plus)
                }
            }
            '-' => {
                self.pop();
                match self.peek_char() {
                    '=' => self.consume(Token::MinusEqual),
                    '>' => self.consume(Token::RightArrow),
                    _ => self.end(Token::Minus),
                }
            }
            '*' => {
                self.pop();
                match self.peek_char() {
                    '=' => self.consume(Token::StarEqual),
                    '*' => self.consume(Token::DoubleStar),
                    _ => self.end(Token::Star),
                }
            }
            '/' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::SlashEqual)
                } else if self.peek_char() == '/' {
                    self.pop();
                    if self.peek_char() == '=' {
                        self.consume(Token::DoubleSlashEqual)
                    } else {
                        self.end(Token::DoubleSlash)
                    }
                } else {
                    self.end(Token::Slash)
                }
            }
            '%' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::PercentEqual)
                } else {
                    self.end(Token::Percent)
                }
            }
            '=' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::DoubleEqual)
                } else {
                    self.end(Token::Equal)
                }
            }
            '!' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::BangEqual)
                } else {
                    self.invalid()
                }
            }
            '<' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::LessEqual)
                } else {
                    self.end(Token::LessThan)
                }
            }
            '>' => {
                self.pop();
                if self.peek_char() == '=' {
                    self.consume(Token::GreaterEqual)
                } else {
                    self.end(Token::GreaterThan)
                }
            }
            '|' => self.consume(Token::Pipe),
            '.' => self.consume(Token::Dot),
            '[' => {
                self.parentheses += 1;
                self.consume(Token::OpeningSquare)
            }
            ']' => {
                self.parentheses -= 1;
                self.consume(Token::ClosingSquare)
            }
            '(' => {
                self.parentheses += 1;
                self.consume(Token::OpeningRound)
            }
            ')' => {
                self.parentheses -= 1;
                self.consume(Token::ClosingRound)
            }
            '{' => {
                self.parentheses += 1;
                self.consume(Token::OpeningCurly)
            }
            '}' => {
                self.parentheses -= 1;
                self.consume(Token::ClosingCurly)
            }
            _ => self.invalid(),
        }
    }
}
