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

//! AST for parsed starlark files.

use codemap::{CodeMap, Span, Spanned};
use derivative::Derivative;
use gazebo::prelude::*;
use std::{
    fmt,
    fmt::{Display, Formatter},
    sync::Arc,
};

// Boxed types used for storing information from the parsing will be used
// especially for the location of the AST item
pub type AstExpr = Spanned<Expr>;
pub type AstArgument = Spanned<Argument>;
pub type AstString = Spanned<String>;
pub type AstParameter = Spanned<Parameter>;
pub type AstClause = Spanned<Clause>;
pub type AstInt = Spanned<i32>;
pub type AstStmt = Spanned<Stmt>;

// Wrapper around an AstModule. Must have been compiled.
#[derive(Derivative)]
#[derivative(Debug)]
pub struct AstModule {
    #[derivative(Debug = "ignore")]
    pub(crate) codemap: Arc<CodeMap>,
    pub(crate) statement: AstStmt,
}

pub(crate) trait ToAst: Sized {
    fn to_ast(self, span: Span) -> Spanned<Self> {
        Spanned { span, node: self }
    }
}

macro_rules! to_ast_trait {
    ($t1:ty, $t2:ty) => {
        impl ToAst for $t1 {}
    };
}

to_ast_trait!(i32, AstInt);
to_ast_trait!(String, AstString);

#[derive(Debug)]
pub enum Argument {
    Positional(AstExpr),
    Named(AstString, AstExpr),
    ArgsArray(AstExpr),
    KWArgsDict(AstExpr),
}
to_ast_trait!(Argument, AstArgument);

#[derive(Debug)]
pub enum Parameter {
    Normal(AstString, Option<Box<AstExpr>>),
    WithDefaultValue(AstString, Option<Box<AstExpr>>, Box<AstExpr>),
    NoArgs,
    Args(AstString, Option<Box<AstExpr>>),
    KWArgs(AstString, Option<Box<AstExpr>>),
}
to_ast_trait!(Parameter, AstParameter);

#[derive(Debug, Clone)]
pub enum AstLiteral {
    IntLiteral(AstInt),
    StringLiteral(AstString),
}

#[derive(Debug)]
pub enum Expr {
    Tuple(Vec<AstExpr>),
    Dot(Box<AstExpr>, AstString),
    Call(
        Box<AstExpr>,
        Vec<AstExpr>,
        Vec<(AstString, AstExpr)>,
        Option<Box<AstExpr>>,
        Option<Box<AstExpr>>,
    ),
    ArrayIndirection(Box<AstExpr>, Box<AstExpr>),
    Slice(
        Box<AstExpr>,
        Option<Box<AstExpr>>,
        Option<Box<AstExpr>>,
        Option<Box<AstExpr>>,
    ),
    Identifier(AstString),
    Lambda(Vec<AstParameter>, Box<AstExpr>),
    Literal(AstLiteral),
    Not(Box<AstExpr>),
    Minus(Box<AstExpr>),
    Plus(Box<AstExpr>),
    Op(Box<AstExpr>, BinOp, Box<AstExpr>),
    If(Box<AstExpr>, Box<AstExpr>, Box<AstExpr>), // Order: condition, v1, v2 <=> v1 if condition else v2
    List(Vec<AstExpr>),
    Dict(Vec<(AstExpr, AstExpr)>),
    ListComprehension(Box<AstExpr>, Vec<AstClause>),
    DictComprehension((Box<AstExpr>, Box<AstExpr>), Vec<AstClause>),
}
to_ast_trait!(Expr, AstExpr);

#[derive(Debug)]
pub struct Clause {
    pub var: Box<AstExpr>,
    pub over: Box<AstExpr>,
    pub ifs: Vec<AstExpr>,
}
to_ast_trait!(Clause, AstClause);

#[derive(Debug, Clone, Copy, Dupe, Eq, PartialEq)]
pub enum BinOp {
    Or,
    And,
    EqualsTo,
    Different,
    LessThan,
    GreaterThan,
    LessOrEqual,
    GreaterOrEqual,
    In,
    NotIn,
    Subtraction,
    Addition,
    Multiplication,
    Percent,
    FloorDivision,
    Pipe,
}

#[derive(Debug, Clone, Copy, Dupe, PartialEq, Eq)]
pub enum AssignOp {
    Assign,
    Increment,
    Decrement,
    Multiplier,
    FloorDivider,
    Percent,
}

#[derive(Debug, Copy, Clone, Dupe)]
pub enum Visibility {
    Private,
    Public,
}

#[derive(Debug)]
pub enum Stmt {
    Break,
    Continue,
    Pass,
    Return(Option<Box<AstExpr>>),
    Expression(Box<AstExpr>),
    Assign(Box<AstExpr>, AssignOp, Box<AstExpr>),
    Statements(Vec<AstStmt>),
    If(Box<AstExpr>, Box<AstStmt>),
    IfElse(Box<AstExpr>, Box<AstStmt>, Box<AstStmt>),
    For(Box<AstExpr>, Box<AstExpr>, Box<AstStmt>),
    Def(
        AstString,
        Vec<AstParameter>,
        Option<Box<AstExpr>>,
        Box<AstStmt>,
    ),
    // The Visibility of a Load is implicit from the Dialect, not written by a user
    Load(AstString, Vec<(AstString, AstString)>, Visibility),
}
to_ast_trait!(Stmt, AstStmt);

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            BinOp::Or => f.write_str(" or "),
            BinOp::And => f.write_str(" and "),
            BinOp::EqualsTo => f.write_str(" == "),
            BinOp::Different => f.write_str(" != "),
            BinOp::LessThan => f.write_str(" < "),
            BinOp::GreaterThan => f.write_str(" > "),
            BinOp::LessOrEqual => f.write_str(" <= "),
            BinOp::GreaterOrEqual => f.write_str(" >= "),
            BinOp::In => f.write_str(" in "),
            BinOp::NotIn => f.write_str(" not in "),
            BinOp::Subtraction => f.write_str(" - "),
            BinOp::Addition => f.write_str(" + "),
            BinOp::Multiplication => f.write_str(" * "),
            BinOp::Percent => f.write_str(" % "),
            BinOp::FloorDivision => f.write_str(" // "),
            BinOp::Pipe => f.write_str(" | "),
        }
    }
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            AssignOp::Assign => f.write_str(" = "),
            AssignOp::Increment => f.write_str(" += "),
            AssignOp::Decrement => f.write_str(" += "),
            AssignOp::Multiplier => f.write_str(" *= "),
            AssignOp::FloorDivider => f.write_str(" //= "),
            AssignOp::Percent => f.write_str(" %= "),
        }
    }
}

fn comma_separated_fmt<I, F>(
    f: &mut Formatter<'_>,
    v: &[I],
    converter: F,
    for_tuple: bool,
) -> fmt::Result
where
    F: Fn(&I, &mut Formatter<'_>) -> fmt::Result,
{
    for (i, e) in v.iter().enumerate() {
        f.write_str(if i == 0 { "" } else { ", " })?;
        converter(e, f)?;
    }
    if v.len() == 1 && for_tuple {
        f.write_str(",")?;
    }
    Ok(())
}

fn fmt_string_literal(f: &mut Formatter<'_>, s: &str) -> fmt::Result {
    f.write_str("\"")?;
    for c in s.chars() {
        match c {
            '\n' => f.write_str("\\n")?,
            '\t' => f.write_str("\\t")?,
            '\r' => f.write_str("\\r")?,
            '\0' => f.write_str("\\0")?,
            '"' => f.write_str("\\\"")?,
            '\\' => f.write_str("\\\\")?,
            x => f.write_str(&x.to_string())?,
        }
    }
    f.write_str("\"")
}

impl Display for AstLiteral {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AstLiteral::IntLiteral(i) => i.node.fmt(f),
            AstLiteral::StringLiteral(ref s) => fmt_string_literal(f, &s.node),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Expr::Tuple(ref e) => {
                f.write_str("(")?;
                comma_separated_fmt(f, e, |x, f| x.node.fmt(f), true)?;
                f.write_str(")")
            }
            Expr::Dot(ref e, ref s) => write!(f, "{}.{}", e.node, s.node),
            Expr::Lambda(ref params, ref e) => {
                f.write_str("(lambda ")?;
                comma_separated_fmt(f, params, |x, f| x.node.fmt(f), false)?;
                f.write_str(": ")?;
                e.node.fmt(f)?;
                f.write_str(")")
            }
            Expr::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
                write!(f, "{}(", e.node)?;
                let mut first = true;
                for a in pos {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    a.node.fmt(f)?;
                }
                for &(ref k, ref v) in named {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    write!(f, "{} = {}", k.node, v.node)?;
                }
                if let Some(ref x) = args {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    write!(f, "*{}", x.node)?;
                }
                if let Some(ref x) = kwargs {
                    if !first {
                        f.write_str(", ")?;
                    }
                    write!(f, "**{}", x.node)?;
                }
                f.write_str(")")
            }
            Expr::ArrayIndirection(ref e, ref i) => write!(f, "{}[{}]", e.node, i.node),
            Expr::Slice(ref e, ref i1, ref i2, ref i3) => {
                write!(f, "{}[]", e.node)?;
                if let Some(ref x) = i1 {
                    write!(f, "{}:", x.node)?
                } else {
                    f.write_str(":")?
                }
                if let Some(ref x) = i2 {
                    x.node.fmt(f)?
                }
                if let Some(ref x) = i3 {
                    write!(f, ":{}", x.node)?
                }
                Ok(())
            }
            Expr::Identifier(ref s) => s.node.fmt(f),
            Expr::Not(ref e) => write!(f, "(not {})", e.node),
            Expr::Minus(ref e) => write!(f, "-{}", e.node),
            Expr::Plus(ref e) => write!(f, "+{}", e.node),
            Expr::Op(ref l, ref op, ref r) => write!(f, "({}{}{})", l.node, op, r.node),
            Expr::If(ref cond, ref v1, ref v2) => {
                write!(f, "({} if {} else {})", v1.node, cond.node, v2.node)
            }
            Expr::List(ref v) => {
                f.write_str("[")?;
                comma_separated_fmt(f, v, |x, f| x.node.fmt(f), false)?;
                f.write_str("]")
            }
            Expr::Dict(ref v) => {
                f.write_str("{")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}: {}", x.0.node, x.1.node), false)?;
                f.write_str("}")
            }
            Expr::ListComprehension(ref e, ref v) => {
                write!(f, "[{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| x.node.fmt(f), false)?;
                f.write_str("]")
            }
            Expr::DictComprehension((ref k, ref v), ref c) => {
                write!(f, "{{{}: {}", k.node, v.node)?;
                comma_separated_fmt(f, c, |x, f| x.node.fmt(f), false)?;
                f.write_str("}}")
            }
            Expr::Literal(ref x) => x.fmt(f),
        }
    }
}

impl Display for Argument {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Argument::Positional(ref s) => s.node.fmt(f),
            Argument::Named(ref s, ref e) => write!(f, "{} = {}", s.node, e.node),
            Argument::ArgsArray(ref s) => write!(f, "*{}", s.node),
            Argument::KWArgsDict(ref s) => write!(f, "**{}", s.node),
        }
    }
}

impl Display for Parameter {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (prefix, name, typ, default) = match self {
            Parameter::Normal(s, t) => ("", s, t, None),
            Parameter::WithDefaultValue(s, t, e) => ("", s, t, Some(e)),
            Parameter::NoArgs => return write!(f, "*"),
            Parameter::Args(s, t) => ("*", s, t, None),
            Parameter::KWArgs(s, t) => ("**", s, t, None),
        };
        write!(f, "{}{}", prefix, name.node)?;
        if let Some(t) = typ {
            write!(f, ": {}", t.node)?;
        }
        if let Some(d) = default {
            write!(f, " = {}", d.node)?;
        }
        Ok(())
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, " for {} in {}", self.var.node, self.over.node)?;
        for x in &self.ifs {
            write!(f, " if {}", x.node)?;
        }
        Ok(())
    }
}

impl Stmt {
    fn fmt_with_tab(&self, f: &mut Formatter<'_>, tab: String) -> fmt::Result {
        match self {
            Stmt::Break => writeln!(f, "{}break", tab),
            Stmt::Continue => writeln!(f, "{}continue", tab),
            Stmt::Pass => writeln!(f, "{}pass", tab),
            Stmt::Return(Some(ref e)) => writeln!(f, "{}return {}", tab, e.node),
            Stmt::Return(None) => writeln!(f, "{}return", tab),
            Stmt::Expression(ref e) => writeln!(f, "{}{}", tab, e.node),
            Stmt::Assign(ref l, ref op, ref r) => writeln!(f, "{}{}{}{}", tab, l.node, op, r.node),
            Stmt::Statements(ref v) => {
                for s in v {
                    s.node.fmt_with_tab(f, tab.clone())?;
                }
                Ok(())
            }
            Stmt::If(ref cond, ref suite) => {
                writeln!(f, "{}if {}:", tab, cond.node)?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Stmt::IfElse(ref cond, ref suite1, ref suite2) => {
                writeln!(f, "{}if {}:", tab, cond.node)?;
                suite1.node.fmt_with_tab(f, tab.clone() + "  ")?;
                writeln!(f, "{}else:", tab)?;
                suite2.node.fmt_with_tab(f, tab + "  ")
            }
            Stmt::For(ref bind, ref coll, ref suite) => {
                writeln!(f, "{}for {} in {}:", tab, bind.node, coll.node)?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Stmt::Def(ref name, ref params, ref return_type, ref suite) => {
                write!(f, "{}def {}(", tab, name.node)?;
                comma_separated_fmt(f, params, |x, f| x.node.fmt(f), false)?;
                f.write_str(")")?;
                if let Some(rt) = return_type {
                    write!(f, " -> {}", rt.node)?;
                }
                f.write_str(":\n")?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Stmt::Load(ref filename, ref v, _) => {
                write!(f, "{}load(", tab)?;
                fmt_string_literal(f, &filename.node)?;
                comma_separated_fmt(
                    f,
                    v,
                    |x, f| {
                        write!(f, "{} = ", x.0.node)?;
                        fmt_string_literal(f, &(x.1.node))
                    },
                    false,
                )?;
                f.write_str(")\n")
            }
        }
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.fmt_with_tab(f, "".to_owned())
    }
}
