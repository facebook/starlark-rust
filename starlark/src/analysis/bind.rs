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

use crate::syntax::{
    ast::{AssignOp, AstClause, AstExpr, AstParameter, AstStmt, AstString, Expr, Stmt},
    AstModule,
};
use codemap::Span;
use gazebo::prelude::*;
use std::collections::HashMap;

#[derive(Debug, Copy, Clone, Dupe, Eq, PartialEq)]
pub enum Assigner {
    Load,     // Obtained from `load`
    Argument, // From a function argument
    Assign,   // From an assignment
}

#[derive(Debug)]
pub enum Bind {
    Set(Assigner, AstString), // Variable assigned to directly
    Get(AstString),           // Variable that is referenced
    Flow,         // Flow control occurs here (if, for etc) - can arrive or leave at this point
    Scope(Scope), // Entering a new scope (lambda/def/comprehension)
}

#[derive(Debug)]
pub struct Scope {
    pub inner: Vec<Bind>,
    pub free: HashMap<String, Span>, // Things referred to in this scope, or inner scopes, that we don't define
    pub bound: HashMap<String, (Assigner, Span)>, // Things bound in this scope, doesn't include inner scope bindings
}

impl Scope {
    fn new(inner: Vec<Bind>) -> Self {
        let mut bound = HashMap::new();
        let mut free = HashMap::new();
        for x in &inner {
            match x {
                Bind::Set(assigner, x) => {
                    bound.entry(x.node.clone()).or_insert((*assigner, x.span));
                }
                Bind::Get(x) => {
                    free.entry(x.node.clone()).or_insert(x.span);
                }
                Bind::Scope(scope) => scope.free.iter().for_each(|(k, v)| {
                    free.entry(k.clone()).or_insert(*v);
                }),
                Bind::Flow => {}
            }
        }
        for x in bound.keys() {
            free.remove(x);
        }

        Self { inner, free, bound }
    }
}

fn opt_expr(x: Option<&AstExpr>, res: &mut Vec<Bind>) {
    if let Some(x) = x {
        expr(x, res)
    }
}

fn comprehension(clauses: &[AstClause], res: &mut Vec<Bind>, end: impl Fn(&mut Vec<Bind>)) {
    match clauses {
        [] => end(res),
        xs => {
            let x = &xs[0];
            expr(&x.over, res);
            let mut inner = Vec::new();
            expr_lvalue(&x.var, &mut inner);
            x.ifs.iter().for_each(|i| expr(i, &mut inner));
            comprehension(&clauses[1..], &mut inner, end);
            res.push(Bind::Scope(Scope::new(inner)))
        }
    }
}

fn expr(x: &AstExpr, res: &mut Vec<Bind>) {
    match &**x {
        Expr::Identifier(x) => res.push(Bind::Get(x.clone())),
        Expr::Lambda(args, body) => {
            let mut inner = Vec::new();
            parameters(args, res, &mut inner);
            expr(body, &mut inner);
            res.push(Bind::Scope(Scope::new(inner)));
        }

        Expr::ListComprehension(x, clauses) => comprehension(clauses, res, |res| expr(x, res)),
        Expr::DictComprehension(x, clauses) => comprehension(clauses, res, |res| {
            expr(&x.0, res);
            expr(&x.1, res)
        }),

        // Uninteresting - just recurse
        _ => x.visit_expr(|x| expr(x, res)),
    }
}

fn expr_lvalue(x: &AstExpr, res: &mut Vec<Bind>) {
    Expr::visit_expr_compound(x, |x| match &**x {
        // A value doesn't get read first
        Expr::Identifier(_) => {}
        // But things like a[i] do get read first
        _ => expr(x, res),
    });
    x.visit_expr_lvalue(|x| res.push(Bind::Set(Assigner::Assign, x.clone())))
}

fn parameters(args: &[AstParameter], res: &mut Vec<Bind>, inner: &mut Vec<Bind>) {
    for a in args {
        let (name, typ, default) = a.split();
        opt_expr(typ, res);
        opt_expr(default, res);
        if let Some(name) = name {
            inner.push(Bind::Set(Assigner::Argument, name.clone()))
        }
    }
}

fn flow(res: &mut Vec<Bind>) {
    res.push(Bind::Flow)
}

fn stmt(x: &AstStmt, res: &mut Vec<Bind>) {
    match &**x {
        Stmt::Statements(xs) => {
            for x in xs {
                stmt(x, res)
            }
        }
        Stmt::Break | Stmt::Continue | Stmt::Return(None) => flow(res),
        Stmt::Pass => {}
        Stmt::Return(Some(x)) => {
            expr(x, res);
            flow(res)
        }
        Stmt::Expression(x) => expr(x, res),
        Stmt::If(a, box b) => {
            expr(a, res);
            flow(res);
            stmt(b, res);
            flow(res);
        }
        Stmt::IfElse(a, box (b, c)) => {
            expr(a, res);
            flow(res);
            stmt(b, res);
            flow(res);
            stmt(c, res);
            flow(res);
        }
        Stmt::Def(name, args, ret, body) => {
            opt_expr(ret.as_ref().map(|x| &**x), res);
            let mut inner = Vec::new();
            parameters(args, res, &mut inner);
            res.push(Bind::Set(Assigner::Assign, name.clone()));
            stmt(body, &mut inner);
            res.push(Bind::Scope(Scope::new(inner)));
        }
        Stmt::Assign(lhs, op, rhs) => {
            expr(rhs, res);
            if *op != AssignOp::Assign {
                expr(lhs, res);
            }
            expr_lvalue(lhs, res);
        }
        Stmt::For(box (dest, inner, body)) => {
            expr(inner, res);
            expr_lvalue(dest, res);
            flow(res);
            stmt(body, res);
            flow(res)
        }
        Stmt::Load(_, args, _) => {
            for x in args {
                res.push(Bind::Set(Assigner::Load, x.0.clone()))
            }
        }
    }
}

pub fn scope(module: &AstModule) -> Scope {
    let mut res = Vec::new();
    stmt(&module.statement, &mut res);
    Scope::new(res)
}
