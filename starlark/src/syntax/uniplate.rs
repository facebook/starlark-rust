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

// These are more readable for formulaic code like Uniplate
#![allow(clippy::many_single_char_names)]

use crate::syntax::ast::{
    unassign, Assign, AstAssign, AstExpr, AstStmt, AstString, Clause, Expr, ForClause, Parameter,
    Stmt,
};
use either::Either;

impl Stmt {
    pub fn visit_children<'a>(&'a self, mut f: impl FnMut(Either<&'a AstStmt, &'a AstExpr>)) {
        match self {
            Stmt::Statements(xs) => xs.iter().for_each(|x| f(Either::Left(x))),
            Stmt::If(condition, box then_block) => {
                f(Either::Right(condition));
                f(Either::Left(then_block));
            }
            Stmt::IfElse(condition, box (then_block, else_block)) => {
                f(Either::Right(condition));
                f(Either::Left(then_block));
                f(Either::Left(else_block));
            }
            Stmt::Def(_, params, ret_type, body) => {
                params
                    .iter()
                    .for_each(|x| x.visit_expr(|x| f(Either::Right(x))));
                ret_type.iter().for_each(|x| f(Either::Right(x)));
                f(Either::Left(body));
            }
            Stmt::For(box (lhs, over, body)) => {
                f(Either::Right(unassign(lhs)));
                f(Either::Right(over));
                f(Either::Left(body));
            }
            // Nothing else contains nested statements
            Stmt::Break => {}
            Stmt::Continue => {}
            Stmt::Pass => {}
            Stmt::Return(ret) => {
                ret.iter().for_each(|x| f(Either::Right(x)));
            }
            Stmt::Expression(e) => f(Either::Right(e)),
            Stmt::Assign(lhs, rhs) => {
                f(Either::Right(unassign(lhs)));
                f(Either::Right(rhs));
            }
            Stmt::AssignModify(lhs, _, rhs) => {
                f(Either::Right(unassign(lhs)));
                f(Either::Right(rhs));
            }
            Stmt::Load(_, _, _) => {}
        }
    }

    pub fn visit_stmt<'a>(&'a self, mut f: impl FnMut(&'a AstStmt)) {
        self.visit_children(|x| match x {
            Either::Left(x) => f(x),
            Either::Right(_) => {} // Nothing to do
        })
    }

    pub fn visit_expr<'a>(&'a self, mut f: impl FnMut(&'a AstExpr)) {
        // Note the &mut impl on f, it's subtle, see
        // https://stackoverflow.com/questions/54613966/error-reached-the-recursion-limit-while-instantiating-funcclosure
        fn pick<'a>(x: Either<&'a AstStmt, &'a AstExpr>, f: &mut impl FnMut(&'a AstExpr)) {
            match x {
                Either::Left(x) => x.visit_children(|x| pick(x, f)),
                Either::Right(x) => f(x),
            }
        }
        self.visit_children(|x| pick(x, &mut f))
    }

    pub fn visit_stmt_result<E>(
        &self,
        mut f: impl FnMut(&AstStmt) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut result = Ok(());
        let f2 = |x: &AstStmt| {
            if result.is_ok() {
                result = f(x);
            }
        };
        self.visit_stmt(f2);
        result
    }
}

impl Parameter {
    // Split a parameter into name, type, default value
    pub fn split(&self) -> (Option<&AstString>, Option<&AstExpr>, Option<&AstExpr>) {
        match self {
            Parameter::Normal(a, b) | Parameter::Args(a, b) | Parameter::KwArgs(a, b) => {
                (Some(a), b.as_ref().map(|x| &**x), None)
            }
            Parameter::WithDefaultValue(a, b, c) => (Some(a), b.as_ref().map(|x| &**x), Some(&**c)),
            Parameter::NoArgs => (None, None, None),
        }
    }

    pub fn visit_expr<'a>(&'a self, mut f: impl FnMut(&'a AstExpr)) {
        let (_, typ, def) = self.split();
        typ.iter().for_each(|x| f(x));
        def.iter().for_each(|x| f(x));
    }
}

impl Expr {
    pub fn visit_expr<'a>(&'a self, mut f: impl FnMut(&'a AstExpr)) {
        match self {
            Expr::Tuple(xs) => xs.iter().for_each(|x| f(x)),
            Expr::Dot(x, _) => f(x),
            Expr::Call(a, b) => {
                f(a);
                b.iter().for_each(|x| f(x.expr()));
            }
            Expr::ArrayIndirection(box (a, b)) => {
                f(a);
                f(b);
            }
            Expr::Slice(a, b, c, d) => {
                f(a);
                b.iter().for_each(|x| f(x));
                c.iter().for_each(|x| f(x));
                d.iter().for_each(|x| f(x));
            }
            Expr::Identifier(_) => {}
            Expr::Lambda(args, body) => {
                args.iter().for_each(|x| x.visit_expr(|x| f(x)));
                f(body);
            }
            Expr::Literal(_) => {}
            Expr::Not(x) => f(x),
            Expr::Minus(x) => f(x),
            Expr::Plus(x) => f(x),
            Expr::BitNot(x) => f(x),
            Expr::Op(x, _, y) => {
                f(x);
                f(y);
            }
            Expr::If(box (a, b, c)) => {
                f(a);
                f(b);
                f(c);
            }
            Expr::List(x) => x.iter().for_each(|x| f(x)),
            Expr::Dict(x) => x.iter().for_each(|(x, y)| {
                f(x);
                f(y);
            }),
            Expr::ListComprehension(x, for_, y) => {
                for_.visit_expr(|x| f(x));
                y.iter().for_each(|x| x.visit_expr(|x| f(x)));
                f(x);
            }
            Expr::DictComprehension(x, for_, y) => {
                for_.visit_expr(|x| f(x));
                y.iter().for_each(|x| x.visit_expr(|x| f(x)));
                f(&x.0);
                f(&x.1);
            }
        }
    }
}

impl Assign {
    // See through compound statements (tuple, array) - mostly useful for lvalue's
    // where those compound forms are structure rather than lvalue
    pub fn visit_expr_compound<'a>(x: &'a AstAssign, mut f: impl FnMut(&'a AstExpr)) {
        fn recurse<'a>(x: &'a AstExpr, f: &mut impl FnMut(&'a AstExpr)) {
            match &**x {
                Expr::Tuple(xs) | Expr::List(xs) => xs.iter().for_each(|x| recurse(x, f)),
                _ => f(x),
            }
        }
        recurse(unassign(x), &mut f)
    }

    /// Assuming this expression was on the left-hand-side of an assignment,
    /// visit all the names that are bound by this assignment.
    /// Note that assignments like `x[i] = n` don't bind any names.
    pub fn visit_expr_lvalue<'a>(&'a self, mut f: impl FnMut(&'a AstString)) {
        fn recurse<'a>(x: &'a Expr, f: &mut impl FnMut(&'a AstString)) {
            match x {
                Expr::Identifier(x) => f(x),
                Expr::Tuple(xs) | Expr::List(xs) => xs.iter().for_each(|x| recurse(x, f)),
                _ => {}
            }
        }
        recurse(self, &mut f)
    }
}

impl ForClause {
    pub fn visit_expr<'a>(&'a self, mut f: impl FnMut(&'a AstExpr)) {
        f(unassign(&self.var));
        f(&self.over);
    }
}

impl Clause {
    pub fn visit_expr<'a>(&'a self, mut f: impl FnMut(&'a AstExpr)) {
        match self {
            Clause::For(x) => x.visit_expr(f),
            Clause::If(x) => f(x),
        }
    }
}
