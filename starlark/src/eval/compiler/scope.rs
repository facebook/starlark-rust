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
    codemap::CodeMap,
    environment::{names::MutableNames, slots::ModuleSlotId, EnvironmentError, Globals, Module},
    errors::Diagnostic,
    eval::runtime::slots::LocalSlotId,
    syntax::{
        ast::{
            Assign, AssignIdent, AstArgumentP, AstAssignIdentP, AstAssignP, AstExprP, AstNoPayload,
            AstParameterP, AstPayload, AstStmtP, AstString, ClauseP, ExprP, ForClauseP, ParameterP,
            Stmt, StmtP, Visibility,
        },
        payload_map::AstPayloadFunction,
        uniplate::VisitMut,
    },
    values::FrozenValue,
};
use gazebo::dupe::Dupe;
use indexmap::map::IndexMap;
use std::{
    collections::{hash_map, HashMap},
    mem,
};

pub(crate) struct Scope<'a> {
    pub(crate) scope_data: ScopeData,
    module: &'a MutableNames,
    // The first scope is a module-level scope (including comprehensions in module scope).
    // The rest are scopes for functions (which include their comprehensions).
    locals: Vec<ScopeId>,
    unscopes: Vec<Unscope>,
    codemap: CodeMap,
    globals: &'a Globals,
    pub(crate) errors: Vec<anyhow::Error>,
}

struct UnscopeBinding {
    slot: LocalSlotId,
    /// Variable mappings in local scope are overwritten by comprehension variables.
    ///
    /// When we enter comprehension, we replace local scope variable slots with comprehension
    /// scope slots. This field stores the original slot in the local scope,
    /// or `None` if there was no mapping for the variable.
    ///
    /// When we pop the comprehension scope, we restore the mapping from this value.
    undo: Option<LocalSlotId>,
}

#[derive(Default)]
struct Unscope(HashMap<String, UnscopeBinding>);

#[derive(Default, Debug)]
pub(crate) struct ScopeNames {
    /// The number of slots this scope uses, including for parameters and `parent`.
    /// The next required slot would be at index `used`.
    pub used: usize,
    /// The names that are in this scope
    pub mp: HashMap<String, LocalSlotId>,
    /// Slots to copy from the parent. (index in parent, index in child).
    /// Module-level identifiers are not copied over, to avoid excess copying.
    pub parent: Vec<(LocalSlotId, LocalSlotId)>,
}

impl ScopeNames {
    fn copy_parent(&mut self, parent: LocalSlotId, name: &str) -> LocalSlotId {
        assert!(self.get_name(name).is_none()); // Or we'll be overwriting our variable
        let res = self.add_name(name);
        self.parent.push((parent, res));
        res
    }

    fn next_slot(&mut self) -> LocalSlotId {
        let res = LocalSlotId::new(self.used);
        self.used += 1;
        res
    }

    fn add_name(&mut self, name: &str) -> LocalSlotId {
        let slot = self.next_slot();
        let old_slot = self.mp.insert(name.to_owned(), slot);
        assert!(old_slot.is_none());
        slot
    }

    fn add_scoped(&mut self, name: &str, unscope: &mut Unscope) -> LocalSlotId {
        match unscope.0.entry(name.to_owned()) {
            hash_map::Entry::Occupied(e) => e.get().slot,
            hash_map::Entry::Vacant(e) => {
                let slot = self.next_slot();
                let undo = match self.mp.get_mut(name) {
                    Some(v) => {
                        let old = *v;
                        *v = slot;
                        Some(old)
                    }
                    None => {
                        self.mp.insert(name.to_owned(), slot);
                        None
                    }
                };
                e.insert(UnscopeBinding { slot, undo });
                slot
            }
        }
    }

    fn unscope(&mut self, unscope: Unscope) {
        for (name, UnscopeBinding { undo, .. }) in unscope.0 {
            match undo {
                None => {
                    self.mp.remove(&name);
                }
                Some(v) => *self.mp.get_mut(&name).unwrap() = v,
            }
        }
    }

    fn get_name(&self, name: &str) -> Option<LocalSlotId> {
        self.mp.get(name).copied()
    }
}

#[derive(Copy, Clone, Dupe, Debug)]
pub(crate) enum Slot {
    Module(ModuleSlotId), // Top-level module scope
    Local(LocalSlotId),   // Local scope, always mutable
}

impl<'a> Scope<'a> {
    fn top_scope_id(&self) -> ScopeId {
        *self.locals.last().unwrap()
    }

    fn scope_at_level(&self, level: usize) -> &ScopeNames {
        let scope_id = self.locals[level];
        self.scope_data.get_scope(scope_id)
    }

    fn scope_at_level_mut(&mut self, level: usize) -> &mut ScopeNames {
        let scope_id = self.locals[level];
        self.scope_data.mut_scope(scope_id)
    }

    pub fn enter_module(
        module: &'a MutableNames,
        scope_id: ScopeId,
        mut scope_data: ScopeData,
        code: &mut CstStmt,
        globals: &'a Globals,
        codemap: CodeMap,
    ) -> Self {
        // Not really important, sanity check
        assert_eq!(scope_id, ScopeId(0));

        let mut locals = IndexMap::new();
        Stmt::collect_defines(code, &mut scope_data, &mut locals);
        for (x, binding_id) in locals {
            let binding = scope_data.mut_binding(binding_id);
            let slot = module.add_name_visibility(x, binding.vis);
            let old_slot = mem::replace(&mut binding.slot, Some(Slot::Module(slot)));
            assert!(old_slot.is_none());
        }

        // Here we traverse the AST second time to collect scopes of defs
        Self::collect_defines_recursively(&mut scope_data, code);
        let mut scope = Self {
            scope_data,
            module,
            locals: vec![scope_id],
            unscopes: Vec::new(),
            codemap,
            globals,
            errors: Vec::new(),
        };
        scope.resolve_idents(code);
        scope
    }

    // Number of module slots I need, number of local anon slots I need
    pub fn exit_module(mut self) -> (usize, usize, ScopeData) {
        assert!(self.locals.len() == 1);
        assert!(self.unscopes.is_empty());
        let scope_id = self.locals.pop().unwrap();
        let scope = self.scope_data.get_scope(scope_id);
        assert!(scope.parent.is_empty());
        (self.module.slot_count(), scope.used, self.scope_data)
    }

    fn collect_defines_in_def(
        scope_data: &mut ScopeData,
        scope_id: ScopeId,
        params: &mut [CstParameter],
        body: Option<&mut CstStmt>,
    ) {
        let params = params.iter_mut().flat_map(|p| match &mut p.node {
            ParameterP::Normal(n, ..) => Some(n),
            ParameterP::WithDefaultValue(n, ..) => Some(n),
            ParameterP::NoArgs => None,
            ParameterP::Args(n, ..) => Some(n),
            ParameterP::KwArgs(n, ..) => Some(n),
        });
        let mut locals: IndexMap<&str, _> = IndexMap::new();
        for p in params {
            // Subtle invariant: the slots for the params must be ordered and at the
            // beginning
            let old_local = locals.insert(&p.0, scope_data.new_binding(Visibility::Public).0);
            assert!(old_local.is_none());
        }
        if let Some(code) = body {
            Stmt::collect_defines(code, scope_data, &mut locals);
        }
        for (name, binding_id) in locals.into_iter() {
            let slot = scope_data.mut_scope(scope_id).add_name(name);
            let binding = scope_data.mut_binding(binding_id);
            let old_slot = mem::replace(&mut binding.slot, Some(Slot::Local(slot)));
            assert!(old_slot.is_none());
        }
    }

    fn collect_defines_recursively(scope_data: &mut ScopeData, code: &mut CstStmt) {
        if let StmtP::Def(_name, params, _ret, suite, scope_id) = &mut code.node {
            // Here we traverse the AST twice: once for this def scope,
            // second time below for nested defs.
            Self::collect_defines_in_def(scope_data, *scope_id, params, Some(suite));
        }

        code.visit_children_mut(&mut |visit| match visit {
            VisitMut::Expr(e) => Self::collect_defines_recursively_in_expr(scope_data, e),
            VisitMut::Stmt(s) => Self::collect_defines_recursively(scope_data, s),
        });
    }

    fn collect_defines_recursively_in_expr(scope_data: &mut ScopeData, code: &mut CstExpr) {
        if let ExprP::Lambda(params, _expr, scope_id) = &mut code.node {
            Self::collect_defines_in_def(scope_data, *scope_id, params, None);
        }

        code.visit_expr_mut(|e| Self::collect_defines_recursively_in_expr(scope_data, e));
    }

    fn resolve_idents(&mut self, code: &mut CstStmt) {
        match &mut code.node {
            StmtP::Def(_name, params, ret, body, scope_id) => self.resolve_idents_in_def(
                *scope_id,
                params,
                ret.as_mut().map(|r| &mut **r),
                Some(body),
                None,
            ),
            _ => code.visit_children_mut(|visit| match visit {
                VisitMut::Stmt(stmt) => self.resolve_idents(stmt),
                VisitMut::Expr(expr) => self.resolve_idents_in_expr(expr),
            }),
        }
    }

    fn resolve_idents_in_assign(&mut self, assign: &mut CstAssign) {
        assign.visit_expr_mut(|expr| self.resolve_idents_in_expr(expr));
    }

    fn resolve_idents_in_def(
        &mut self,
        scope_id: ScopeId,
        params: &mut [CstParameter],
        ret: Option<&mut CstExpr>,
        body_stmt: Option<&mut CstStmt>,
        body_expr: Option<&mut CstExpr>,
    ) {
        for param in params {
            param.visit_expr_mut(|expr| self.resolve_idents_in_expr(expr));
        }
        if let Some(ret) = ret {
            self.resolve_idents_in_expr(ret);
        }

        self.enter_def(scope_id);
        if let Some(body_stmt) = body_stmt {
            self.resolve_idents(body_stmt);
        }
        if let Some(body_expr) = body_expr {
            self.resolve_idents_in_expr(body_expr);
        }
        self.exit_def();
    }

    fn resolve_idents_in_expr(&mut self, expr: &mut CstExpr) {
        match &mut expr.node {
            ExprP::Identifier(ident, slot) => self.resolve_ident(ident, slot),
            ExprP::Lambda(params, body, scope_id) => {
                self.resolve_idents_in_def(*scope_id, params, None, None, Some(body))
            }
            ExprP::ListComprehension(expr, first_for, clauses) => {
                self.resolve_idents_in_compr(&mut [expr], first_for, clauses)
            }
            ExprP::DictComprehension(box (k, v), first_for, clauses) => {
                self.resolve_idents_in_compr(&mut [k, v], first_for, clauses)
            }
            _ => expr.visit_expr_mut(|expr| self.resolve_idents_in_expr(expr)),
        }
    }

    fn resolve_ident(&mut self, ident: &AstString, resolved_ident: &mut Option<ResolvedIdent>) {
        assert!(resolved_ident.is_none());
        *resolved_ident = Some(match self.get_name(ident) {
            None => {
                // Must be a global, since we know all variables
                match self.globals.get_frozen(ident) {
                    None => {
                        let codemap = self.codemap.dupe();
                        let mk_err = move || {
                            Diagnostic::new(
                                EnvironmentError::VariableNotFound(ident.node.clone()),
                                ident.span,
                                codemap.dupe(),
                            )
                        };
                        self.errors.push(mk_err());
                        return;
                    }
                    Some(v) => ResolvedIdent::Global(v),
                }
            }
            Some(slot) => ResolvedIdent::Slot(slot),
        });
    }

    fn resolve_idents_in_compr(
        &mut self,
        exprs: &mut [&mut CstExpr],
        first_for: &mut ForClauseP<CstPayload>,
        clauses: &mut [ClauseP<CstPayload>],
    ) {
        // First for is resolved in outer scope
        self.resolve_idents_in_for_clause(first_for);

        self.enter_compr();

        // Add identifiers to compr scope

        self.add_compr(&mut first_for.var);
        for clause in clauses.iter_mut() {
            match clause {
                ClauseP::For(for_clause) => self.add_compr(&mut for_clause.var),
                ClauseP::If(..) => {}
            }
        }

        // Now resolve idents in compr scope

        for clause in clauses.iter_mut() {
            match clause {
                ClauseP::For(for_clause) => self.resolve_idents_in_for_clause(for_clause),
                ClauseP::If(cond) => self.resolve_idents_in_expr(cond),
            }
        }

        // Finally, resolve the item expression

        for expr in exprs {
            self.resolve_idents_in_expr(expr);
        }

        self.exit_compr();
    }

    fn resolve_idents_in_for_clause(&mut self, for_clause: &mut ForClauseP<CstPayload>) {
        self.resolve_idents_in_expr(&mut for_clause.over);
        self.resolve_idents_in_assign(&mut for_clause.var);
    }

    pub fn enter_def(&mut self, scope_id: ScopeId) {
        self.locals.push(scope_id);
    }

    // Which slots to grab from the current scope to the parent scope, size of your
    // self scope Future state: Should return the slots to use from the parent
    // scope
    pub fn exit_def(&mut self) -> &mut ScopeNames {
        let scope_id = self.locals.pop().unwrap();
        self.scope_data.mut_scope(scope_id)
    }

    fn enter_compr(&mut self) {
        self.unscopes.push(Unscope::default());
    }

    fn add_compr(&mut self, var: &mut CstAssign) {
        let scope_id = self.top_scope_id();
        let mut locals = IndexMap::new();
        Assign::collect_defines_lvalue(var, &mut self.scope_data, &mut locals);
        for (name, binding_id) in locals.into_iter() {
            let slot = self
                .scope_data
                .mut_scope(scope_id)
                .add_scoped(name, self.unscopes.last_mut().unwrap());
            let binding = self.scope_data.mut_binding(binding_id);
            assert!(mem::replace(&mut binding.slot, Some(Slot::Local(slot))).is_none());
        }
    }

    fn exit_compr(&mut self) {
        self.scope_data
            .mut_scope(self.top_scope_id())
            .unscope(self.unscopes.pop().unwrap());
    }

    fn get_name(&mut self, name: &str) -> Option<Slot> {
        // look upwards to find the first place the variable occurs
        // then copy that variable downwards
        for i in (0..self.locals.len()).rev() {
            if let Some(mut v) = self.scope_at_level(i).get_name(name) {
                for j in (i + 1)..self.locals.len() {
                    v = self.scope_at_level_mut(j).copy_parent(v, name);
                }
                return Some(Slot::Local(v));
            }
        }
        self.module
            .get_name(name)
            .map(|(slot, _vis)| Slot::Module(slot))
    }
}

impl Stmt {
    // Collect all the variables that are defined in this scope
    fn collect_defines<'a>(
        stmt: &'a mut CstStmt,
        scope_data: &mut ScopeData,
        result: &mut IndexMap<&'a str, BindingId>,
    ) {
        match &mut stmt.node {
            StmtP::Assign(dest, _) | StmtP::AssignModify(dest, _, _) => {
                Assign::collect_defines_lvalue(dest, scope_data, result);
            }
            StmtP::For(dest, box (_, body)) => {
                Assign::collect_defines_lvalue(dest, scope_data, result);
                StmtP::collect_defines(body, scope_data, result);
            }
            StmtP::Def(name, ..) => {
                AssignIdent::collect_assign_ident(name, Visibility::Public, scope_data, result)
            }
            StmtP::Load(load) => {
                let vis = load.visibility;
                for (name, _) in &mut load.node.args {
                    let mut vis = vis;
                    if Module::default_visibility(&name.0) == Visibility::Private {
                        vis = Visibility::Private;
                    }
                    AssignIdent::collect_assign_ident(name, vis, scope_data, result);
                }
            }
            stmt => stmt.visit_stmt_mut(|x| Stmt::collect_defines(x, scope_data, result)),
        }
    }
}

impl AssignIdent {
    fn collect_assign_ident<'a>(
        assign: &'a mut CstAssignIdent,
        vis: Visibility,
        scope_data: &mut ScopeData,
        result: &mut IndexMap<&'a str, BindingId>,
    ) {
        // Helper function to untangle lifetimes: we read and modify `assign` fields.
        fn assign_ident_impl<'b>(
            name: &'b str,
            binding: &'b mut Option<BindingId>,
            mut vis: Visibility,
            scope_data: &mut ScopeData,
            result: &mut IndexMap<&'b str, BindingId>,
        ) {
            assert!(
                binding.is_none(),
                "binding can be assigned only once: `{}`",
                name
            );
            if vis == Visibility::Public {
                vis = Module::default_visibility(name);
            }
            match result.entry(name) {
                indexmap::map::Entry::Occupied(e) => {
                    let prev_binding_id = *e.get();
                    let prev_binding = scope_data.mut_binding(prev_binding_id);
                    // If we are in the map as Public and Private, then Public wins.
                    // Everything but Load is definitely Public.
                    // So only insert if it wasn't already there.
                    if vis == Visibility::Public {
                        prev_binding.vis = Visibility::Public;
                    }
                    *binding = Some(prev_binding_id);
                }
                indexmap::map::Entry::Vacant(e) => {
                    let (new_binding_id, _) = scope_data.new_binding(vis);
                    e.insert(new_binding_id);
                    *binding = Some(new_binding_id);
                }
            };
        }
        assign_ident_impl(&assign.node.0, &mut assign.node.1, vis, scope_data, result);
    }
}

impl Assign {
    // Collect variables defined in an expression on the LHS of an assignment (or
    // for variable etc)
    fn collect_defines_lvalue<'a>(
        expr: &'a mut CstAssign,
        scope_data: &mut ScopeData,
        result: &mut IndexMap<&'a str, BindingId>,
    ) {
        expr.node.visit_lvalue_mut(|x| {
            AssignIdent::collect_assign_ident(x, Visibility::Public, scope_data, result)
        });
    }
}

/// Storage of objects referenced by AST.
#[derive(Default)]
pub(crate) struct ScopeData {
    bindings: Vec<Binding>,
    scopes: Vec<ScopeNames>,
}

/// Binding defines a place for a variable.
///
/// For example, in code `x = 1; x = 2`, there's one binding for name `x`.
///
/// In code `x = 1; def f(): x = 2`, there are two bindings for name `x`.
#[derive(Debug)]
pub(crate) struct Binding {
    pub(crate) vis: Visibility,
    /// `slot` is `None` when it is not initialized yet.
    /// When analysis is completed, `slot` is always `Some`.
    pub(crate) slot: Option<Slot>,
}

impl Binding {
    fn new(vis: Visibility) -> Binding {
        Binding { vis, slot: None }
    }
}

/// If of a binding within current module.
#[derive(Copy, Clone, Dupe, Debug)]
pub(crate) struct BindingId(usize);

/// Id of a scope within current module.
#[derive(Copy, Clone, Dupe, Debug, Eq, PartialEq)]
pub(crate) struct ScopeId(usize);

impl ScopeId {
    pub(crate) fn module() -> ScopeId {
        ScopeId(0)
    }
}

impl ScopeData {
    pub(crate) fn new() -> ScopeData {
        ScopeData::default()
    }

    pub(crate) fn get_binding(&self, BindingId(id): BindingId) -> &Binding {
        &self.bindings[id]
    }

    fn mut_binding(&mut self, BindingId(id): BindingId) -> &mut Binding {
        &mut self.bindings[id]
    }

    fn new_binding(&mut self, vis: Visibility) -> (BindingId, &mut Binding) {
        let binding_id = BindingId(self.bindings.len());
        self.bindings.push(Binding::new(vis));
        (binding_id, self.bindings.last_mut().unwrap())
    }

    pub(crate) fn get_scope(&self, ScopeId(id): ScopeId) -> &ScopeNames {
        &self.scopes[id]
    }

    pub(crate) fn mut_scope(&mut self, ScopeId(id): ScopeId) -> &mut ScopeNames {
        &mut self.scopes[id]
    }

    pub(crate) fn new_scope(&mut self) -> (ScopeId, &mut ScopeNames) {
        let scope_id = ScopeId(self.scopes.len());
        self.scopes.push(ScopeNames::default());
        (scope_id, self.scopes.last_mut().unwrap())
    }

    /// Get resolved slot for assigning identifier.
    pub(crate) fn get_assign_ident_slot(&self, ident: &CstAssignIdent) -> Slot {
        let binding_id = ident.1.expect("binding not assigned for ident");
        let slot = self.get_binding(binding_id).slot;
        slot.expect("binding slot is not initialized")
    }
}

#[derive(Debug)]
pub(crate) enum ResolvedIdent {
    Slot(Slot),
    Global(FrozenValue),
}

// We use CST as acronym for compiler-specific AST.

/// Compiler-specific AST payload.
#[derive(Debug)]
pub(crate) struct CstPayload;
impl AstPayload for CstPayload {
    /// Information about how identifier binding is resolved.
    ///
    /// This is `None` when CST is created.
    /// All payload objects are filled with binding ids for all assign idents
    /// during analysis.
    ///
    /// When compilation starts, all payloads are `Some`.
    type IdentPayload = Option<ResolvedIdent>;
    /// Binding for an identifier in assignment position.
    ///
    /// This is `None` when CST is created.
    /// All payload objects are filled with binding ids for all assign idents
    /// during analysis.
    ///
    /// When compilation starts, all payloads are `Some`.
    type IdentAssignPayload = Option<BindingId>;
    type DefPayload = ScopeId;
}

pub(crate) struct CompilerAstMap<'a>(pub(crate) &'a mut ScopeData);
impl AstPayloadFunction<AstNoPayload, CstPayload> for CompilerAstMap<'_> {
    fn map_ident(&mut self, (): ()) -> Option<ResolvedIdent> {
        None
    }

    fn map_ident_assign(&mut self, (): ()) -> Option<BindingId> {
        None
    }

    fn map_def(&mut self, (): ()) -> ScopeId {
        self.0.new_scope().0
    }
}

pub(crate) type CstExpr = AstExprP<CstPayload>;
pub(crate) type CstAssign = AstAssignP<CstPayload>;
pub(crate) type CstAssignIdent = AstAssignIdentP<CstPayload>;
pub(crate) type CstArgument = AstArgumentP<CstPayload>;
pub(crate) type CstParameter = AstParameterP<CstPayload>;
pub(crate) type CstStmt = AstStmtP<CstPayload>;
