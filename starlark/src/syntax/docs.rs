use crate::docs::DocFunction;
use crate::docs::DocParam;
use crate::docs::DocProperty;
use crate::docs::DocString;
use crate::docs::DocStringKind;
use crate::syntax::ast::AstAssignP;
use crate::syntax::ast::AstLiteral;
use crate::syntax::ast::AstPayload;
use crate::syntax::ast::AstStmtP;
use crate::syntax::ast::DefP;
use crate::syntax::ast::ExprP;
use crate::syntax::ast::ParameterP;
use crate::syntax::ast::StmtP;

/// Given the AST node for a `def` statement, return a `DocFunction` if the
/// `def` statement has a docstring as its first statement.
pub(crate) fn get_doc_item_for_def<P: AstPayload>(def: &DefP<P>) -> Option<DocFunction> {
    if let Some(doc_string) = peek_docstring(&def.body) {
        let args: Vec<_> = def
            .params
            .iter()
            .filter_map(|param| match &param.node {
                ParameterP::Normal(p, _)
                | ParameterP::WithDefaultValue(p, _, _)
                | ParameterP::Args(p, _)
                | ParameterP::KwArgs(p, _) => Some(DocParam::Arg {
                    name: p.0.to_owned(),
                    docs: None,
                    typ: None,
                    default_value: None,
                }),
                _ => None,
            })
            .collect();

        let doc_function = DocFunction::from_docstring(
            DocStringKind::Starlark,
            args,
            // TODO: Figure out how to get a `Ty` from the `def.return_type`.
            None,
            Some(doc_string),
            None,
        );
        Some(doc_function)
    } else {
        None
    }
}

pub(crate) fn get_doc_item_for_assign<P: AstPayload>(
    previous_node: &AstStmtP<P>,
    _assign: &AstAssignP<P>,
) -> Option<DocProperty> {
    peek_docstring(previous_node).map(|doc_string| {
        DocProperty {
            docs: DocString::from_docstring(DocStringKind::Starlark, doc_string),
            // TODO: Can constants have a type?
            typ: None,
        }
    })
}

fn peek_docstring<P: AstPayload>(stmt: &AstStmtP<P>) -> Option<&str> {
    match &stmt.node {
        StmtP::Statements(stmts) => stmts.first().and_then(peek_docstring),
        StmtP::Expression(expr) => match &expr.node {
            ExprP::Literal(AstLiteral::String(s)) => Some(s.node.as_str()),
            _ => None,
        },
        _ => None,
    }
}
