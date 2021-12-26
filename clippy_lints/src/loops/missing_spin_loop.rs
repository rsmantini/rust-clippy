use super::MISSING_SPIN_LOOP;
use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::is_no_std_crate;
use rustc_errors::Applicability;
use rustc_hir::{Block, Expr, ExprKind};
use rustc_lint::LateContext;
//use rustc_middle::ty;
use rustc_span::sym;

pub(super) fn check<'tcx>(cx: &LateContext<'tcx>, cond: &'tcx Expr<'_>, body: &'tcx Expr<'_>) {
    if_chain! {
        if let ExprKind::Block(Block { stmts: [], expr: None, ..}, _) = body.kind;
        if let ExprKind::MethodCall(method, _, [_callee, _ordering], _) = cond.kind;
        if method.ident.name == sym::load;
        //if let ty::Adt(def, _substs) = cx.typeck_results().expr_ty(callee).kind();
        //if cx.tcx.is_diagnostic_item(sym::AtomicBool, def.did);
        then {
            span_lint_and_sugg(
                cx,
                MISSING_SPIN_LOOP,
                body.span,
                "busy-waiting loop should at least have a spin loop hint",
                "try this",
                (if is_no_std_crate(cx) {
                    "{ core::hint::spin_loop() }"
                }else {
                    "{ std::hint::spin_loop() }"
                }).into(),
                Applicability::MachineApplicable
            );
        }
    }
}
