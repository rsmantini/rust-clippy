use clippy_utils::diagnostics;
use rustc_data_structures::fx::FxHashMap;
use rustc_errors::Applicability;
use rustc_hir::{intravisit::FnKind, Body, FnDecl, HirId};
use rustc_index::bit_set::HybridBitSet;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::{
    mir::{
        self,
        visit::{PlaceContext, Visitor as MirVisitor},
        BasicBlock, Local, Location, Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty,
};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::{sym, Span};

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.60.0"]
    pub ITER_INSTEAD_OF_INTO_ITER,
    style,
    "default lint description"
}
declare_lint_pass!(IterInsteadOfIntoIter => [ITER_INSTEAD_OF_INTO_ITER]);

impl<'tcx> LateLintPass<'tcx> for IterInsteadOfIntoIter {
    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: FnKind<'tcx>,
        _: &'tcx FnDecl<'_>,
        body: &'tcx Body<'_>,
        _: Span,
        _: HirId,
    ) {
        let def_id = cx.tcx.hir().body_owner_def_id(body.id());

        if clippy_utils::fn_has_unsatisfiable_preds(cx, def_id.to_def_id()) {
            return;
        }

        let mir = cx.tcx.optimized_mir(def_id.to_def_id());

        let mut iter_visitor = IterCallVisitor {
            mir,
            cx,
            calls: Vec::new(),
        };
        iter_visitor.visit_body(mir);
        let mut calls = iter_visitor.calls;

        if calls.is_empty() {
            return;
        }

        let mut relation_visitor = TransitiveRelationVisitor::new(mir.local_decls.len());
        relation_visitor.visit_body(mir);
        let relations = relation_visitor.relations;

        for iter_call in &mut calls {
            iter_call.collection = find_valid_collections(cx, mir, iter_call.local, &relations);
        }

        calls.retain(|x| x.collection.is_some());

        let collections: FxHashMap<_, _> = calls
            .iter()
            .filter_map(|c| Some((c.collection?, relations.reachable_from(c.collection?))))
            .collect();

        let mut used_after_call_visitor = UseAfterCallVisitor {
            calls,
            collections,
            relations,
        };

        used_after_call_visitor.visit_body(mir);

        for call in used_after_call_visitor
            .calls
            .iter()
            .filter(|x| !x.collection_used_after_call)
        {
            let span = mir.basic_blocks()[call.location.block].terminator().source_info.span;
            diagnostics::span_lint_and_sugg(
                cx,
                ITER_INSTEAD_OF_INTO_ITER,
                span,
                &format!(
                    "this `.iter()` call can be replaced with `.into_iter()` as the container is not used afterwards",
                ),
                "replace `iter()` with",
                "into_iter()".to_string(),
                Applicability::MachineApplicable,
            );
        }

        // dbg!("Relations:", re_vistor.relations);
        // println!("MIR:");
        // println!();
        // dbg!(&mir);
    }
}

#[derive(Debug)]
struct IterCall {
    local: Local,
    location: Location,
    dest: Local,
    collection_used_after_call: bool,
    collection: Option<Local>,
}

impl IterCall {
    fn new(local: Local, location: Location, dest: Local) -> IterCall {
        IterCall {
            local,
            location,
            dest,
            collection_used_after_call: false,
            collection: None,
        }
    }
}

struct IterCallVisitor<'a, 'tcx> {
    mir: &'a rustc_middle::mir::Body<'tcx>,
    cx: &'a LateContext<'tcx>,
    calls: Vec<IterCall>,
}

// collect info for all calls of the kind ```foo.iter()```
impl<'a, 'txc> MirVisitor<'txc> for IterCallVisitor<'a, 'txc> {
    fn visit_terminator(&mut self, term: &Terminator<'txc>, loc: Location) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        {
            let ty = func.ty(self.mir, self.cx.tcx);
            if let ty::FnDef(def_id, _) = ty.kind() {
                let defpath = self.cx.tcx.def_path(*def_id);
                let name = defpath.data.last().unwrap().data.get_opt_name();
                if let Some(sym::iter) = name {
                    // Could it be something else than a move?
                    if let Operand::Move(place) = args[0] {
                        if !is_inside_loop(self.mir, term, loc) {
                            self.calls.push(IterCall::new(place.local, loc, destination.local));
                        }
                    }
                }
            }
        }
    }
}

fn is_inside_loop<'tcx>(mir: &mir::Body<'tcx>, term: &mir::Terminator<'tcx>, loc: Location) -> bool {
    let mut seen = HybridBitSet::new_empty(mir.basic_blocks().len());
    let mut stack: Vec<BasicBlock> = term.successors().map(|bb| bb).collect();
    while let Some(bb) = stack.pop() {
        if bb == loc.block {
            return true;
        }
        if seen.insert(bb.index()) {
            if let Some(next_term) = &mir.basic_blocks()[bb].terminator {
                for successor in next_term.successors() {
                    stack.push(successor);
                }
            }
        }
    }
    false
}

fn find_valid_collections<'tcx>(
    cx: &LateContext<'tcx>,
    mir: &mir::Body<'tcx>,
    local: Local,
    relations: &TransitiveRelations,
) -> Option<Local> {
    let mut node = local;
    while let Some(parents) = relations.backward.get(&node) {
        // Give up on nodes with more than one parent
        if parents.len() != 1 {
            break;
        }
        node = *parents.first().unwrap();
        // use local info as proxy for a user defined local
        if let Some(_) = mir.local_decls[node].local_info {
            let ty = mir.local_decls[node].ty;
            // only interest in owned origins
            if let ty::Ref(..) = ty.kind() {
                break;
            }
            // only consider owned types that have a valid iter method
            if clippy_utils::ty::has_iter_method(cx, ty).is_none() {
                break;
            }
            return Some(node);
        }
    }
    None
}

struct TransitiveRelationVisitor {
    relations: TransitiveRelations,
}

impl TransitiveRelationVisitor {
    fn new(domain_size: usize) -> TransitiveRelationVisitor {
        TransitiveRelationVisitor {
            relations: TransitiveRelations::new(domain_size),
        }
    }
}

impl TransitiveRelationVisitor {
    fn process_local(&mut self, lhs: Local, rhs: Local, _: Location) {
        self.relations.add(rhs, lhs);
    }
    fn process_operand<'tcx>(&mut self, lhs: Local, oper: &Operand<'tcx>, location: Location) {
        match oper {
            Operand::Copy(place) | Operand::Move(place) => self.process_local(lhs, place.local, location),
            Operand::Constant(..) => (),
        }
    }
}

impl<'txc> MirVisitor<'txc> for TransitiveRelationVisitor {
    fn visit_assign(&mut self, place: &Place<'txc>, rvalue: &Rvalue<'txc>, location: Location) {
        let lhs = place.local;
        match rvalue {
            Rvalue::Ref(_, _, place) => self.process_local(lhs, place.local, location),
            Rvalue::Cast(_, oper, _) => self.process_operand(lhs, oper, location),
            Rvalue::BinaryOp(_, box (a, b)) => {
                self.process_operand(lhs, a, location);
                self.process_operand(lhs, b, location);
            },
            Rvalue::UnaryOp(_, oper) => self.process_operand(lhs, oper, location),
            Rvalue::Aggregate(_, opers) => {
                for oper in opers {
                    self.process_operand(lhs, oper, location)
                }
            },
            Rvalue::Use(oper) => self.process_operand(lhs, oper, location),
            _ => (),
        }
    }

    fn visit_terminator(&mut self, term: &Terminator<'txc>, location: Location) {
        if let TerminatorKind::Call { args, destination, .. } = &term.kind {
            for arg in args {
                self.process_operand(destination.local, arg, location);
            }
        }
    }
}
struct UseAfterCallVisitor {
    calls: Vec<IterCall>,
    collections: FxHashMap<Local, HybridBitSet<Local>>,
    relations: TransitiveRelations,
}

impl<'tcx> MirVisitor<'tcx> for UseAfterCallVisitor {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, location: Location) {
        for call in self.calls.iter_mut().filter(|x| !x.collection_used_after_call) {
            if location > call.location {
                let origin_refs = self.collections.get(&call.collection.unwrap()).unwrap();
                // Do not count usages of the iterator itself ie: iter.next()
                if place.local != call.dest
                    && origin_refs.contains(place.local)
                    && !self.relations.is_descendant(call.dest, place.local)
                {
                    call.collection_used_after_call = true;
                }
            }
        }
    }

    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        if let StatementKind::StorageLive(_) | StatementKind::StorageDead(_) = stmt.kind {
            return;
        }
        self.super_statement(stmt, location);
    }

    fn visit_terminator(&mut self, term: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Drop { .. } = term.kind {
            return;
        }
        self.super_terminator(term, location);
    }
}

#[derive(Debug)]
struct TransitiveRelations {
    forward: FxHashMap<Local, Vec<Local>>,
    backward: FxHashMap<Local, Vec<Local>>,
    domain_size: usize,
}

impl TransitiveRelations {
    fn new(domain_size: usize) -> TransitiveRelations {
        TransitiveRelations {
            forward: FxHashMap::default(),
            backward: FxHashMap::default(),
            domain_size,
        }
    }
}

impl TransitiveRelations {
    fn add(&mut self, a: Local, b: Local) {
        self.forward.entry(a).or_default().push(b);
        self.backward.entry(b).or_default().push(a);
    }

    fn reachable_from(&self, node: Local) -> HybridBitSet<Local> {
        let mut seen = HybridBitSet::new_empty(self.domain_size);
        let mut stack = vec![node];
        while let Some(u) = stack.pop() {
            if let Some(edges) = self.forward.get(&u) {
                for &e in edges {
                    if seen.insert(e) {
                        stack.push(e);
                    }
                }
            }
        }
        seen
    }

    fn is_descendant(&self, parent: Local, node: Local) -> bool {
        let mut seen = HybridBitSet::new_empty(self.domain_size);
        let mut stack = vec![parent];
        while let Some(u) = stack.pop() {
            if let Some(edges) = self.forward.get(&u) {
                for &e in edges {
                    if e == node {
                        return true;
                    }
                    if seen.insert(e) {
                        stack.push(e);
                    }
                }
            }
        }
        false
    }
}
