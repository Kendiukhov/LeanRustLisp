use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use cli::set_prelude_macro_boundary_allowlist;
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::ast::Term;
use kernel::checker::{Builtin, Env};
use mir::codegen::{
    codegen_body, codegen_constant, codegen_prelude, codegen_recursors, sanitize_name,
};
use mir::typed_codegen::{codegen_program, TypedBody, TypedProgram};
use mir::types::{AdtId, CtorId, IdRegistry, MirType};
use mir::Literal;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Clone)]
struct LoweredDef {
    name: String,
    body: mir::Body,
    derived_bodies: Vec<mir::Body>,
}

fn lower_program(
    source: &str,
    load_prelude: bool,
    check_closure_bodies: bool,
) -> (Env, IdRegistry, Vec<LoweredDef>, Option<String>) {
    let prelude = if load_prelude {
        Some("stdlib/prelude.lrl")
    } else {
        None
    };
    lower_program_with_prelude(source, prelude, check_closure_bodies)
}

fn lower_program_with_prelude(
    source: &str,
    prelude_source_path: Option<&str>,
    check_closure_bodies: bool,
) -> (Env, IdRegistry, Vec<LoweredDef>, Option<String>) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    env.set_allow_reserved_primitives(true);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    if let Some(prelude_source_path) = prelude_source_path {
        let mut prelude_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(prelude_source_path);
        if !prelude_path.exists() {
            prelude_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join(prelude_source_path);
        }
        let prelude = fs::read_to_string(&prelude_path)
            .unwrap_or_else(|e| panic!("failed to read prelude {:?}: {}", prelude_path, e));
        let prelude_module = module_id_for_source(prelude_source_path);
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        let mut prelude_diagnostics = DiagnosticCollector::new();
        let allow_reserved = env.allows_reserved_primitives();
        env.set_allow_reserved_primitives(true);
        process_code(
            &prelude,
            "prelude",
            &mut env,
            &mut expander,
            &PipelineOptions::default(),
            &mut prelude_diagnostics,
        )
        .expect("prelude processing failed");
        expander.clear_macro_boundary_allowlist();
        env.set_allow_reserved_primitives(allow_reserved);
        if let Err(err) = env.init_marker_registry() {
            panic!("Failed to initialize marker registry: {}", err);
        }
        expander.set_default_imports(vec![prelude_module]);
        assert!(
            !prelude_diagnostics.has_errors(),
            "prelude diagnostics contained errors"
        );
    }

    let result = process_code(
        source,
        "typed_backend_test",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .expect("process_code failed");

    assert!(
        !diagnostics.has_errors(),
        "diagnostics contained errors: {:?}",
        diagnostics.diagnostics
    );

    let ids = IdRegistry::from_env(&env);
    let mut names: Vec<_> = env.definitions().keys().cloned().collect();
    names.sort();

    let mut lowered_defs = Vec::new();
    for name in names {
        let def = env.definitions().get(&name).expect("missing def");
        if let Some(val) = &def.value {
            if matches!(&**val, Term::Ctor(_, _, _)) {
                continue;
            }
        } else {
            continue;
        }

        let mut ctx = mir::lower::LoweringContext::new_with_metadata(
            vec![],
            def.ty.clone(),
            &env,
            &ids,
            None,
            Some(name.clone()),
            Some(Rc::new(def.capture_modes.clone())),
        )
        .unwrap_or_else(|e| panic!("lowering context init error in {}: {}", name, e));
        let dest = mir::Place::from(mir::Local(0));
        let target = mir::BasicBlock(1);
        ctx.body.basic_blocks.push(mir::BasicBlockData {
            statements: vec![],
            terminator: Some(mir::Terminator::Return),
        });

        if let Some(val) = &def.value {
            ctx.lower_term(val, dest, target)
                .unwrap_or_else(|e| panic!("lowering error in {}: {}", name, e));
        }

        mir::transform::storage::insert_exit_storage_deads(&mut ctx.body);

        let mut typing = mir::analysis::typing::TypingChecker::new(&ctx.body);
        typing.check();
        assert!(
            typing.errors().is_empty(),
            "typing errors in {}: {:?}",
            name,
            typing.errors()
        );

        let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(&ctx.body);
        ownership.analyze();
        let ownership_errors = ownership.check();
        assert!(
            ownership_errors.is_empty(),
            "ownership errors in {}: {:?}",
            name,
            ownership_errors
        );

        let mut nll = mir::analysis::nll::NllChecker::new(&ctx.body);
        nll.check();
        let nll_result = nll.into_result();
        assert!(
            nll_result.errors.is_empty(),
            "borrow errors in {}: {:?}",
            name,
            nll_result.errors
        );
        if nll_result.is_ok() {
            nll_result.inject_runtime_checks(&mut ctx.body);
        }

        if check_closure_bodies {
            for (i, body) in ctx.derived_bodies.borrow_mut().iter_mut().enumerate() {
                mir::transform::storage::insert_exit_storage_deads(body);

                let mut typing = mir::analysis::typing::TypingChecker::new(body);
                typing.check();
                assert!(
                    typing.errors().is_empty(),
                    "typing errors in {} closure {}: {:?}",
                    name,
                    i,
                    typing.errors()
                );

                let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
                ownership.analyze();
                let ownership_errors = ownership.check();
                assert!(
                    ownership_errors.is_empty(),
                    "ownership errors in {} closure {}: {:?}",
                    name,
                    i,
                    ownership_errors
                );

                let mut nll = mir::analysis::nll::NllChecker::new(body);
                nll.check();
                let nll_result = nll.into_result();
                assert!(
                    nll_result.errors.is_empty(),
                    "borrow errors in {} closure {}: {:?}",
                    name,
                    i,
                    nll_result.errors
                );
                if nll_result.is_ok() {
                    nll_result.inject_runtime_checks(body);
                }
            }
        }

        mir::transform::erasure::erase_proofs(&mut ctx.body);
        for body in ctx.derived_bodies.borrow_mut().iter_mut() {
            mir::transform::erasure::erase_proofs(body);
        }
        mir::transform::dce::eliminate_dead_code(&mut ctx.body);
        for body in ctx.derived_bodies.borrow_mut().iter_mut() {
            mir::transform::dce::eliminate_dead_code(body);
        }
        mir::transform::dce::simplify_cfg(&mut ctx.body);
        for body in ctx.derived_bodies.borrow_mut().iter_mut() {
            mir::transform::dce::simplify_cfg(body);
        }
        mir::transform::inline::optimize(&mut ctx.body);
        for body in ctx.derived_bodies.borrow_mut().iter_mut() {
            mir::transform::inline::optimize(body);
        }

        let safe_name = sanitize_name(&name);
        lowered_defs.push(LoweredDef {
            name: safe_name,
            body: ctx.body,
            derived_bodies: ctx.derived_bodies.borrow().clone(),
        });
    }

    let main_name = result
        .deployed_definitions
        .last()
        .map(|name| sanitize_name(name));

    (env, ids, lowered_defs, main_name)
}

fn build_typed_program(defs: &[LoweredDef], main_name: Option<String>) -> TypedProgram {
    let mut typed_defs = Vec::new();
    let mut typed_closures = Vec::new();
    let mut closure_base = 0usize;

    for def in defs {
        typed_defs.push(TypedBody {
            name: def.name.clone(),
            body: def.body.clone(),
            closure_base,
        });
        for (idx, body) in def.derived_bodies.iter().enumerate() {
            typed_closures.push(TypedBody {
                name: format!("closure_{}", closure_base + idx),
                body: body.clone(),
                closure_base,
            });
        }
        closure_base += def.derived_bodies.len();
    }

    TypedProgram {
        defs: typed_defs,
        closures: typed_closures,
        main_name,
    }
}

fn build_dynamic_code(
    env: &Env,
    ids: &IdRegistry,
    defs: &[LoweredDef],
    main_name: Option<String>,
) -> String {
    let mut code = String::new();
    code.push_str("#![allow(dead_code, unused_variables, unused_parens, unreachable_patterns)]\n");
    code.push_str(&codegen_prelude());
    code.push('\n');

    let mut ind_names: Vec<_> = env.inductives.keys().cloned().collect();
    ind_names.sort();
    for name in ind_names {
        if let Some(decl) = env.inductives.get(&name) {
            for (i, ctor) in decl.ctors.iter().enumerate() {
                let safe_ctor_name = sanitize_name(&ctor.name);
                let mut arity = 0;
                let mut ty = &ctor.ty;
                while let Term::Pi(_, body, _, _) = &**ty {
                    arity += 1;
                    ty = body;
                }
                let ctor_id = ids
                    .ctor_id(&name, i)
                    .unwrap_or_else(|| CtorId::new(AdtId::new(&name), i));
                let ctor_val_code = codegen_constant(&Literal::InductiveCtor(ctor_id, arity), 0);
                code.push_str(&format!(
                    "fn {}() -> Value {{ {} }}\n",
                    safe_ctor_name, ctor_val_code
                ));
            }
        }
    }

    let mut closure_idx = 0usize;
    for def in defs {
        let closure_base = closure_idx;
        for (i, body) in def.derived_bodies.iter().enumerate() {
            let closure_name = format!("closure_{}", closure_base + i);
            code.push_str(&codegen_body(&closure_name, body, closure_base));
            code.push('\n');
        }

        code.push_str(&codegen_body(&def.name, &def.body, closure_base));
        code.push('\n');

        closure_idx += def.derived_bodies.len();
    }

    code.push_str(&codegen_recursors(&env.inductives, env));

    code.push_str("fn main() {\n");
    if let Some(name) = main_name {
        code.push_str(&format!("    let result = {}();\n", name));
        code.push_str("    println!(\"Result: {:?}\", result);\n");
    }
    code.push_str("}\n");

    code
}

fn extract_result_value(output: &str) -> Option<&str> {
    output
        .lines()
        .find_map(|line| line.strip_prefix("Result: "))
        .map(str::trim)
}

fn extract_nat_result(output: &str) -> Option<u64> {
    let value = extract_result_value(output)?;
    if let Some(rest) = value.strip_prefix("Nat(").and_then(|s| s.strip_suffix(')')) {
        rest.parse().ok()
    } else {
        value.parse().ok()
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root")
}

#[derive(Clone, Copy)]
enum ScalarResultKind {
    Nat,
}

fn assert_scalar_result_parity(
    case_name: &str,
    kind: ScalarResultKind,
    typed_output: &str,
    dynamic_output: &str,
) {
    match kind {
        ScalarResultKind::Nat => {
            let typed = extract_nat_result(typed_output);
            let dynamic = extract_nat_result(dynamic_output);
            assert!(
                typed.is_some() && dynamic.is_some(),
                "expected nat result for {}. typed output:\n{}\ndynamic output:\n{}",
                case_name,
                typed_output,
                dynamic_output
            );
            assert_eq!(
                typed, dynamic,
                "typed/dynamic nat result mismatch for {}. typed output:\n{}\ndynamic output:\n{}",
                case_name, typed_output, dynamic_output
            );
        }
    }
}

fn collect_round5_sources() -> Vec<(String, String)> {
    let root = repo_root().join("code_examples/typed_validation_round5");
    let entries =
        fs::read_dir(&root).unwrap_or_else(|e| panic!("failed to read {:?}: {}", root, e));

    let mut paths: Vec<_> = entries
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().and_then(|s| s.to_str()) == Some("lrl"))
        .filter(|path| {
            path.file_name()
                .and_then(|s| s.to_str())
                .map(|name| !name.starts_with("._"))
                .unwrap_or(false)
        })
        .collect();
    paths.sort();

    paths
        .into_iter()
        .map(|path| {
            let name = path
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("<unknown>")
                .to_string();
            let source = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("failed to read {:?}: {}", path, e));
            (name, source)
        })
        .collect()
}

fn collect_lrl_sources_recursively(root: &Path) -> Vec<(String, String)> {
    let mut dirs = vec![root.to_path_buf()];
    let mut paths: Vec<PathBuf> = Vec::new();

    while let Some(dir) = dirs.pop() {
        let entries =
            fs::read_dir(&dir).unwrap_or_else(|e| panic!("failed to read {:?}: {}", dir, e));
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.is_dir() {
                dirs.push(path);
                continue;
            }
            if path.extension().and_then(|s| s.to_str()) != Some("lrl") {
                continue;
            }
            let Some(name) = path.file_name().and_then(|s| s.to_str()) else {
                continue;
            };
            if name.starts_with("._") {
                continue;
            }
            paths.push(path);
        }
    }

    paths.sort();
    let repo = repo_root();
    paths
        .into_iter()
        .map(|path| {
            let label = path
                .strip_prefix(&repo)
                .unwrap_or(&path)
                .display()
                .to_string();
            let source = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("failed to read {:?}: {}", path, e));
            (label, source)
        })
        .collect()
}

fn is_unary_fn_type(ty: &MirType) -> bool {
    matches!(
        ty,
        MirType::Fn(_, _, args, _) | MirType::FnItem(_, _, _, args, _) | MirType::Closure(_, _, _, args, _)
            if args.len() == 1
    )
}

fn is_fn_type(ty: &MirType) -> bool {
    matches!(
        ty,
        MirType::Fn(_, _, _, _) | MirType::FnItem(_, _, _, _, _) | MirType::Closure(_, _, _, _, _)
    )
}

fn field_type_without_downcast(
    body: &mir::Body,
    adt_id: &AdtId,
    field_idx: usize,
    args: &[MirType],
) -> Option<MirType> {
    let layout = body.adt_layouts.get(adt_id)?;
    let mut field_ty: Option<MirType> = None;
    for variant in &layout.variants {
        if let Some(ty_template) = variant.fields.get(field_idx) {
            let ty = ty_template.substitute_params(args);
            if let Some(existing) = &field_ty {
                if existing != &ty {
                    return None;
                }
            } else {
                field_ty = Some(ty);
            }
        }
    }
    field_ty
}

fn index_item_type_from_field_shallow(ids: &IdRegistry, field_ty: &MirType) -> Option<MirType> {
    let MirType::Adt(field_adt, field_args) = field_ty else {
        return None;
    };
    let list_builtin = ids.builtin_adt(Builtin::List);
    if list_builtin.as_ref().is_some_and(|id| id == field_adt) {
        return field_args.first().cloned();
    }
    if ids.is_indexable_adt(field_adt) {
        return field_args.first().cloned();
    }
    None
}

fn infer_monomorphic_index_item_type(
    ids: &IdRegistry,
    body: &mir::Body,
    adt_id: &AdtId,
) -> Option<MirType> {
    let layout = body.adt_layouts.get(adt_id)?;
    let mut candidate: Option<MirType> = None;
    for variant in &layout.variants {
        for field_ty in &variant.fields {
            let mut field_candidate = index_item_type_from_field_shallow(ids, field_ty);
            if field_candidate.is_none() && variant.fields.len() == 1 {
                field_candidate = Some(field_ty.clone());
            }
            if let Some(item_ty) = field_candidate {
                if let Some(existing) = &candidate {
                    if existing != &item_ty {
                        return None;
                    }
                } else {
                    candidate = Some(item_ty);
                }
            }
        }
    }
    candidate
}

fn index_item_type_for_container(
    ids: &IdRegistry,
    body: &mir::Body,
    ty: &MirType,
) -> Option<MirType> {
    let MirType::Adt(adt_id, args) = ty else {
        return None;
    };
    let list_builtin = ids.builtin_adt(Builtin::List);
    if list_builtin.as_ref().is_some_and(|id| id == adt_id) {
        return args.first().cloned();
    }
    if !ids.is_indexable_adt(adt_id) {
        return None;
    }
    if let Some(first) = args.first() {
        return Some(first.clone());
    }
    infer_monomorphic_index_item_type(ids, body, adt_id)
}

fn project_type_from(
    body: &mir::Body,
    ids: &IdRegistry,
    mut current_ty: MirType,
    projections: &[mir::PlaceElem],
) -> Option<MirType> {
    let mut variant = None;
    for proj in projections {
        match proj {
            mir::PlaceElem::Downcast(idx) => variant = Some(*idx),
            mir::PlaceElem::Field(field_idx) => {
                if matches!(current_ty, MirType::Nat) {
                    if variant == Some(1) && *field_idx == 0 {
                        current_ty = MirType::Nat;
                        variant = None;
                        continue;
                    }
                    return None;
                }
                current_ty = match &current_ty {
                    MirType::Adt(adt_id, args) => body
                        .adt_layouts
                        .field_type(adt_id, variant, *field_idx, args)
                        .or_else(|| field_type_without_downcast(body, adt_id, *field_idx, args))?,
                    _ => return None,
                };
                variant = None;
            }
            mir::PlaceElem::Deref => {
                current_ty = match current_ty {
                    MirType::Ref(_, inner, _) | MirType::RawPtr(inner, _) => *inner,
                    _ => return None,
                };
                variant = None;
            }
            mir::PlaceElem::Index(_) => {
                current_ty = index_item_type_for_container(ids, body, &current_ty)?;
                variant = None;
            }
        }
    }
    Some(current_ty)
}

fn typed_place_type_for_body(
    body: &mir::Body,
    ids: &IdRegistry,
    place: &mir::Place,
) -> Option<MirType> {
    if body.arg_count == 2 && body.local_decls.len() >= 3 && place.local.index() == 1 {
        if place.projection.is_empty() {
            return body.local_decls.get(1).map(|decl| decl.ty.clone());
        }
        let mir::PlaceElem::Field(capture_idx) = place.projection[0] else {
            return None;
        };
        let captures = &body.local_decls.get(1)?.closure_captures;
        let capture_ty = captures.get(capture_idx)?.clone();
        return project_type_from(body, ids, capture_ty, &place.projection[1..]);
    }

    let base_ty = body.local_decls.get(place.local.index())?.ty.clone();
    project_type_from(body, ids, base_ty, &place.projection)
}

fn assert_constant_guard_invariants(constant: &mir::Constant, context: &str) {
    match &constant.literal {
        Literal::Closure(_, _) => {
            assert!(
                is_unary_fn_type(&constant.ty),
                "{}: closure literal must carry unary function type (TB007/TB002 invariant), got {:?}",
                context,
                constant.ty
            );
        }
        Literal::Fix(_, _) => {
            assert!(
                is_unary_fn_type(&constant.ty),
                "{}: fix literal must carry unary function type (TB008/TB002 invariant), got {:?}",
                context,
                constant.ty
            );
        }
        _ => {}
    }
}

fn assert_place_guard_invariants(
    body: &mir::Body,
    ids: &IdRegistry,
    place: &mir::Place,
    context: &str,
) {
    assert!(
        typed_place_type_for_body(body, ids, place).is_some(),
        "{}: place must be lowerable by typed backend (TB005/TB006 invariant), got {:?}",
        context,
        place
    );
}

fn assert_operand_guard_invariants(
    body: &mir::Body,
    ids: &IdRegistry,
    op: &mir::Operand,
    context: &str,
) {
    match op {
        mir::Operand::Copy(place) | mir::Operand::Move(place) => {
            assert_place_guard_invariants(body, ids, place, context);
        }
        mir::Operand::Constant(constant) => {
            assert_constant_guard_invariants(constant, context);
        }
    }
}

fn assert_call_operand_guard_invariants(
    body: &mir::Body,
    ids: &IdRegistry,
    call_op: &mir::CallOperand,
    context: &str,
) {
    match call_op {
        mir::CallOperand::Operand(op) => assert_operand_guard_invariants(body, ids, op, context),
        mir::CallOperand::Borrow(_, place) => {
            assert_place_guard_invariants(body, ids, place, context);
            let ty = typed_place_type_for_body(body, ids, place)
                .expect("borrow call operand place type should exist after place invariant");
            assert!(
                is_fn_type(&ty),
                "{}: borrowed call operand must be function typed (TB003 invariant), got {:?}",
                context,
                ty
            );
        }
    }
}

fn assert_rvalue_guard_invariants(
    body: &mir::Body,
    ids: &IdRegistry,
    rv: &mir::Rvalue,
    context: &str,
) {
    match rv {
        mir::Rvalue::Use(op) => assert_operand_guard_invariants(body, ids, op, context),
        mir::Rvalue::Discriminant(place) | mir::Rvalue::Ref(_, place) => {
            assert_place_guard_invariants(body, ids, place, context);
        }
    }
}

fn assert_body_guard_invariants(body: &mir::Body, ids: &IdRegistry, body_label: &str) {
    for (local_idx, decl) in body.local_decls.iter().enumerate() {
        if is_fn_type(&decl.ty) {
            assert!(
                is_unary_fn_type(&decl.ty),
                "{} local _{} must be unary function typed (TB002 invariant), got {:?}",
                body_label,
                local_idx,
                decl.ty
            );
        }
        for (capture_idx, cap_ty) in decl.closure_captures.iter().enumerate() {
            if is_fn_type(cap_ty) {
                assert!(
                    is_unary_fn_type(cap_ty),
                    "{} local _{} capture[{}] must be unary function typed (TB002 invariant), got {:?}",
                    body_label,
                    local_idx,
                    capture_idx,
                    cap_ty
                );
            }
        }
    }

    for (bb_idx, block) in body.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            let context = format!("{} block {} stmt {}", body_label, bb_idx, stmt_idx);
            match stmt {
                mir::Statement::Assign(place, rv) => {
                    assert!(
                        place.projection.is_empty(),
                        "{}: assignment destination must be local-only (TB004 invariant), got {:?}",
                        context,
                        place
                    );
                    assert_place_guard_invariants(body, ids, place, &context);
                    assert_rvalue_guard_invariants(body, ids, rv, &context);
                }
                mir::Statement::RuntimeCheck(check) => match check {
                    mir::RuntimeCheckKind::RefCellBorrow { local }
                    | mir::RuntimeCheckKind::MutexLock { local } => {
                        assert!(
                            body.local_decls.get(local.index()).is_some(),
                            "{}: runtime-check local must exist",
                            context
                        );
                    }
                    mir::RuntimeCheckKind::BoundsCheck { local, index } => {
                        assert!(
                            body.local_decls.get(local.index()).is_some()
                                && body.local_decls.get(index.index()).is_some(),
                            "{}: bounds-check locals must exist",
                            context
                        );
                    }
                },
                mir::Statement::StorageLive(local) | mir::Statement::StorageDead(local) => {
                    assert!(
                        body.local_decls.get(local.index()).is_some(),
                        "{}: storage marker local must exist",
                        context
                    );
                }
                mir::Statement::Nop => {}
            }
        }

        if let Some(term) = &block.terminator {
            let context = format!("{} block {} term", body_label, bb_idx);
            match term {
                mir::Terminator::Return
                | mir::Terminator::Goto { .. }
                | mir::Terminator::Unreachable => {}
                mir::Terminator::SwitchInt { discr, .. } => {
                    assert_operand_guard_invariants(body, ids, discr, &context);
                }
                mir::Terminator::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    assert_call_operand_guard_invariants(body, ids, func, &context);
                    for arg in args {
                        assert_operand_guard_invariants(body, ids, arg, &context);
                    }
                    assert_place_guard_invariants(body, ids, destination, &context);
                }
            }
        }
    }
}

fn assert_program_guard_invariants(program: &TypedProgram, ids: &IdRegistry, case_label: &str) {
    for body in &program.defs {
        let label = format!("{}::def::{}", case_label, body.name);
        assert_body_guard_invariants(&body.body, ids, &label);
    }
    for body in &program.closures {
        let label = format!("{}::closure::{}", case_label, body.name);
        assert_body_guard_invariants(&body.body, ids, &label);
    }
}

fn generated_nat_chain_source(depth: usize) -> String {
    let mut nat_expr = "zero".to_string();
    for _ in 0..depth {
        nat_expr = format!("(succ {})", nat_expr);
    }

    format!(
        "(def entry Nat
  (print_nat {}))",
        nat_expr
    )
}

fn compile_rust_to_temp_bin(code: &str) -> PathBuf {
    compile_rust_to_temp_bin_with_args(code, &[])
}

fn compile_rust_to_temp_bin_with_args(code: &str, extra_args: &[&str]) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time went backwards")
        .as_nanos();
    let temp_dir = std::env::temp_dir().join(format!(
        "lrl_typed_backend_{}_{}",
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&temp_dir).expect("failed to create temp dir");
    let src_path = temp_dir.join("main.rs");
    let bin_path = temp_dir.join("main_bin");

    fs::write(&src_path, code).expect("failed to write rust source");
    let mut cmd = Command::new("rustc");
    cmd.arg(&src_path);
    for arg in extra_args {
        cmd.arg(arg);
    }
    let status = cmd
        .arg("-O")
        .arg("-o")
        .arg(&bin_path)
        .status()
        .expect("failed to invoke rustc");
    assert!(status.success(), "rustc failed for {:?}", src_path);

    bin_path
}

fn compile_with_deny_warnings(code: &str) {
    let _ = compile_rust_to_temp_bin_with_args(code, &["-D", "warnings"]);
}

fn compile_and_run(code: &str) -> String {
    compile_and_run_with_context(code, "compiled binary")
}

fn compile_and_run_with_context(code: &str, context: &str) -> String {
    let bin_path = compile_rust_to_temp_bin(code);
    let output = Command::new(bin_path)
        .output()
        .expect("failed to run compiled binary");
    assert!(
        output.status.success(),
        "{} failed. stdout:\n{}\nstderr:\n{}",
        context,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout).to_string()
}

fn compile_and_run_allow_failure(code: &str) -> std::process::Output {
    let bin_path = compile_rust_to_temp_bin(code);
    Command::new(bin_path)
        .output()
        .expect("failed to run compiled binary")
}

#[test]
fn typed_backend_generates_code_for_simple_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive copy Color (sort 1)
          (ctor red Color)
          (ctor rgb (pi r Nat (pi g Nat (pi b Nat Color)))))

        (def id_color (pi c Color Color)
          (lam c Color c))

        (def main Color
          (id_color (rgb (succ zero) zero (succ zero))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, true);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert!(code.contains("enum Color"), "expected Color enum in output");
    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime"
    );
    assert!(
        !code.contains("Expected Func"),
        "typed backend should not emit tag-check panics"
    );
    assert!(
        code.contains("non_snake_case"),
        "typed backend output should suppress generated naming warnings"
    );
    assert!(
        code.contains("non_camel_case_types"),
        "typed backend output should suppress generated naming warnings"
    );
}

#[test]
fn typed_backend_codegen_is_deterministic() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive copy Color (sort 1)
          (ctor red Color)
          (ctor rgb (pi r Nat (pi g Nat (pi b Nat Color)))))

        (def id_color (pi c Color Color)
          (lam c Color c))

        (def main Color
          (id_color (rgb (succ zero) zero (succ zero))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, true);
    let program = build_typed_program(&defs, main_name);
    let code1 = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let code2 = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert_eq!(code1, code2, "typed backend output is nondeterministic");
}

#[test]
fn typed_backend_supports_parametric_adts() {
    let source = r#"
        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive Box (pi (T (sort 1)) (sort 1))
          (ctor mk_box (pi (T (sort 1)) (pi (x T) (Box T)))))

        (def unbox_bool (pi b (Box Bool) Bool)
          (lam b (Box Bool)
            (match b Bool
              (case (mk_box x) x))))

        (def entry Bool
          (unbox_bool (mk_box Bool true)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert!(
        code.contains("enum Box<T0>"),
        "expected generic Box enum in output, got:\n{}",
        code
    );
    assert!(
        !code.contains("Value::"),
        "typed backend should not emit dynamic Value runtime for parametric subset"
    );
}

#[test]
fn typed_backend_executes_monomorphic_wrapper_over_polymorphic_function_value() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def id (pi A (sort 1) (pi x A A))
          (lam A (sort 1)
            (lam x A x)))

        (def id_nat (pi x Nat Nat)
          (lam x Nat
            (id Nat x)))

        (def entry Nat
          (id_nat (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_match_on_nat() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def add (pi n Nat (pi m Nat Nat))
          (lam n Nat
            (lam m Nat
              (match n Nat
                (case (zero) m)
                (case (succ m' ih) (succ ih))))))

        (def entry Nat
          (add (succ zero) (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 2"),
        "expected output to contain Result: 2, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_match_on_user_inductive() {
    let source = r#"
        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive copy Color (sort 1)
          (ctor red Color)
          (ctor rgb (pi r Bool (pi g Bool (pi b Bool Color)))))

        (def is_red (pi c Color Bool)
          (lam c Color
            (match c Bool
              (case (red) true)
              (case (rgb r g b) false))))

        (def entry Bool
          (is_red red))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: true"),
        "expected output to contain Result: true, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_print_nat() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def print_nat (pi n Nat Nat)
          (lam n Nat n))

        (def entry Nat
          (print_nat (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    let lines: Vec<_> = output.lines().collect();
    assert!(
        lines.iter().any(|line| *line == "1"),
        "expected print output to include a standalone '1', got {:?}",
        lines
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_nested_projections() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Pair (sort 1)
          (ctor pair (pi a Nat (pi b Nat Pair))))

        (inductive copy Tree (sort 1)
          (ctor leaf (pi p Pair Tree))
          (ctor node (pi left Tree (pi right Tree Tree))))

        (def sum_pair (pi p Pair Nat)
          (lam p Pair
            (match p Nat
              (case (pair a b) b))))

        (def leaf_sum (pi t Tree Nat)
          (lam t Tree
            (match t Nat
              (case (leaf p) (sum_pair p))
              (case (node l r) zero))))

        (def entry Nat
          (leaf_sum (leaf (pair zero (succ (succ zero))))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 2"),
        "expected output to contain Result: 2, got {}",
        output
    );
}

#[test]
fn typed_backend_matches_dynamic_output_for_stage1_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def entry Nat
          (succ (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name.clone());
    let typed_code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

    let typed_output = compile_and_run(&typed_code);
    let dynamic_output = compile_and_run(&dynamic_code);

    let typed_value = extract_nat_result(&typed_output);
    let dynamic_value = extract_nat_result(&dynamic_output);
    assert!(
        typed_value.is_some() && dynamic_value.is_some(),
        "expected nat outputs, got typed: {:?}, dynamic: {:?}",
        typed_output,
        dynamic_output
    );
    assert_eq!(
        typed_value, dynamic_value,
        "typed and dynamic outputs differ: typed {:?}, dynamic {:?}",
        typed_output, dynamic_output
    );
}

#[test]
fn typed_backend_matches_dynamic_output_for_parametric_adt_program() {
    let source = r#"
        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive Box (pi (T (sort 1)) (sort 1))
          (ctor mk_box (pi (T (sort 1)) (pi (x T) (Box T)))))

        (def unbox_bool (pi b (Box Bool) Bool)
          (lam b (Box Bool)
            (match b Bool
              (case (mk_box x) x))))

        (def entry Bool
          (unbox_bool (mk_box Bool true)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name.clone());
    let typed_code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

    assert!(
        typed_code.contains("enum Box<T0>"),
        "expected generic Box enum in typed output"
    );
    assert!(
        !typed_code.contains("Value::"),
        "typed backend should not emit Value runtime for parametric subset"
    );
    assert!(
        dynamic_code.contains("Value::"),
        "expected dynamic backend codegen to use Value runtime"
    );
}

#[test]
fn typed_backend_emits_ref_lowering_for_borrow_shared() {
    let source = r#"
        (axiom Ref (pi k Type (pi A (sort 1) (sort 1))))
        (axiom Shared Type)
        (axiom Mut Type)
        (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def ignore_ref (pi r (Ref #[r] Shared Nat) Nat)
          (lam r (Ref #[r] Shared Nat) (succ zero)))

        (def entry Nat
          (let x Nat
            (succ zero)
            (ignore_ref (borrow_shared x))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        code.contains("LrlRefShared"),
        "expected LrlRefShared lowering in output"
    );
    assert!(
        code.contains("from_value"),
        "expected borrow rvalue lowering to use wrapper constructor"
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_codegen_is_deterministic_with_generics_and_refs() {
    let source = r#"
        (axiom Ref (pi k Type (pi A (sort 1) (sort 1))))
        (axiom Shared Type)
        (axiom Mut Type)
        (axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref #[r] Shared A))))

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive Box (pi (T (sort 1)) (sort 1))
          (ctor mk_box (pi (T (sort 1)) (pi (x T) (Box T)))))

        (def ignore_ref (pi r (Ref #[r] Shared Nat) Nat)
          (lam r (Ref #[r] Shared Nat) (succ zero)))

        (def use_box (pi x Nat Nat)
          (lam x Nat
            (match (mk_box Nat x) Nat
              (case (mk_box y) y))))

        (def entry Nat
          (let x Nat
            (succ zero)
            (use_box (ignore_ref (borrow_shared x)))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);

    let code1 = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let code2 = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert_eq!(code1, code2, "typed backend output is nondeterministic");
    assert!(
        code1.contains("enum Box<T0>"),
        "expected generic Box enum in typed output"
    );
    assert!(
        code1.contains("LrlRefShared"),
        "expected shared-ref wrapper emission in typed output"
    );
}

#[test]
fn typed_backend_accepts_prop_inductive_function_signatures() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive ProofEq (pi A (sort 1) (pi a A (pi b A (sort 0))))
          (ctor reflP (pi A (sort 1) (pi a A (ProofEq A a a)))))

        (def keep_nat
          (pi n Nat (pi p (ProofEq Nat n n) Nat))
          (lam n Nat
            (lam p (ProofEq Nat n n)
              n)))

        (def entry Nat
          (keep_nat (succ zero) (reflP Nat (succ zero))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not fall back to dynamic Value runtime"
    );
    assert!(
        !code.contains("enum ProofEq"),
        "proof-only ADTs should be erased from runtime typed Rust output"
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_comp_constructor_from_typed_prelude() {
    let source = r#"
        (def entry (Comp Nat)
          (ret Nat (succ zero)))
    "#;

    let (env, ids, defs, main_name) =
        lower_program_with_prelude(source, Some("stdlib/prelude_typed.lrl"), false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        code.contains("enum Comp<T0>"),
        "expected Comp enum in typed output"
    );
    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime"
    );
    assert!(
        output.contains("Result: ret"),
        "expected output to contain Result: ret..., got {}",
        output
    );
}

#[test]
fn typed_backend_executes_eval_with_capability_token_from_typed_prelude() {
    let source = r#"
        (unsafe entry Dyn
          (eval (dyn_nat (succ zero)) eval_cap))
    "#;

    let (env, ids, defs, main_name) =
        lower_program_with_prelude(source, Some("stdlib/prelude_typed.lrl"), false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        code.contains("enum Dyn"),
        "expected Dyn enum in typed output"
    );
    assert!(
        output.contains("dyn_nat"),
        "expected output to contain dyn_nat, got {}",
        output
    );
}

#[test]
fn typed_backend_emits_index_and_runtime_check_lowering() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
          (ctor mk_vec_dyn (pi (T (sort 1)) (pi x T (VecDyn T))))
        )

        (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))

        (unsafe entry Nat
          (let v (VecDyn Nat)
            (mk_vec_dyn Nat (succ zero))
            v[0]))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert!(
        code.contains("runtime_bounds_check("),
        "expected bounds-check runtime check emission"
    );
    assert!(
        code.contains("runtime_index("),
        "expected index projection lowering via runtime_index"
    );
}

#[test]
fn typed_backend_executes_index_projection_for_vecdyn_singleton() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
          (ctor mk_vec_dyn (pi (T (sort 1)) (pi x T (VecDyn T))))
        )

        (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))

        (unsafe entry Nat
          (let v (VecDyn Nat)
            (mk_vec_dyn Nat (succ zero))
            v[0]))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_panics_on_out_of_bounds_vecdyn_index() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
          (ctor mk_vec_dyn (pi (T (sort 1)) (pi x T (VecDyn T))))
        )

        (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))

        (unsafe entry Nat
          (let v (VecDyn Nat)
            (mk_vec_dyn Nat (succ zero))
            v[1]))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run_allow_failure(&code);

    assert!(
        !output.status.success(),
        "expected runtime failure for out-of-bounds VecDyn index"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let combined = format!("{}\n{}", stdout, stderr);
    assert!(
        combined.contains("index out of bounds"),
        "expected out-of-bounds panic text, got:\n{}",
        combined
    );
}

#[test]
fn typed_backend_executes_deep_recursive_tree_payload_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy NatTree (sort 1)
          (ctor leaf (pi n Nat NatTree))
          (ctor node (pi l NatTree (pi r NatTree NatTree))))

        (def add_nat (pi a Nat (pi b Nat Nat))
          (lam a Nat
            (lam b Nat
              (match a Nat
                (case (zero) b)
                (case (succ x ih) (succ ih))))))

        (def sum_tree (pi t NatTree Nat)
          (lam t NatTree
            (match t Nat
              (case (leaf n) n)
              (case (node l lsum r rsum) (add_nat lsum rsum)))))

        (def entry Nat
          (sum_tree
            (node
              (leaf (succ zero))
              (node (leaf (succ (succ zero))) (leaf (succ zero))))))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 4"),
        "expected output to contain Result: 4, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_index_projection_for_slice_list_wrapper() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive List (pi T (sort 1) (sort 1))
          (ctor nil (pi (T (sort 1)) (List T)))
          (ctor cons (pi (T (sort 1)) (pi h T (pi t (List T) (List T)))))
        )

        (inductive (indexable) Slice (pi T (sort 1) (sort 1))
          (ctor mk_slice (pi (T (sort 1)) (pi data (List T) (Slice T))))
        )

        (axiom unsafe index_slice (pi {T (sort 1)} (pi v (Slice T) (pi i Nat T))))

        (unsafe entry Nat
          (let xs (Slice Nat)
            (mk_slice Nat (cons Nat (succ zero) (cons Nat zero (nil Nat))))
            xs[1]))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        output.contains("Result: 0"),
        "expected output to contain Result: 0, got {}",
        output
    );
}

#[test]
fn typed_backend_codegen_is_deterministic_for_slice_index_program() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive List (pi T (sort 1) (sort 1))
          (ctor nil (pi (T (sort 1)) (List T)))
          (ctor cons (pi (T (sort 1)) (pi h T (pi t (List T) (List T)))))
        )

        (inductive (indexable) Slice (pi T (sort 1) (sort 1))
          (ctor mk_slice (pi (T (sort 1)) (pi data (List T) (Slice T))))
        )

        (axiom unsafe index_slice (pi {T (sort 1)} (pi v (Slice T) (pi i Nat T))))

        (unsafe entry Nat
          (let xs (Slice Nat)
            (mk_slice Nat (cons Nat (succ zero) (cons Nat zero (nil Nat))))
            xs[1]))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code1 = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let code2 = codegen_program(&env, &ids, &program).expect("typed codegen failed");

    assert_eq!(code1, code2, "typed backend output is nondeterministic");
    assert!(
        code1.contains("runtime_index("),
        "expected typed index runtime lowering in output"
    );
}

#[test]
fn typed_backend_executes_index_projection_for_nested_indexable_shapes() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
          (ctor empty_vec (pi (T (sort 1)) (VecDyn T)))
          (ctor singleton_vec (pi (T (sort 1)) (pi meta Nat (pi x T (VecDyn T)))))
        )

        (inductive (indexable) Slice (pi T (sort 1) (sort 1))
          (ctor mk_slice (pi (T (sort 1)) (pi meta Nat (pi data (VecDyn T) (Slice T)))))
        )

        (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))
        (axiom unsafe index_slice (pi {T (sort 1)} (pi v (Slice T) (pi i Nat T))))

        (unsafe entry Nat
          (let xs (VecDyn Nat)
            (singleton_vec Nat zero (succ zero))
            (let s (Slice Nat)
              (mk_slice Nat zero xs)
              s[0])))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not emit dynamic Value runtime for nested indexable shapes"
    );
    assert!(
        code.contains("runtime_index("),
        "expected runtime_index lowering for nested indexable shapes"
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_index_projection_without_index_source_field_panics_at_runtime() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
          (ctor empty_vec (pi (T (sort 1)) (VecDyn T)))
          (ctor tagged_vec (pi (T (sort 1)) (pi meta Nat (VecDyn T))))
        )

        (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))

        (unsafe entry Bool
          (let xs (VecDyn Bool)
            (tagged_vec Bool zero)
            xs[0]))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    assert!(
        !code.contains("Value::"),
        "typed backend should not emit dynamic Value runtime"
    );
    let output = compile_and_run_allow_failure(&code);
    assert!(
        !output.status.success(),
        "expected runtime panic for source-less index shape"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("index out of bounds"),
        "expected index panic, got stderr:\n{}",
        stderr
    );
}

#[test]
fn typed_backend_emits_rawptr_and_interior_mutable_local_types() {
    let env = Env::new();
    let ids = IdRegistry::from_env(&env);

    let mut body = mir::Body::new(0);
    body.local_decls
        .push(mir::LocalDecl::new(MirType::Unit, Some("_0".to_string())));
    body.local_decls.push(mir::LocalDecl::new(
        MirType::RawPtr(Box::new(MirType::Nat), mir::types::Mutability::Not),
        Some("_1".to_string()),
    ));
    body.local_decls.push(mir::LocalDecl::new(
        MirType::InteriorMutable(Box::new(MirType::Nat), mir::types::IMKind::RefCell),
        Some("_2".to_string()),
    ));
    body.basic_blocks.push(mir::BasicBlockData {
        statements: vec![],
        terminator: Some(mir::Terminator::Return),
    });

    let program = TypedProgram {
        defs: vec![TypedBody {
            name: "entry".to_string(),
            body,
            closure_base: 0,
        }],
        closures: vec![],
        main_name: None,
    };

    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    assert!(
        code.contains("Option<*const u64>"),
        "expected raw pointer local type in emitted Rust"
    );
    assert!(
        code.contains("Option<LrlRefCell<u64>>"),
        "expected interior mutability local type in emitted Rust"
    );
}

#[test]
fn typed_backend_executes_higher_order_apply_twice() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def apply_twice
          (pi f (pi n Nat Nat)
            (pi n Nat Nat))
          (lam f (pi n Nat Nat)
            (lam n Nat
              (f (f n)))))

        (def entry Nat
          (apply_twice succ1 (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime for higher-order subset"
    );
    assert!(
        !code.contains("Expected Func"),
        "typed backend should not emit dynamic function tag checks"
    );
    assert!(
        output.contains("Result: 3"),
        "expected output to contain Result: 3, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_higher_order_returned_closure_capture() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def make_k
          (pi n Nat (pi x Nat Nat))
          (lam n Nat
            (lam x Nat n)))

        (def entry Nat
          ((make_k (succ zero)) zero))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not emit Value runtime for closure capture subset"
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_explicit_fnmut_higher_order_calls() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def use_twice
          (pi f (pi fnmut n Nat Nat)
            (pi fnmut x Nat Nat))
          (lam f (pi fnmut n Nat Nat)
            (lam fnmut x Nat
              (let y Nat (f x)
                (f y)))))

        (def mk_fnmut
          (pi bias Nat (pi fnmut n Nat Nat))
          (lam bias Nat
            (lam fnmut n Nat
              n)))

        (def entry Nat
          (use_twice (mk_fnmut zero) (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Value::"),
        "typed backend should not emit dynamic Value runtime for fnmut subset"
    );
    assert!(
        output.contains("Result: 1"),
        "expected output to contain Result: 1, got {}",
        output
    );
}

#[test]
fn typed_backend_executes_higher_order_match_selects_function() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive copy Bool (sort 1)
          (ctor true Bool)
          (ctor false Bool))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def id_nat (pi n Nat Nat)
          (lam n Nat n))

        (def choose
          (pi b Bool (pi n Nat Nat))
          (lam b Bool
            (match b (pi n Nat Nat)
              (case (true) succ1)
              (case (false) id_nat))))

        (def entry Nat
          ((choose true) (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run(&code);

    assert!(
        !code.contains("Expected Func"),
        "typed backend should not emit dynamic function-tag checks in match-selected calls"
    );
    assert!(
        output.contains("Result: 2"),
        "expected output to contain Result: 2, got {}",
        output
    );
}

#[test]
fn typed_backend_matches_dynamic_output_for_higher_order_program() {
    let source = r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def apply_twice
          (pi f (pi n Nat Nat)
            (pi n Nat Nat))
          (lam f (pi n Nat Nat)
            (lam n Nat
              (f (f n)))))

        (def entry Nat
          (apply_twice succ1 (succ zero)))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name.clone());
    let typed_code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

    let typed_output = compile_and_run(&typed_code);
    assert_eq!(
        extract_nat_result(&typed_output),
        Some(3),
        "unexpected typed backend output for higher-order program: {}",
        typed_output
    );

    let dynamic_output = compile_and_run(&dynamic_code);
    let typed_value = extract_nat_result(&typed_output);
    let dynamic_value = extract_nat_result(&dynamic_output);
    assert_eq!(
        typed_value, dynamic_value,
        "typed and dynamic outputs differ for higher-order program: typed {:?}, dynamic {:?}",
        typed_output, dynamic_output
    );
}

#[test]
fn typed_backend_round5_corpus_compiles_runs_and_stays_typed() {
    for (name, source) in collect_round5_sources() {
        let (env, ids, defs, main_name) =
            lower_program_with_prelude(&source, Some("stdlib/prelude_typed.lrl"), false);
        let program = build_typed_program(&defs, main_name);
        let code = codegen_program(&env, &ids, &program)
            .unwrap_or_else(|e| panic!("typed codegen failed for {}: {}", name, e));

        assert!(
            !code.contains("Value::"),
            "typed backend emitted dynamic Value runtime for {}",
            name
        );
        assert!(
            !code.contains("Expected Func"),
            "typed backend emitted function tag-check panic for {}",
            name
        );
        let output = compile_and_run(&code);
        assert!(
            extract_result_value(&output).is_some(),
            "expected result line for {}, got:\n{}",
            name,
            output
        );
    }
}

#[test]
fn typed_backend_tb_guards_are_unreachable_for_well_typed_code_examples() {
    let root = repo_root().join("code_examples");
    let sources = collect_lrl_sources_recursively(&root);
    assert!(
        !sources.is_empty(),
        "expected at least one source in {:?}",
        root
    );

    for (label, source) in sources {
        let (env, ids, defs, main_name) =
            lower_program_with_prelude(&source, Some("stdlib/prelude_typed.lrl"), true);
        let program = build_typed_program(&defs, main_name);
        assert_program_guard_invariants(&program, &ids, &label);
        codegen_program(&env, &ids, &program).unwrap_or_else(|e| {
            panic!("typed codegen unexpectedly failed for {} with {}", label, e)
        });
    }
}

#[test]
fn typed_backend_round5_corpus_is_deterministic() {
    for (name, source) in collect_round5_sources() {
        let (env, ids, defs, main_name) =
            lower_program_with_prelude(&source, Some("stdlib/prelude_typed.lrl"), false);
        let program = build_typed_program(&defs, main_name);
        let code1 = codegen_program(&env, &ids, &program)
            .unwrap_or_else(|e| panic!("typed codegen failed for {}: {}", name, e));
        let code2 = codegen_program(&env, &ids, &program)
            .unwrap_or_else(|e| panic!("typed codegen failed for {}: {}", name, e));
        assert_eq!(
            code1, code2,
            "typed backend output is nondeterministic for {}",
            name
        );
    }
}

#[test]
fn typed_backend_differential_parity_for_deterministic_nat_subset() {
    let cases: Vec<(&str, String, Option<&str>, ScalarResultKind)> = vec![
        (
            "inline_stage1_nat",
            r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def entry Nat
          (succ (succ zero)))
    "#
            .to_string(),
            None,
            ScalarResultKind::Nat,
        ),
        (
            "inline_higher_order_nat",
            r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def apply_twice
          (pi f (pi n Nat Nat)
            (pi n Nat Nat))
          (lam f (pi n Nat Nat)
            (lam n Nat
              (f (f n)))))

        (def entry Nat
          (apply_twice succ1 (succ zero)))
    "#
            .to_string(),
            None,
            ScalarResultKind::Nat,
        ),
        (
            "generated_nat_chain_17",
            generated_nat_chain_source(17),
            Some("stdlib/prelude_typed.lrl"),
            ScalarResultKind::Nat,
        ),
    ];

    for (case_name, source, prelude, kind) in cases {
        let (env, ids, defs, main_name) = lower_program_with_prelude(&source, prelude, false);
        let program = build_typed_program(&defs, main_name.clone());
        let typed_code = codegen_program(&env, &ids, &program)
            .unwrap_or_else(|e| panic!("typed codegen failed for {}: {}", case_name, e));
        let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

        assert!(
            !typed_code.contains("Value::"),
            "typed backend emitted dynamic runtime for {}",
            case_name
        );
        let typed_output =
            compile_and_run_with_context(&typed_code, &format!("typed binary for {}", case_name));
        let dynamic_output = compile_and_run_with_context(
            &dynamic_code,
            &format!("dynamic binary for {}", case_name),
        );
        assert_scalar_result_parity(case_name, kind, &typed_output, &dynamic_output);
    }
}

#[test]
fn typed_backend_generated_nat_chain_cases_match_dynamic() {
    for depth in [0usize, 1, 2, 5, 9, 17] {
        let source = generated_nat_chain_source(depth);
        let (env, ids, defs, main_name) =
            lower_program_with_prelude(&source, Some("stdlib/prelude_typed.lrl"), false);
        let program = build_typed_program(&defs, main_name.clone());
        let typed_code = codegen_program(&env, &ids, &program).unwrap_or_else(|e| {
            panic!("typed codegen failed for generated depth {}: {}", depth, e)
        });
        let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);
        let typed_output = compile_and_run(&typed_code);
        let dynamic_output = compile_and_run(&dynamic_code);

        assert_scalar_result_parity(
            &format!("generated_nat_depth_{}", depth),
            ScalarResultKind::Nat,
            &typed_output,
            &dynamic_output,
        );
    }
}

#[test]
fn typed_backend_panics_on_out_of_bounds_nested_index_projection() {
    let source = r#"
        (axiom unsafe interior_mutable Type)
        (axiom unsafe may_panic_on_borrow_violation Type)
        (axiom unsafe concurrency_primitive Type)
        (axiom unsafe atomic_primitive Type)
        (axiom unsafe indexable Type)

        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (inductive (indexable) VecDyn (pi T (sort 1) (sort 1))
          (ctor empty_vec (pi (T (sort 1)) (VecDyn T)))
          (ctor singleton_vec (pi (T (sort 1)) (pi meta Nat (pi x T (VecDyn T)))))
        )

        (inductive (indexable) Slice (pi T (sort 1) (sort 1))
          (ctor mk_slice (pi (T (sort 1)) (pi meta Nat (pi data (VecDyn T) (Slice T)))))
        )

        (axiom unsafe index_vec_dyn (pi {T (sort 1)} (pi v (VecDyn T) (pi i Nat T))))
        (axiom unsafe index_slice (pi {T (sort 1)} (pi v (Slice T) (pi i Nat T))))

        (unsafe entry Nat
          (let xs (VecDyn Nat)
            (singleton_vec Nat zero (succ zero))
            (let s (Slice Nat)
              (mk_slice Nat zero xs)
              s[1])))
    "#;

    let (env, ids, defs, main_name) = lower_program(source, false, false);
    let program = build_typed_program(&defs, main_name);
    let code = codegen_program(&env, &ids, &program).expect("typed codegen failed");
    let output = compile_and_run_allow_failure(&code);
    assert!(
        !output.status.success(),
        "expected runtime failure for out-of-bounds nested index projection"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let combined = format!("{}\n{}", stdout, stderr);
    assert!(
        combined.contains("index out of bounds"),
        "expected out-of-bounds panic text, got:\n{}",
        combined
    );
}

#[test]
fn typed_backend_generated_rust_is_warning_free_under_deny_warnings() {
    let mut cases: Vec<(String, String, Option<&str>)> = collect_round5_sources()
        .into_iter()
        .map(|(name, source)| {
            (
                format!("round5/{}", name),
                source,
                Some("stdlib/prelude_typed.lrl"),
            )
        })
        .collect();
    cases.push((
        "generated_nat_chain_11".to_string(),
        generated_nat_chain_source(11),
        Some("stdlib/prelude_typed.lrl"),
    ));
    cases.push((
        "inline_higher_order_nat".to_string(),
        r#"
        (inductive copy Nat (sort 1)
          (ctor zero Nat)
          (ctor succ (pi n Nat Nat)))

        (def succ1 (pi n Nat Nat)
          (lam n Nat (succ n)))

        (def apply_twice
          (pi f (pi n Nat Nat)
            (pi n Nat Nat))
          (lam f (pi n Nat Nat)
            (lam n Nat
              (f (f n)))))

        (def entry Nat
          (apply_twice succ1 (succ zero)))
    "#
        .to_string(),
        None,
    ));

    for (name, source, prelude) in cases {
        let (env, ids, defs, main_name) = lower_program_with_prelude(&source, prelude, false);
        let program = build_typed_program(&defs, main_name);
        let code = codegen_program(&env, &ids, &program)
            .unwrap_or_else(|e| panic!("typed codegen failed for {}: {}", name, e));

        assert!(
            !code.contains("Value::"),
            "typed backend emitted dynamic runtime in {}",
            name
        );
        assert!(
            !code.contains("Expected Func"),
            "typed backend emitted tag-check panic path in {}",
            name
        );
        compile_with_deny_warnings(&code);
    }
}
