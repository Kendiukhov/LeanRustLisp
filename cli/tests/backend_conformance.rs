use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use cli::set_prelude_macro_boundary_allowlist;
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::ast::Term;
use kernel::checker::Env;
use mir::codegen::{
    codegen_body, codegen_constant, codegen_prelude, codegen_recursors, sanitize_name,
};
use mir::typed_codegen::{codegen_program, TypedBody, TypedProgram};
use mir::types::{AdtId, CtorId, IdRegistry};
use mir::Literal;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

const CONFORMANCE_PRELUDE_REL: &str = "tests/backend_conformance/conformance_prelude.inc";

#[derive(Clone)]
struct LoweredDef {
    name: String,
    body: mir::Body,
    derived_bodies: Vec<mir::Body>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CaseTag {
    OverlapSubset,
    Excluded,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ExpectedResult {
    Nat(u64),
    Bool(bool),
}

#[derive(Debug, Clone)]
struct CaseMeta {
    tag: CaseTag,
    expect_exit: i32,
    expected_result: Option<ExpectedResult>,
    reason: Option<String>,
    prelude_source: String,
}

#[derive(Debug, Clone)]
struct ConformanceCase {
    path: PathBuf,
    source: String,
    meta: CaseMeta,
}

#[derive(Debug, Clone)]
struct ExecutionRecord {
    compile_ok: bool,
    compile_error: String,
    exit_code: i32,
    stdout: String,
    stderr: String,
}

#[derive(Debug, Clone)]
struct BackendEvaluation {
    ok: bool,
    canonical_result: Option<String>,
    extra_stdout: Vec<String>,
    reason: String,
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("failed to resolve repository root")
}

fn conformance_cases_root() -> PathBuf {
    repo_root().join("tests/backend_conformance/cases")
}

fn parse_case_meta(source: &str, path: &Path) -> Result<CaseMeta, String> {
    let mut tag: Option<CaseTag> = None;
    let mut expect_exit: Option<i32> = None;
    let mut expect_result_kind: Option<String> = None;
    let mut expect_result_value: Option<String> = None;
    let mut reason: Option<String> = None;
    let mut prelude_source: Option<String> = None;

    for line in source.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with(";;!") {
            continue;
        }
        let rest = trimmed.trim_start_matches(";;!").trim();
        let (key, value) = rest
            .split_once(':')
            .ok_or_else(|| format!("invalid metadata line in {:?}: {}", path, line))?;
        let key = key.trim();
        let value = value.trim();
        match key {
            "tag" => {
                tag = Some(match value {
                    "overlap-subset" => CaseTag::OverlapSubset,
                    "excluded" => CaseTag::Excluded,
                    _ => {
                        return Err(format!(
                            "invalid tag '{}' in {:?}; expected overlap-subset or excluded",
                            value, path
                        ));
                    }
                });
            }
            "expect_exit" => {
                expect_exit = Some(value.parse::<i32>().map_err(|e| {
                    format!("invalid expect_exit '{}' in {:?}: {}", value, path, e)
                })?);
            }
            "expect_result_kind" => {
                expect_result_kind = Some(value.to_string());
            }
            "expect_result" => {
                expect_result_value = Some(value.to_string());
            }
            "reason" => {
                reason = Some(value.to_string());
            }
            "prelude" => {
                if value.is_empty() {
                    return Err(format!("empty prelude metadata in {:?}", path));
                }
                prelude_source = Some(value.to_string());
            }
            _ => {
                return Err(format!("unknown metadata key '{}' in {:?}", key, path));
            }
        }
    }

    let tag = tag.ok_or_else(|| format!("missing 'tag' metadata in {:?}", path))?;
    let prelude_source = prelude_source.unwrap_or_else(|| CONFORMANCE_PRELUDE_REL.to_string());

    match tag {
        CaseTag::OverlapSubset => {
            let expect_exit = expect_exit.ok_or_else(|| {
                format!("missing 'expect_exit' metadata for overlap case {:?}", path)
            })?;
            let kind = expect_result_kind.ok_or_else(|| {
                format!(
                    "missing 'expect_result_kind' metadata for overlap case {:?}",
                    path
                )
            })?;
            let value = expect_result_value.ok_or_else(|| {
                format!(
                    "missing 'expect_result' metadata for overlap case {:?}",
                    path
                )
            })?;
            let expected_result = match kind.as_str() {
                "nat" => ExpectedResult::Nat(value.parse::<u64>().map_err(|e| {
                    format!("invalid nat expect_result '{}' in {:?}: {}", value, path, e)
                })?),
                "bool" => ExpectedResult::Bool(value.parse::<bool>().map_err(|e| {
                    format!(
                        "invalid bool expect_result '{}' in {:?}: {}",
                        value, path, e
                    )
                })?),
                _ => {
                    return Err(format!(
                        "invalid expect_result_kind '{}' in {:?}; expected nat or bool",
                        kind, path
                    ));
                }
            };
            Ok(CaseMeta {
                tag,
                expect_exit,
                expected_result: Some(expected_result),
                reason,
                prelude_source,
            })
        }
        CaseTag::Excluded => {
            let reason = reason.ok_or_else(|| {
                format!(
                    "missing 'reason' metadata for excluded conformance case {:?}",
                    path
                )
            })?;
            Ok(CaseMeta {
                tag,
                expect_exit: 0,
                expected_result: None,
                reason: Some(reason),
                prelude_source,
            })
        }
    }
}

fn collect_conformance_cases() -> Result<Vec<ConformanceCase>, String> {
    let root = conformance_cases_root();
    let mut files = Vec::new();
    let mut stack = vec![root.clone()];

    while let Some(dir) = stack.pop() {
        let entries = fs::read_dir(&dir)
            .map_err(|e| format!("failed to read conformance dir {:?}: {}", dir, e))?;
        for entry in entries {
            let entry =
                entry.map_err(|e| format!("failed to read dir entry in {:?}: {}", dir, e))?;
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|s| s.to_str()) else {
                continue;
            };
            if name.starts_with('.') {
                continue;
            }
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().and_then(|s| s.to_str()) == Some("lrl") {
                files.push(path);
            }
        }
    }

    files.sort();

    let mut cases = Vec::new();
    for path in files {
        let source = fs::read_to_string(&path)
            .map_err(|e| format!("failed to read conformance case {:?}: {}", path, e))?;
        let meta = parse_case_meta(&source, &path)?;
        cases.push(ConformanceCase { path, source, meta });
    }
    Ok(cases)
}

fn diagnostics_to_string(diags: &DiagnosticCollector) -> String {
    let mut out = String::new();
    for d in &diags.diagnostics {
        if d.level == Level::Error {
            out.push_str(&format!("- {}\n", d.message_with_code()));
        }
    }
    out
}

fn validate_body(name: &str, body: &mut mir::Body) -> Result<(), String> {
    mir::transform::storage::insert_exit_storage_deads(body);

    let mut typing = mir::analysis::typing::TypingChecker::new(body);
    typing.check();
    if !typing.errors().is_empty() {
        return Err(format!("typing errors in {}: {:?}", name, typing.errors()));
    }

    let mut ownership = mir::analysis::ownership::OwnershipAnalysis::new(body);
    ownership.analyze();
    let ownership_errors = ownership.check();
    if !ownership_errors.is_empty() {
        return Err(format!(
            "ownership errors in {}: {:?}",
            name, ownership_errors
        ));
    }

    let mut nll = mir::analysis::nll::NllChecker::new(body);
    nll.check();
    let nll_result = nll.into_result();
    if !nll_result.errors.is_empty() {
        return Err(format!(
            "borrow errors in {}: {:?}",
            name, nll_result.errors
        ));
    }
    if nll_result.is_ok() {
        nll_result.inject_runtime_checks(body);
    }

    Ok(())
}

fn lower_program_with_prelude(
    source: &str,
    prelude_source_path: &str,
) -> Result<(Env, IdRegistry, Vec<LoweredDef>, Option<String>), String> {
    let mut env = Env::new();
    let mut expander = Expander::new();
    env.set_allow_reserved_primitives(true);
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions::default();

    let prelude_path = repo_root().join(prelude_source_path);
    let prelude = fs::read_to_string(&prelude_path)
        .map_err(|e| format!("failed to read prelude {:?}: {}", prelude_path, e))?;
    let prelude_module = module_id_for_source(prelude_source_path);
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
    let mut prelude_diagnostics = DiagnosticCollector::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    process_code(
        &prelude,
        prelude_source_path,
        &mut env,
        &mut expander,
        &PipelineOptions::default(),
        &mut prelude_diagnostics,
    )
    .map_err(|e| format!("prelude processing failed for {:?}: {:?}", prelude_path, e))?;
    expander.clear_macro_boundary_allowlist();
    env.set_allow_reserved_primitives(allow_reserved);
    expander.set_default_imports(vec![prelude_module]);
    if prelude_diagnostics.has_errors() {
        return Err(format!(
            "prelude diagnostics contained errors:\n{}",
            diagnostics_to_string(&prelude_diagnostics)
        ));
    }

    let result = process_code(
        source,
        "backend_conformance_case",
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    )
    .map_err(|e| format!("process_code failed: {:?}", e))?;

    if diagnostics.has_errors() {
        return Err(format!(
            "diagnostics contained errors:\n{}",
            diagnostics_to_string(&diagnostics)
        ));
    }

    let ids = IdRegistry::from_env(&env);
    let mut names: Vec<_> = env.definitions().keys().cloned().collect();
    names.sort();

    let mut lowered_defs = Vec::new();
    for name in names {
        let def = env
            .definitions()
            .get(&name)
            .ok_or_else(|| format!("missing definition {}", name))?;

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
        .map_err(|e| format!("lowering context init error in {}: {}", name, e))?;

        let dest = mir::Place::from(mir::Local(0));
        let target = mir::BasicBlock(1);
        ctx.body.basic_blocks.push(mir::BasicBlockData {
            statements: vec![],
            terminator: Some(mir::Terminator::Return),
        });

        if let Some(val) = &def.value {
            ctx.lower_term(val, dest, target)
                .map_err(|e| format!("lowering error in {}: {}", name, e))?;
        }

        validate_body(&name, &mut ctx.body)?;

        for (i, body) in ctx.derived_bodies.borrow_mut().iter_mut().enumerate() {
            validate_body(&format!("{} closure {}", name, i), body)?;
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

        lowered_defs.push(LoweredDef {
            name: sanitize_name(&name),
            body: ctx.body,
            derived_bodies: ctx.derived_bodies.borrow().clone(),
        });
    }

    let main_name = result
        .deployed_definitions
        .last()
        .map(|name| sanitize_name(name));

    Ok((env, ids, lowered_defs, main_name))
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

fn mir_fingerprint(defs: &[LoweredDef]) -> u64 {
    let mut hasher = DefaultHasher::new();
    for def in defs {
        def.name.hash(&mut hasher);
        mir::pretty::pretty_print_body(&def.body).hash(&mut hasher);
        for body in &def.derived_bodies {
            mir::pretty::pretty_print_body(body).hash(&mut hasher);
        }
    }
    hasher.finish()
}

fn compile_rust_to_temp_bin(code: &str) -> Result<PathBuf, String> {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time went backwards")
        .as_nanos();
    let temp_dir = std::env::temp_dir().join(format!(
        "lrl_backend_conformance_{}_{}",
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&temp_dir)
        .map_err(|e| format!("failed to create temp dir {:?}: {}", temp_dir, e))?;
    let src_path = temp_dir.join("main.rs");
    let bin_path = temp_dir.join("main_bin");

    fs::write(&src_path, code)
        .map_err(|e| format!("failed to write generated rust {:?}: {}", src_path, e))?;

    let output = Command::new("rustc")
        .arg(&src_path)
        .arg("-O")
        .arg("-o")
        .arg(&bin_path)
        .output()
        .map_err(|e| format!("failed to invoke rustc for {:?}: {}", src_path, e))?;

    if !output.status.success() {
        return Err(format!(
            "rustc failed for {:?}\nstdout:\n{}\nstderr:\n{}",
            src_path,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    Ok(bin_path)
}

fn execute_generated_rust(code: &str) -> ExecutionRecord {
    match compile_rust_to_temp_bin(code) {
        Ok(bin_path) => match Command::new(bin_path).output() {
            Ok(output) => ExecutionRecord {
                compile_ok: true,
                compile_error: String::new(),
                exit_code: output.status.code().unwrap_or(-1),
                stdout: String::from_utf8_lossy(&output.stdout).to_string(),
                stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            },
            Err(e) => ExecutionRecord {
                compile_ok: true,
                compile_error: String::new(),
                exit_code: -1,
                stdout: String::new(),
                stderr: format!("failed to run compiled binary: {}", e),
            },
        },
        Err(err) => ExecutionRecord {
            compile_ok: false,
            compile_error: err,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
        },
    }
}

fn extract_result_value(output: &str) -> Option<&str> {
    output
        .lines()
        .find_map(|line| line.trim().strip_prefix("Result: "))
        .map(str::trim)
}

fn normalize_expected_result(expected: &ExpectedResult, value: &str) -> Option<String> {
    match expected {
        ExpectedResult::Nat(_) => {
            if let Some(rest) = value.strip_prefix("Nat(").and_then(|s| s.strip_suffix(')')) {
                rest.parse::<u64>().ok().map(|v| format!("nat:{}", v))
            } else {
                value.parse::<u64>().ok().map(|v| format!("nat:{}", v))
            }
        }
        ExpectedResult::Bool(_) => {
            if let Some(rest) = value
                .strip_prefix("Bool(")
                .and_then(|s| s.strip_suffix(')'))
            {
                rest.parse::<bool>().ok().map(|v| format!("bool:{}", v))
            } else {
                value.parse::<bool>().ok().map(|v| format!("bool:{}", v))
            }
        }
    }
}

fn expected_result_key(expected: &ExpectedResult) -> String {
    match expected {
        ExpectedResult::Nat(v) => format!("nat:{}", v),
        ExpectedResult::Bool(v) => format!("bool:{}", v),
    }
}

fn extra_stdout_lines(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .filter(|line| !line.starts_with("Result:"))
        .collect()
}

fn evaluate_backend(
    backend_name: &str,
    exec: &ExecutionRecord,
    expected_exit: i32,
    expected_result: &ExpectedResult,
) -> BackendEvaluation {
    if !exec.compile_ok {
        return BackendEvaluation {
            ok: false,
            canonical_result: None,
            extra_stdout: vec![],
            reason: format!("{} compile failed:\n{}", backend_name, exec.compile_error),
        };
    }

    if exec.exit_code != expected_exit {
        return BackendEvaluation {
            ok: false,
            canonical_result: None,
            extra_stdout: extra_stdout_lines(&exec.stdout),
            reason: format!(
                "{} exit code mismatch: expected {}, got {}",
                backend_name, expected_exit, exec.exit_code
            ),
        };
    }

    let expected_key = expected_result_key(expected_result);
    let observed_key = extract_result_value(&exec.stdout)
        .and_then(|v| normalize_expected_result(expected_result, v));

    if observed_key.as_deref() != Some(expected_key.as_str()) {
        return BackendEvaluation {
            ok: false,
            canonical_result: observed_key.clone(),
            extra_stdout: extra_stdout_lines(&exec.stdout),
            reason: format!(
                "{} result mismatch: expected {}, got {:?}",
                backend_name, expected_key, observed_key
            ),
        };
    }

    BackendEvaluation {
        ok: true,
        canonical_result: Some(expected_key),
        extra_stdout: extra_stdout_lines(&exec.stdout),
        reason: String::new(),
    }
}

fn classify_mismatch(dynamic_ok: bool, typed_ok: bool) -> &'static str {
    match (dynamic_ok, typed_ok) {
        (true, false) => "typed backend violates MIR semantics for this case",
        (false, true) => "dynamic backend violates MIR semantics for this case",
        (false, false) => {
            "both backends deviate from expected MIR semantics (or lowering/expectation bug)"
        }
        (true, true) => "observable-output mismatch despite both matching expected value",
    }
}

fn run_overlap_case(case: &ConformanceCase) -> Result<(), String> {
    let expected_result = case
        .meta
        .expected_result
        .as_ref()
        .ok_or_else(|| format!("missing expected result metadata in {:?}", case.path))?;

    let (env, ids, defs, main_name) =
        lower_program_with_prelude(&case.source, &case.meta.prelude_source)?;
    let mir_hash = mir_fingerprint(&defs);

    let typed_program = build_typed_program(&defs, main_name.clone());
    let typed_code = codegen_program(&env, &ids, &typed_program).map_err(|e| {
        format!(
            "typed codegen failed for {:?}: {} ({})",
            case.path,
            e.message,
            e.code()
        )
    })?;
    let dynamic_code = build_dynamic_code(&env, &ids, &defs, main_name);

    let typed_exec = execute_generated_rust(&typed_code);
    let dynamic_exec = execute_generated_rust(&dynamic_code);

    let typed_eval = evaluate_backend("typed", &typed_exec, case.meta.expect_exit, expected_result);
    let dynamic_eval = evaluate_backend(
        "dynamic",
        &dynamic_exec,
        case.meta.expect_exit,
        expected_result,
    );

    let observables_match = typed_eval.canonical_result == dynamic_eval.canonical_result
        && typed_eval.extra_stdout == dynamic_eval.extra_stdout
        && typed_exec.exit_code == dynamic_exec.exit_code;

    if typed_eval.ok && dynamic_eval.ok && observables_match {
        return Ok(());
    }

    let classification = classify_mismatch(dynamic_eval.ok, typed_eval.ok);

    Err(format!(
        "case: {:?}\ntag: overlap-subset\nmir_hash: {}\nclassification: {}\nexpected_exit: {}\nexpected_result: {}\n\n\
         typed:\n  ok: {}\n  reason: {}\n  exit: {}\n  stdout:\n{}\n  stderr:\n{}\n  compile_error:\n{}\n\n\
         dynamic:\n  ok: {}\n  reason: {}\n  exit: {}\n  stdout:\n{}\n  stderr:\n{}\n  compile_error:\n{}\n",
        case.path,
        mir_hash,
        classification,
        case.meta.expect_exit,
        expected_result_key(expected_result),
        typed_eval.ok,
        typed_eval.reason,
        typed_exec.exit_code,
        typed_exec.stdout,
        typed_exec.stderr,
        typed_exec.compile_error,
        dynamic_eval.ok,
        dynamic_eval.reason,
        dynamic_exec.exit_code,
        dynamic_exec.stdout,
        dynamic_exec.stderr,
        dynamic_exec.compile_error,
    ))
}

#[test]
fn backend_conformance_metadata_is_well_formed() {
    let cases = collect_conformance_cases().expect("failed to collect conformance cases");
    assert!(!cases.is_empty(), "no conformance cases found");

    let overlap_count = cases
        .iter()
        .filter(|case| case.meta.tag == CaseTag::OverlapSubset)
        .count();
    let excluded_count = cases
        .iter()
        .filter(|case| case.meta.tag == CaseTag::Excluded)
        .count();

    assert!(
        overlap_count >= 10,
        "need at least 10 overlap-subset cases; found {}",
        overlap_count
    );
    assert!(
        excluded_count >= 1,
        "need at least one excluded case; found {}",
        excluded_count
    );

    for case in &cases {
        match case.meta.tag {
            CaseTag::OverlapSubset => {
                assert!(
                    case.meta.expected_result.is_some(),
                    "overlap case {:?} missing expected result",
                    case.path
                );
            }
            CaseTag::Excluded => {
                let reason = case.meta.reason.as_deref().unwrap_or("").trim();
                assert!(
                    !reason.is_empty(),
                    "excluded case {:?} missing reason",
                    case.path
                );
            }
        }
    }
}

#[test]
fn backend_conformance_overlap_subset_matches() {
    let cases = collect_conformance_cases().expect("failed to collect conformance cases");
    let overlap_cases: Vec<_> = cases
        .into_iter()
        .filter(|case| case.meta.tag == CaseTag::OverlapSubset)
        .collect();

    let mut failures = Vec::new();
    for case in &overlap_cases {
        if let Err(err) = run_overlap_case(case) {
            failures.push(err);
        }
    }

    if !failures.is_empty() {
        panic!(
            "backend conformance mismatches ({}):\n\n{}",
            failures.len(),
            failures.join("\n----------------------------------------\n")
        );
    }
}
