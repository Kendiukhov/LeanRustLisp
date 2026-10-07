//! Stage matrix for LRL source files.
//!
//! For every top-level definition (`def`, `partial`, `unsafe`, `noncomputable`, including
//! definitions produced by macro calls) and every top-level expression of a file, this tool
//! reports the verdict of each compiler stage *independently*:
//!
//! * `elab`           — the frontend: the driver's pre-checks, type/value elaboration,
//!                      constraint solving and core-invariant validation;
//! * `kernel_typing`  — `kernel::checker::infer` on the type and `kernel::checker::check` on the
//!                      value (the driver's "Kernel re-check");
//! * `kernel_admit`   — `Env::add_definition` on a CLONE of the environment (typing, the kernel
//!                      ownership walk, capture-mode validation, effects, termination, axioms);
//!                      `kernel_ownership` is derived from the phase in which it failed;
//! * `mir`            — MIR lowering of the elaborated term and MIR typing / MIR ownership /
//!                      NLL borrow checking on the lowered body AND every derived closure body.
//!                      This part is computed even when the kernel rejects the definition: the
//!                      elaborated term is lowered without being admitted (no kernel API is
//!                      changed or weakened; the environment is only read).
//!
//! The environment is advanced exactly as the CLI advances it: after the stages of a form have
//! been computed, the form is replayed through the unmodified `cli::driver::process_code` (on
//! the source text with every other form blanked, so spans are unchanged). The replay's own
//! verdict is reported as `cli`, and the harness's prediction (`kernel_admit` ok AND every MIR
//! check ok AND the interior-mutability gate) is cross-checked against it (`consistent`).
//!
//! Output: one JSON object per line on stdout (`record` = `file` | `def` | `form` | `end`).
//! Run it from the repository root (the prelude is located relative to the working directory,
//! like the CLI).

use cli::driver::{self, PipelineOptions};
use frontend::declaration_parser::DeclarationParser;
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::elaborator::Elaborator;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use frontend::parser::Parser;
use frontend::surface::{Declaration, SurfaceTerm, Syntax, SyntaxKind};
use kernel::ast::{is_reserved_primitive_name, Definition, Term, Totality, Transparency};
use kernel::checker::{Context, Env, TypeError};
use kernel::ownership::DefCaptureModeMap;
use std::cell::RefCell;
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::Path;
use std::rc::Rc;

// ---------------------------------------------------------------------------------------------
// Minimal JSON writer (no external dependencies).

enum J {
    Null,
    B(bool),
    N(i64),
    S(String),
    A(Vec<J>),
    O(Vec<(&'static str, J)>),
}

fn s<T: Into<String>>(x: T) -> J {
    J::S(x.into())
}

fn opt_s(x: Option<String>) -> J {
    x.map(J::S).unwrap_or(J::Null)
}

fn opt_b(x: Option<bool>) -> J {
    x.map(J::B).unwrap_or(J::Null)
}

impl J {
    fn render(&self, out: &mut String) {
        match self {
            J::Null => out.push_str("null"),
            J::B(b) => out.push_str(if *b { "true" } else { "false" }),
            J::N(n) => out.push_str(&n.to_string()),
            J::S(text) => {
                out.push('"');
                for c in text.chars() {
                    match c {
                        '"' => out.push_str("\\\""),
                        '\\' => out.push_str("\\\\"),
                        '\n' => out.push_str("\\n"),
                        '\r' => out.push_str("\\r"),
                        '\t' => out.push_str("\\t"),
                        c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
                        c => out.push(c),
                    }
                }
                out.push('"');
            }
            J::A(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.render(out);
                }
                out.push(']');
            }
            J::O(fields) => {
                out.push('{');
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    J::S((*k).to_string()).render(out);
                    out.push(':');
                    v.render(out);
                }
                out.push('}');
            }
        }
    }
}

fn emit(record: J) {
    let mut line = String::new();
    record.render(&mut line);
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    let _ = writeln!(lock, "{}", line);
    let _ = lock.flush();
}

/// First line of a message, at most 400 characters (diagnostics can be long terms).
fn short(msg: &str) -> String {
    let first = msg.lines().next().unwrap_or("");
    if first.chars().count() > 400 {
        let cut: String = first.chars().take(400).collect();
        format!("{}...", cut)
    } else {
        first.to_string()
    }
}

// ---------------------------------------------------------------------------------------------
// Panic capture: a panic inside a stage is recorded instead of aborting the whole file.

thread_local! {
    static LAST_PANIC: RefCell<Option<String>> = const { RefCell::new(None) };
}

fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        let payload = if let Some(text) = info.payload().downcast_ref::<&str>() {
            (*text).to_string()
        } else if let Some(text) = info.payload().downcast_ref::<String>() {
            text.clone()
        } else {
            "non-string panic payload".to_string()
        };
        let location = info
            .location()
            .map(|l| format!(" at {}:{}", l.file(), l.line()))
            .unwrap_or_default();
        LAST_PANIC.with(|p| *p.borrow_mut() = Some(format!("{}{}", payload, location)));
    }));
}

fn guarded<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(v) => Ok(v),
        Err(_) => Err(LAST_PANIC
            .with(|p| p.borrow_mut().take())
            .unwrap_or_else(|| "panic".to_string())),
    }
}

// ---------------------------------------------------------------------------------------------
// Options

#[derive(Clone, Copy, PartialEq, Eq)]
enum Backend {
    Dynamic,
    Typed,
}

struct Opts {
    file: String,
    backend: Backend,
    allow_axioms: bool,
    macro_boundary_warn: bool,
    allow_redefine: bool,
    dump_mir: Option<String>,
}

fn parse_args() -> Result<Opts, String> {
    let mut file = None;
    let mut backend = Backend::Dynamic;
    let mut allow_axioms = false;
    let mut macro_boundary_warn = false;
    let mut allow_redefine = false;
    let mut dump_mir = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--backend" => match args.next().as_deref() {
                Some("dynamic") => backend = Backend::Dynamic,
                Some("typed") | Some("auto") => backend = Backend::Typed,
                other => return Err(format!("unknown backend {:?}", other)),
            },
            "--allow-axioms" => allow_axioms = true,
            "--macro-boundary-warn" => macro_boundary_warn = true,
            "--allow-redefine" => allow_redefine = true,
            "--dump-mir" => dump_mir = args.next(),
            "-h" | "--help" => {
                return Err("usage: stage_matrix [--backend dynamic|typed] [--allow-axioms] \
                            [--macro-boundary-warn] [--allow-redefine] [--dump-mir NAME|all] <file.lrl>"
                    .to_string())
            }
            other if file.is_none() => file = Some(other.to_string()),
            other => return Err(format!("unexpected argument {}", other)),
        }
    }
    Ok(Opts {
        file: file.ok_or("missing <file.lrl>")?,
        backend,
        allow_axioms,
        macro_boundary_warn,
        allow_redefine,
        dump_mir,
    })
}

// ---------------------------------------------------------------------------------------------
// Prelude: same stack, options and order as `run` (package_manager::load_prelude, dynamic stack)
// or `compile` (compiler.rs, typed stack for --backend typed/auto).

fn load_prelude(env: &mut Env, expander: &mut Expander, backend: Backend) -> Result<(), String> {
    let mode = match backend {
        Backend::Dynamic => cli::compiler::BackendMode::Dynamic,
        Backend::Typed => cli::compiler::BackendMode::Typed,
    };
    let prelude_options = PipelineOptions {
        prelude_frozen: false,
        allow_redefine: false,
        allow_axioms: true,
        ..Default::default()
    };
    let mut modules = Vec::new();
    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    for path in cli::compiler::prelude_stack_for_backend(mode) {
        if !Path::new(path).exists() {
            continue;
        }
        let content =
            std::fs::read_to_string(path).map_err(|e| format!("read prelude {}: {}", path, e))?;
        let module = driver::module_id_for_source(path);
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        cli::set_prelude_macro_boundary_allowlist(expander, &module);
        if !modules.is_empty() {
            expander.set_default_imports(modules.clone());
        }
        let mut diagnostics = DiagnosticCollector::new();
        let _ = driver::process_code(
            &content,
            path,
            env,
            expander,
            &prelude_options,
            &mut diagnostics,
        );
        expander.clear_macro_boundary_allowlist();
        if diagnostics.has_errors() {
            let errors: Vec<String> = diagnostics
                .diagnostics
                .iter()
                .filter(|d| d.level == Level::Error)
                .map(|d| d.message_with_code())
                .collect();
            return Err(format!("prelude {} failed: {}", path, errors.join(" | ")));
        }
        modules.push(module);
    }
    env.set_allow_reserved_primitives(allow_reserved);
    if !modules.is_empty() {
        env.init_marker_registry()
            .map_err(|e| format!("marker registry: {:?}", e))?;
        expander.set_default_imports(modules);
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Name resolution state (mirrors the driver's handling of module / import / open declarations).

#[derive(Default, Clone)]
struct Resolution {
    current_module: Option<String>,
    imported: Vec<(String, String)>, // (alias, module)
    opened: Vec<String>,
}

impl Resolution {
    fn qualify(&self, name: &str) -> String {
        if name.contains('.') {
            return name.to_string();
        }
        match &self.current_module {
            Some(m) if !m.is_empty() => format!("{}.{}", m, name),
            _ => name.to_string(),
        }
    }

    fn elaborator<'a>(&self, env: &'a Env) -> Elaborator<'a> {
        let mut elab = Elaborator::new(env);
        elab.set_name_resolution(
            self.current_module.clone(),
            self.opened.clone(),
            self.imported.clone(),
        );
        elab
    }

    fn open(&mut self, target: &str) {
        let mut candidates: Vec<String> = Vec::new();
        for (alias, module) in &self.imported {
            if alias == target || module == target || module.rsplit('.').next() == Some(target) {
                if !candidates.contains(module) {
                    candidates.push(module.clone());
                }
            }
        }
        if candidates.len() == 1 && !self.opened.contains(&candidates[0]) {
            self.opened.push(candidates[0].clone());
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Stage verdicts

struct Verdict {
    ok: Option<bool>, // None = not computed (an earlier stage produced no input)
    code: Option<String>,
    variant: Option<String>,
    phase: Option<String>,
    msg: Option<String>,
}

impl Verdict {
    fn pass() -> Self {
        Verdict {
            ok: Some(true),
            code: None,
            variant: None,
            phase: None,
            msg: None,
        }
    }
    fn na() -> Self {
        Verdict {
            ok: None,
            code: None,
            variant: None,
            phase: None,
            msg: None,
        }
    }
    fn fail(phase: &str, code: Option<&str>, msg: String) -> Self {
        Verdict {
            ok: Some(false),
            code: code.map(|c| c.to_string()),
            variant: None,
            phase: Some(phase.to_string()),
            msg: Some(short(&msg)),
        }
    }
    fn json(&self) -> J {
        J::O(vec![
            ("ok", opt_b(self.ok)),
            ("code", opt_s(self.code.clone())),
            ("variant", opt_s(self.variant.clone())),
            ("phase", opt_s(self.phase.clone())),
            ("msg", opt_s(self.msg.clone())),
        ])
    }
}

fn type_error_variant(err: &TypeError) -> String {
    match err {
        TypeError::OwnershipError(o) => o.variant_name().to_string(),
        other => {
            let dbg = format!("{:?}", other);
            dbg.split(|c: char| !c.is_alphanumeric() && c != '_')
                .next()
                .unwrap_or("")
                .to_string()
        }
    }
}

/// The phase of `Env::add_definition` (kernel/src/checker.rs) that raised `code`.
/// Order in add_definition: reserved names / redefinition / core invariants / partial-in-type
/// ("pre"), type + value typing incl. function kinds ("typing"), `check_ownership_in_term`
/// ("ownership"), `validate_capture_modes`, `check_effects`, termination, axiom dependencies.
fn admit_phase(code: &str) -> &'static str {
    match code {
        "K0008" | "K0009" | "K0010" | "K0011" | "K0012" | "K0013" | "K0020" | "K0039" | "K0040"
        | "K0047" => "pre",
        "K0021" => "ownership",
        "K0033" | "K0034" => "capture_modes",
        "K0022" => "effects",
        "K0018" | "K0019" | "K0025" | "K0026" => "termination",
        "K0023" => "axioms",
        _ => "typing",
    }
}

/// Kernel ownership verdict derived from add_definition: the walk runs after typing and
/// before capture modes / effects / termination / axioms.
fn kernel_ownership_from_admit(admit: &Verdict) -> &'static str {
    match admit.ok {
        None => "not_computed",
        Some(true) => "pass",
        Some(false) => match admit.phase.as_deref() {
            Some("ownership") => "reject",
            Some("capture_modes") | Some("effects") | Some("termination") | Some("axioms") => {
                "pass"
            }
            _ => "not_reached",
        },
    }
}

fn uses_interior_mutability_axioms(axioms: &[String]) -> bool {
    // Same list as cli/src/driver.rs `uses_interior_mutability_axioms`.
    axioms.iter().any(|ax| {
        matches!(
            ax.as_str(),
            "may_panic_on_borrow_violation" | "concurrency_primitive" | "atomic_primitive"
        )
    })
}

// ---------------------------------------------------------------------------------------------
// MIR stage (replicates cli/src/driver.rs `validate_definition_mir`, without the panic-free lints)

struct BodyReport {
    label: String,
    typing: Vec<(String, String)>,
    ownership: Vec<(String, String)>,
    borrow: Vec<(String, String)>,
}

struct MirReport {
    env_used: &'static str, // "admitted" (env after add_definition) or "pre_admission"
    lowered: Option<bool>,
    lower_error: Option<String>,
    panic: Option<String>,
    bodies: Vec<BodyReport>,
}

impl MirReport {
    fn stage_ok(&self, pick: impl Fn(&BodyReport) -> usize) -> Option<bool> {
        if self.lowered != Some(true) {
            return None;
        }
        Some(self.bodies.iter().all(|b| pick(b) == 0))
    }
    fn all_ok(&self) -> bool {
        self.lowered == Some(true)
            && self
                .bodies
                .iter()
                .all(|b| b.typing.is_empty() && b.ownership.is_empty() && b.borrow.is_empty())
    }
    fn errors_json(&self, pick: impl Fn(&BodyReport) -> &Vec<(String, String)>) -> J {
        let mut out = Vec::new();
        for b in &self.bodies {
            for (code, msg) in pick(b) {
                out.push(J::O(vec![
                    ("body", s(b.label.clone())),
                    ("code", s(code.clone())),
                    ("msg", s(msg.clone())),
                ]));
            }
        }
        J::A(out)
    }
    fn json(&self) -> J {
        J::O(vec![
            ("env", s(self.env_used)),
            ("lowered", opt_b(self.lowered)),
            ("lower_error", opt_s(self.lower_error.clone())),
            ("panic", opt_s(self.panic.clone())),
            ("bodies", J::N(self.bodies.len() as i64)),
            ("typing_ok", opt_b(self.stage_ok(|b| b.typing.len()))),
            ("ownership_ok", opt_b(self.stage_ok(|b| b.ownership.len()))),
            ("borrow_ok", opt_b(self.stage_ok(|b| b.borrow.len()))),
            ("ok", J::B(self.all_ok())),
            ("typing_errors", self.errors_json(|b| &b.typing)),
            ("ownership_errors", self.errors_json(|b| &b.ownership)),
            ("borrow_errors", self.errors_json(|b| &b.borrow)),
        ])
    }
}

fn check_body(label: String, body: &mir::Body) -> BodyReport {
    let mut typing = mir::analysis::typing::TypingChecker::new(body);
    typing.check();
    let typing_errors = typing
        .errors()
        .iter()
        .map(|e| (e.diagnostic_code().to_string(), short(&e.to_string())))
        .collect();
    let mut own = mir::analysis::ownership::OwnershipAnalysis::new(body);
    own.analyze();
    let ownership_errors = own
        .check_structured()
        .iter()
        .map(|e| (e.diagnostic_code().to_string(), short(&e.to_string())))
        .collect();
    let mut nll = mir::analysis::nll::NllChecker::new(body);
    nll.check();
    let result = nll.into_result();
    let borrow_errors = result
        .errors
        .iter()
        .map(|e| (e.diagnostic_code().to_string(), short(&e.to_string())))
        .collect();
    BodyReport {
        label,
        typing: typing_errors,
        ownership: ownership_errors,
        borrow: borrow_errors,
    }
}

fn run_mir(
    env: &Env,
    env_used: &'static str,
    name: &str,
    ty: Rc<Term>,
    val: Rc<Term>,
    capture_modes: DefCaptureModeMap,
    term_span_map: Rc<mir::lower::TermSpanMap>,
    dump: bool,
) -> MirReport {
    let mut report = MirReport {
        env_used,
        lowered: Some(false),
        lower_error: None,
        panic: None,
        bodies: Vec::new(),
    };
    let ids = mir::types::IdRegistry::from_env(env);
    if ids.has_errors() {
        let msgs: Vec<String> = ids.errors().iter().map(|e| e.to_string()).collect();
        report.lower_error = Some(short(&format!("IdRegistry: {}", msgs.join(" | "))));
        return report;
    }
    let mut ctx = match mir::lower::LoweringContext::new_with_metadata(
        vec![],
        ty,
        env,
        &ids,
        Some(term_span_map),
        Some(name.to_string()),
        Some(Rc::new(capture_modes)),
    ) {
        Ok(ctx) => ctx,
        Err(e) => {
            report.lower_error = Some(short(&format!("Lowering error in {}: {}", name, e)));
            return report;
        }
    };
    let dest = mir::Place::from(mir::Local(0));
    let target = mir::BasicBlock(1);
    ctx.body.basic_blocks.push(mir::BasicBlockData {
        statements: vec![],
        terminator: None,
    });
    if let Err(e) = ctx.lower_term(&val, dest, target) {
        report.lower_error = Some(short(&format!("Lowering error in {}: {}", name, e)));
        return report;
    }
    ctx.set_block(target);
    ctx.terminate_with_term_span(&val, mir::Terminator::Return);
    mir::transform::storage::insert_exit_storage_deads(&mut ctx.body);
    report.lowered = Some(true);
    if dump {
        eprintln!(
            "===== {} ({})\n{}",
            name,
            env_used,
            mir::pretty::pretty_print_body(&ctx.body)
        );
    }
    report.bodies.push(check_body(name.to_string(), &ctx.body));
    let mut derived = ctx.derived_bodies.borrow_mut();
    for (i, body) in derived.iter_mut().enumerate() {
        mir::transform::storage::insert_exit_storage_deads(body);
        if dump {
            eprintln!(
                "===== {} closure {}\n{}",
                name,
                i,
                mir::pretty::pretty_print_body(body)
            );
        }
        report
            .bodies
            .push(check_body(format!("{} closure {}", name, i), body));
    }
    report
}

fn build_term_span_map(elab: &Elaborator) -> mir::lower::TermSpanMap {
    // Same construction as cli/src/driver.rs `build_term_span_map`.
    let spans_by_id = elab
        .span_map()
        .iter()
        .map(|(id, span)| {
            (
                id.0,
                mir::errors::SourceSpan {
                    start: span.start,
                    end: span.end,
                    line: span.line,
                    col: span.col,
                },
            )
        })
        .collect();
    let term_ids_by_ptr = elab
        .term_id_map()
        .iter()
        .map(|(ptr, id)| (*ptr, id.0))
        .collect();
    mir::lower::TermSpanMap::new(spans_by_id, term_ids_by_ptr)
        .with_pinned_terms(elab.pinned_terms().to_vec())
}

// ---------------------------------------------------------------------------------------------
// Per-definition analysis

struct DefInput {
    name: String,
    kind: &'static str, // def | partial | unsafe | expr
    ty: Option<SurfaceTerm>,
    val: SurfaceTerm,
    totality: Totality,
    transparency: Transparency,
    noncomputable: bool,
}

struct DefAnalysis {
    name: String,
    elab: Verdict,
    kernel_typing: Verdict,
    kernel_admit: Verdict,
    gate: Option<String>,
    mir: Option<MirReport>,
    predicted_admitted: bool,
}

fn analyze(env: &Env, res: &Resolution, input: DefInput, opts: &Opts) -> DefAnalysis {
    let is_expr = input.kind == "expr";
    let name = if is_expr {
        "<expr>".to_string()
    } else {
        res.qualify(&input.name)
    };
    let mut out = DefAnalysis {
        name: name.clone(),
        elab: Verdict::na(),
        kernel_typing: Verdict::na(),
        kernel_admit: Verdict::na(),
        gate: None,
        mir: None,
        predicted_admitted: false,
    };

    // ---- Elaboration (the driver's Def / Expr arms up to the kernel re-check)
    if !is_expr {
        if is_reserved_primitive_name(&name) && !env.allows_reserved_primitives() {
            out.elab = Verdict::fail("pre", None, format!("Reserved primitive name '{}'", name));
            return out;
        }
        if !opts.allow_redefine
            && (env.get_definition(&name).is_some() || env.get_inductive(&name).is_some())
        {
            out.elab = Verdict::fail(
                "pre",
                None,
                format!("Cannot redefine definition '{}': prelude is frozen", name),
            );
            return out;
        }
        if input.totality != Totality::Partial {
            let fix = input
                .val
                .find_fix_span()
                .or_else(|| input.ty.as_ref().and_then(|t| t.find_fix_span()));
            if fix.is_some() {
                out.elab = Verdict::fail(
                    "pre",
                    None,
                    format!("fix is only allowed in partial definitions ('{}')", name),
                );
                return out;
            }
        }
    }

    let mut elab = res.elaborator(env);
    let (mut ty_core, val_core) = if is_expr {
        match elab.infer(input.val) {
            Ok((core, ty)) => {
                if let Err(e) = elab.solve_constraints() {
                    out.elab =
                        Verdict::fail("constraints", Some(e.diagnostic_code()), e.to_string());
                    return out;
                }
                let core = elab.instantiate_metas(&core);
                if let Err(e) = kernel::checker::validate_core_term(&core) {
                    out.elab = Verdict::fail("value_invariants", None, e.to_string());
                    return out;
                }
                let ty = elab.instantiate_metas(&ty);
                if let Err(e) = kernel::checker::validate_core_term(&ty) {
                    out.elab = Verdict::fail("type_invariants", None, e.to_string());
                    return out;
                }
                (ty, core)
            }
            Err(e) => {
                out.elab = Verdict::fail("value", Some(e.diagnostic_code()), e.to_string());
                return out;
            }
        }
    } else {
        let ty_surface = input.ty.expect("definition type");
        let ty_core = match elab.infer_type(ty_surface) {
            Ok((t, sort)) => {
                if !matches!(*sort, Term::Sort(_)) {
                    out.elab =
                        Verdict::fail("type", None, "type of definition is not a Sort".into());
                    return out;
                }
                let t = elab.instantiate_metas(&t);
                if let Err(e) = kernel::checker::validate_core_term(&t) {
                    out.elab = Verdict::fail("type_invariants", None, e.to_string());
                    return out;
                }
                t
            }
            Err(e) => {
                out.elab = Verdict::fail("type", Some(e.diagnostic_code()), e.to_string());
                return out;
            }
        };
        if input.totality == Totality::Partial {
            match kernel::checker::is_comp_return_type(env, &Context::new(), &ty_core) {
                Ok(true) => {}
                Ok(false) => {
                    out.elab = Verdict::fail(
                        "partial_return",
                        None,
                        format!("Partial definition '{}' must return Comp A", name),
                    );
                    return out;
                }
                Err(e) => {
                    out.elab =
                        Verdict::fail("partial_return", Some(e.diagnostic_code()), e.to_string());
                    return out;
                }
            }
        }
        elab.clear_capture_mode_map();
        let val_core = match elab.check(input.val, &ty_core) {
            Ok(t) => {
                if let Err(e) = elab.solve_constraints() {
                    out.elab =
                        Verdict::fail("constraints", Some(e.diagnostic_code()), e.to_string());
                    return out;
                }
                let t = elab.instantiate_metas(&t);
                if let Err(e) = kernel::checker::validate_core_term(&t) {
                    out.elab = Verdict::fail("value_invariants", None, e.to_string());
                    return out;
                }
                t
            }
            Err(e) => {
                out.elab = Verdict::fail("value", Some(e.diagnostic_code()), e.to_string());
                return out;
            }
        };
        (ty_core, val_core)
    };
    if !is_expr {
        ty_core = elab.instantiate_metas(&ty_core);
    }
    out.elab = Verdict::pass();

    let closure_ids = kernel::ownership::collect_closure_ids(&val_core, &name);
    let closure_free_vars = kernel::ownership::collect_closure_free_vars(&val_core);
    let capture_modes = kernel::ownership::map_capture_modes_to_closures_filtered(
        &closure_ids,
        &closure_free_vars,
        elab.capture_mode_map(),
    );
    let binder_names = elab.binder_name_map().clone();
    let term_span_map = Rc::new(build_term_span_map(&elab));
    drop(elab);

    // ---- Kernel typing (the driver's "Kernel re-check")
    let ctx = Context::new();
    out.kernel_typing = match guarded(|| -> Result<(), Verdict> {
        if !is_expr {
            let ty_ty = kernel::checker::infer(env, &ctx, ty_core.clone())
                .map_err(|e| Verdict::fail("type", Some(e.diagnostic_code()), e.to_string()))?;
            let norm = kernel::checker::whnf(env, ty_ty, kernel::Transparency::Reducible)
                .map_err(|e| Verdict::fail("type", Some(e.diagnostic_code()), e.to_string()))?;
            if !matches!(&*norm, Term::Sort(_)) {
                return Err(Verdict::fail("type", None, "type is not a Sort".into()));
            }
        }
        kernel::checker::check(env, &ctx, val_core.clone(), ty_core.clone()).map_err(|e| {
            let mut v = Verdict::fail("value", Some(e.diagnostic_code()), e.to_string());
            v.variant = Some(type_error_variant(&e));
            v
        })?;
        Ok(())
    }) {
        Ok(Ok(())) => Verdict::pass(),
        Ok(Err(v)) => v,
        Err(panic) => Verdict::fail("panic", None, format!("panic: {}", panic)),
    };

    // ---- Kernel admission on a cloned environment
    let mut def = if is_expr {
        // check_expression_admission: an anonymous `unsafe` definition
        Definition::unsafe_def(name.clone(), ty_core.clone(), val_core.clone())
    } else {
        match input.totality {
            Totality::Partial => {
                Definition::partial(name.clone(), ty_core.clone(), val_core.clone())
            }
            Totality::Unsafe => {
                Definition::unsafe_def(name.clone(), ty_core.clone(), val_core.clone())
            }
            _ => Definition::total(name.clone(), ty_core.clone(), val_core.clone()),
        }
    };
    if !is_expr {
        def.transparency = input.transparency;
        def.noncomputable = input.noncomputable;
    }
    def.capture_modes = capture_modes.clone();
    let mut env2 = env.clone();
    let admit = guarded(|| env2.add_definition(def));
    let admitted = matches!(admit, Ok(Ok(())));
    out.kernel_admit = match admit {
        Ok(Ok(())) => Verdict::pass(),
        Ok(Err(mut e)) => {
            if let TypeError::OwnershipError(o) = &mut e {
                o.resolve_names(&binder_names);
            }
            let code = e.diagnostic_code();
            let mut v = Verdict::fail(admit_phase(code), Some(code), e.to_string());
            v.variant = Some(type_error_variant(&e));
            v
        }
        Err(panic) => Verdict::fail("panic", None, format!("panic: {}", panic)),
    };

    // Driver gate after admission (definitions only): interior-mutability axioms (C0005).
    if admitted && !is_expr {
        if let Some(d) = env2.get_definition(&name) {
            if uses_interior_mutability_axioms(&d.axioms)
                && d.totality != Totality::Unsafe
                && !opts.allow_axioms
            {
                out.gate = Some("C0005".to_string());
            }
        }
    }

    // ---- MIR: on the admitted definition (exactly what the CLI lowers) or, if the kernel
    // rejected it, on the elaborated term in the pre-admission environment.
    let dump = matches!(opts.dump_mir.as_deref(), Some(d) if d == "all" || d == name);
    let mir = if admitted {
        let d = env2
            .get_definition(&name)
            .expect("admitted definition")
            .clone();
        let ty = d.ty.clone();
        let val = d.value.clone().expect("definition value");
        let modes = d.capture_modes.clone();
        guarded(|| {
            run_mir(
                &env2,
                "admitted",
                &name,
                ty,
                val,
                modes,
                term_span_map.clone(),
                dump,
            )
        })
    } else {
        guarded(|| {
            run_mir(
                env,
                "pre_admission",
                &name,
                ty_core.clone(),
                val_core.clone(),
                capture_modes.clone(),
                term_span_map.clone(),
                dump,
            )
        })
    };
    let mir = match mir {
        Ok(r) => r,
        Err(panic) => MirReport {
            env_used: if admitted {
                "admitted"
            } else {
                "pre_admission"
            },
            lowered: None,
            lower_error: None,
            panic: Some(short(&panic)),
            bodies: Vec::new(),
        },
    };
    out.predicted_admitted = admitted && out.gate.is_none() && mir.all_ok();
    out.mir = Some(mir);
    out
}

// ---------------------------------------------------------------------------------------------
// Replay through the CLI driver

struct Replay {
    ok: bool,
    deployed: Vec<String>,
    errors: Vec<(Option<String>, String, Vec<String>)>,
    panic: Option<String>,
}

impl Replay {
    fn json(&self) -> J {
        J::O(vec![
            ("ok", J::B(self.ok)),
            (
                "deployed",
                J::A(self.deployed.iter().map(|d| s(d.clone())).collect()),
            ),
            (
                "errors",
                J::A(
                    self.errors
                        .iter()
                        .map(|(c, m, labels)| {
                            J::O(vec![
                                ("code", opt_s(c.clone())),
                                ("msg", s(m.clone())),
                                (
                                    "labels",
                                    J::A(labels.iter().map(|l| s(l.clone())).collect()),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
            ("panic", opt_s(self.panic.clone())),
        ])
    }
}

/// The source text with every byte outside the kept forms replaced by a space (newlines kept),
/// so byte offsets and line numbers of the kept forms are unchanged.
fn masked_source(src: &str, keep: &[(usize, usize)]) -> String {
    let bytes = src.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    for (i, b) in bytes.iter().enumerate() {
        let kept = keep.iter().any(|(start, end)| i >= *start && i < *end);
        if kept || *b == b'\n' {
            out.push(*b);
        } else {
            out.push(b' ');
        }
    }
    String::from_utf8(out).expect("masking keeps UTF-8 boundaries of kept forms")
}

fn replay(
    src: &str,
    keep: &[(usize, usize)],
    file: &str,
    env: &mut Env,
    expander: &mut Expander,
    options: &PipelineOptions,
) -> Replay {
    let text = masked_source(src, keep);
    let mut diagnostics = DiagnosticCollector::new();
    let result =
        guarded(|| driver::process_code(&text, file, env, expander, options, &mut diagnostics));
    let errors: Vec<(Option<String>, String, Vec<String>)> = diagnostics
        .diagnostics
        .iter()
        .filter(|d| d.level == Level::Error)
        .map(|d| {
            (
                d.code.map(|c| c.to_string()),
                short(&d.message),
                d.labels.iter().map(|(_, label)| short(label)).collect(),
            )
        })
        .collect();
    match result {
        Ok(Ok(processed)) => Replay {
            ok: errors.is_empty(),
            deployed: processed.deployed_definitions,
            errors,
            panic: None,
        },
        Ok(Err(_)) => Replay {
            ok: false,
            deployed: vec![],
            errors,
            panic: None,
        },
        Err(panic) => Replay {
            ok: false,
            deployed: vec![],
            errors,
            panic: Some(short(&panic)),
        },
    }
}

// ---------------------------------------------------------------------------------------------

fn head_symbol(node: &Syntax) -> Option<String> {
    match &node.kind {
        SyntaxKind::List(items) if !items.is_empty() => match &items[0].kind {
            SyntaxKind::Symbol(sym) => Some(sym.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Names of the macros defined in this file (`defmacro` forms).
fn file_macro_names(nodes: &[Syntax]) -> Vec<String> {
    let mut names = Vec::new();
    for node in nodes {
        if head_symbol(node).as_deref() == Some("defmacro") {
            if let SyntaxKind::List(items) = &node.kind {
                if let Some(SyntaxKind::Symbol(name)) = items.get(1).map(|i| &i.kind) {
                    names.push(name.clone());
                }
            }
        }
    }
    names
}

/// File-local macros called (as a list head, anywhere) in a form, sorted and deduplicated.
fn macros_called(node: &Syntax, macros: &[String]) -> Vec<String> {
    fn walk(node: &Syntax, macros: &[String], out: &mut Vec<String>) {
        if let SyntaxKind::List(items) = &node.kind {
            if let Some(SyntaxKind::Symbol(head)) = items.first().map(|i| &i.kind) {
                if macros.contains(head) && !out.contains(head) {
                    out.push(head.clone());
                }
            }
            for item in items {
                walk(item, macros, out);
            }
        }
    }
    let mut out = Vec::new();
    if head_symbol(node).as_deref() != Some("defmacro") {
        walk(node, macros, &mut out);
    }
    out.sort();
    out
}

const DECL_KEYWORDS: &[&str] = &[
    "def",
    "partial",
    "unsafe",
    "noncomputable",
    "opaque",
    "axiom",
    "inductive",
    "instance",
    "defmacro",
    "module",
    "import",
    "open",
    "import-classical",
    "structure",
    "transparent",
];

fn run_file(opts: &Opts) {
    let file = opts.file.clone();
    let backend = match opts.backend {
        Backend::Dynamic => "dynamic",
        Backend::Typed => "typed",
    };
    let file_record = |fields: Vec<(&'static str, J)>| {
        let mut all = vec![
            ("record", s("file")),
            ("file", s(file.clone())),
            ("backend", s(backend)),
        ];
        all.extend(fields);
        emit(J::O(all));
    };

    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            file_record(vec![("status", s("io_error")), ("msg", s(e.to_string()))]);
            return;
        }
    };

    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    if let Err(e) = load_prelude(&mut env, &mut expander, opts.backend) {
        file_record(vec![("status", s("prelude_error")), ("msg", s(short(&e)))]);
        return;
    }
    expander.set_macro_boundary_policy(if opts.macro_boundary_warn {
        MacroBoundaryPolicy::Warn
    } else {
        MacroBoundaryPolicy::Deny
    });
    env.set_allow_redefinition(opts.allow_redefine);
    let options = PipelineOptions {
        show_types: false,
        show_eval: false,
        verbose: false,
        collect_artifacts: false,
        panic_free: false,
        require_axiom_tags: false,
        allow_axioms: opts.allow_axioms,
        prelude_frozen: true,
        allow_redefine: opts.allow_redefine,
    };
    let whole = [(0usize, src.len())];

    // 1. Parse (a parse error rejects the whole file in the CLI).
    let nodes = match Parser::new(&src).parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            let r = replay(&src, &whole, &file, &mut env, &mut expander, &options);
            file_record(vec![
                ("status", s("parse_error")),
                ("code", s(e.diagnostic_code())),
                ("msg", s(short(&e.to_string()))),
                ("cli", r.json()),
            ]);
            return;
        }
    };
    let spans: Vec<(usize, usize)> = nodes.iter().map(|n| (n.span.start, n.span.end)).collect();
    let local_macros = file_macro_names(&nodes);

    // 2. Macro imports are extracted from the whole file before expansion (apply_macro_imports).
    let module_id = driver::module_id_for_source(&file);
    let import_nodes: Vec<usize> = (0..nodes.len())
        .filter(|i| head_symbol(&nodes[*i]).as_deref() == Some("import-macros"))
        .collect();
    if !import_nodes.is_empty() {
        let keep: Vec<(usize, usize)> = import_nodes.iter().map(|i| spans[*i]).collect();
        let r = replay(&src, &keep, &file, &mut env, &mut expander, &options);
        emit(J::O(vec![
            ("record", s("form")),
            ("file", s(file.clone())),
            ("kind", s("import-macros")),
            ("cli", r.json()),
        ]));
    }
    expander.enter_module(module_id);

    // 3. Expand every form into a declaration first, like process_code_inner (an expansion
    //    error anywhere rejects the whole file before any declaration is processed).
    let mut decls: Vec<(usize, Option<Declaration>)> = Vec::new();
    let mut expansion_error: Option<(usize, String, String)> = None;
    {
        let mut parser = DeclarationParser::new(&mut expander);
        for (i, node) in nodes.iter().enumerate() {
            if import_nodes.contains(&i) {
                continue;
            }
            match guarded(|| parser.parse(vec![node.clone()])) {
                Ok(Ok(mut parsed)) => decls.push((i, parsed.pop())),
                Ok(Err(e)) => {
                    expansion_error =
                        Some((i, e.diagnostic_code().to_string(), short(&e.to_string())));
                    break;
                }
                Err(panic) => {
                    expansion_error = Some((i, "panic".to_string(), short(&panic)));
                    break;
                }
            }
        }
    }
    let _ = expander.take_pending_diagnostics();
    if let Some((i, code, msg)) = expansion_error {
        let r = replay(&src, &whole, &file, &mut env, &mut expander, &options);
        file_record(vec![
            ("status", s("expansion_error")),
            ("form_index", J::N(i as i64)),
            ("line", J::N(nodes[i].span.line as i64)),
            ("code", s(code)),
            ("msg", s(msg)),
            ("cli", r.json()),
        ]);
        return;
    }
    file_record(vec![
        ("status", s("ok")),
        ("forms", J::N(nodes.len() as i64)),
    ]);

    // 4. Analyse and replay every form in order.
    let mut res = Resolution::default();
    let mut resolution_forms: Vec<usize> = Vec::new();
    let mut n_defs = 0i64;
    let mut n_inconsistent = 0i64;
    let mut cli_errors = 0i64;
    for (i, decl) in decls {
        let node = &nodes[i];
        let head = head_symbol(node);
        let via_macro = head
            .as_ref()
            .filter(|h| !DECL_KEYWORDS.contains(&h.as_str()))
            .cloned();
        let macros = J::A(
            macros_called(node, &local_macros)
                .into_iter()
                .map(J::S)
                .collect(),
        );
        let mut keep: Vec<(usize, usize)> = resolution_forms.iter().map(|j| spans[*j]).collect();
        keep.push(spans[i]);

        let input = match &decl {
            Some(Declaration::Def {
                name,
                ty,
                val,
                totality,
                transparency,
                noncomputable,
            }) => Some(DefInput {
                name: name.clone(),
                kind: match totality {
                    Totality::Partial => "partial",
                    Totality::Unsafe => "unsafe",
                    _ => "def",
                },
                ty: Some(ty.clone()),
                val: val.clone(),
                totality: *totality,
                transparency: *transparency,
                noncomputable: *noncomputable,
            }),
            Some(Declaration::Expr(term)) => Some(DefInput {
                name: "<expr>".to_string(),
                kind: "expr",
                ty: None,
                val: term.clone(),
                totality: Totality::Unsafe,
                transparency: Transparency::Reducible,
                noncomputable: false,
            }),
            _ => None,
        };

        match input {
            Some(input) => {
                n_defs += 1;
                let kind = input.kind;
                let source_name = input.name.clone();
                let analysis = match guarded(|| analyze(&env, &res, input, opts)) {
                    Ok(a) => a,
                    Err(panic) => DefAnalysis {
                        name: source_name.clone(),
                        elab: Verdict::fail("panic", None, format!("panic: {}", panic)),
                        kernel_typing: Verdict::na(),
                        kernel_admit: Verdict::na(),
                        gate: None,
                        mir: None,
                        predicted_admitted: false,
                    },
                };
                let r = replay(&src, &keep, &file, &mut env, &mut expander, &options);
                if !r.ok {
                    cli_errors += r.errors.len().max(1) as i64;
                }
                let cli_admitted = if kind == "expr" {
                    r.ok
                } else {
                    r.deployed.contains(&analysis.name)
                };
                let consistent = cli_admitted == analysis.predicted_admitted;
                if !consistent {
                    n_inconsistent += 1;
                }
                emit(J::O(vec![
                    ("record", s("def")),
                    ("file", s(file.clone())),
                    ("backend", s(backend)),
                    ("form_index", J::N(i as i64)),
                    ("line", J::N(node.span.line as i64)),
                    ("name", s(analysis.name.clone())),
                    ("kind", s(kind)),
                    ("via_macro", opt_s(via_macro)),
                    ("macros_called", macros),
                    ("elab", analysis.elab.json()),
                    ("kernel_typing", analysis.kernel_typing.json()),
                    ("kernel_admit", analysis.kernel_admit.json()),
                    (
                        "kernel_ownership",
                        s(kernel_ownership_from_admit(&analysis.kernel_admit)),
                    ),
                    ("gate", opt_s(analysis.gate.clone())),
                    (
                        "mir",
                        analysis.mir.as_ref().map(|m| m.json()).unwrap_or(J::Null),
                    ),
                    ("predicted_admitted", J::B(analysis.predicted_admitted)),
                    ("cli_admitted", J::B(cli_admitted)),
                    ("consistent", J::B(consistent)),
                    ("cli", r.json()),
                ]));
            }
            None => {
                let kind = match &decl {
                    None => "empty",
                    Some(Declaration::Axiom { .. }) => "axiom",
                    Some(Declaration::Inductive { .. }) => "inductive",
                    Some(Declaration::Instance { .. }) => "instance",
                    Some(Declaration::DefMacro { .. }) => "defmacro",
                    Some(Declaration::Module { .. }) => "module",
                    Some(Declaration::ImportModule { .. }) => "import",
                    Some(Declaration::OpenModule { .. }) => "open",
                    Some(Declaration::ImportClassical) => "import-classical",
                    _ => "other",
                };
                let name = match &decl {
                    Some(Declaration::Axiom { name, .. })
                    | Some(Declaration::Inductive { name, .. })
                    | Some(Declaration::DefMacro { name, .. })
                    | Some(Declaration::Module { name }) => Some(name.clone()),
                    _ => None,
                };
                let r = replay(&src, &keep, &file, &mut env, &mut expander, &options);
                if !r.ok {
                    cli_errors += r.errors.len().max(1) as i64;
                }
                // Mirror the driver's name-resolution state for later forms.
                match &decl {
                    Some(Declaration::Module { name }) => {
                        if res.current_module.is_none() {
                            res.current_module = Some(name.clone());
                        }
                        resolution_forms.push(i);
                    }
                    Some(Declaration::ImportModule { module, alias }) => {
                        let alias = alias.clone().unwrap_or_else(|| {
                            module
                                .rsplit('.')
                                .next()
                                .unwrap_or(module.as_str())
                                .to_string()
                        });
                        if !res.imported.iter().any(|(a, m)| a == &alias && m == module) {
                            res.imported.push((alias, module.clone()));
                        }
                        resolution_forms.push(i);
                    }
                    Some(Declaration::OpenModule { target }) => {
                        res.open(target);
                        resolution_forms.push(i);
                    }
                    _ => {}
                }
                emit(J::O(vec![
                    ("record", s("form")),
                    ("file", s(file.clone())),
                    ("form_index", J::N(i as i64)),
                    ("line", J::N(node.span.line as i64)),
                    ("kind", s(kind)),
                    ("name", opt_s(name)),
                    ("via_macro", opt_s(via_macro)),
                    ("macros_called", macros),
                    ("cli", r.json()),
                ]));
            }
        }
    }
    emit(J::O(vec![
        ("record", s("end")),
        ("file", s(file.clone())),
        ("backend", s(backend)),
        ("defs", J::N(n_defs)),
        ("inconsistent", J::N(n_inconsistent)),
        ("cli_errors", J::N(cli_errors)),
    ]));
}

fn main() {
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(2);
        }
    };
    if let Err(err) = cli::configure_defeq_fuel(None) {
        eprintln!("invalid LRL_DEFEQ_FUEL: {:?}", err);
        std::process::exit(2);
    }
    install_panic_hook();
    // A larger stack than the CLI's main thread, so that one deep term does not abort the
    // remaining records of a file (documented in the README).
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || run_file(&opts))
        .expect("spawn worker thread");
    if handle.join().is_err() {
        std::process::exit(3);
    }
}
