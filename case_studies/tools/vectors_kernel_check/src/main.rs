//! Kernel-only checks for case study A (`case_studies/lrl/vectors.lrl`).
//!
//! Run from the repository root (the prelude is found relative to the current directory):
//!
//!     cargo run --manifest-path case_studies/tools/vectors_kernel_check/Cargo.toml -- \
//!         case_studies/lrl/vectors.lrl
//!
//! 1. Loads the prelude stack of `lrl run` (dynamic backend) and processes `vectors.lrl` with
//!    the CLI driver (`cli::driver::process_code`: parse, expand, elaborate, kernel admission
//!    via `Env::add_definition`, MIR checks), printing every diagnostic.
//! 2. For every theorem of the file: prints the sort of its statement as inferred by the kernel
//!    (`kernel::checker::infer`, then `whnf`; `Prop` = `Sort 0`, so its value is a proof), its
//!    totality, `noncomputable` flag and the axiom set the kernel recorded for it, and re-checks
//!    its value against its type with the kernel type checker (`kernel::checker::check`) in an
//!    empty context. As a control, the types of two program definitions (`vhead`, `vreverse`)
//!    must not be propositions.
//! 3. Submits FALSE statements directly to the kernel, bypassing the elaborator: the admitted
//!    proof term of a true theorem (or a `refl` term) paired with a false type, via
//!    `Env::add_definition` on a clone of the environment. Each false statement must be rejected;
//!    each control (the same value with the true type) must be accepted.
//!
//! Only public APIs are used; nothing in the compiler is changed.

use cli::driver::{self, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use frontend::surface::Declaration;
use kernel::ast::Definition;
use kernel::checker::{Context, Env};
use std::rc::Rc;

const THEOREMS: &[&str] = &[
    "cong",
    "sym",
    "trans",
    "vreverse_vsnoc",
    "vreverse_involutive",
    "vreverse_injective",
    "v3_reverse_twice",
];

/// [1, 2] and [2, 1] with every implicit argument written out.
const L12: &str = "(vcons {Nat} {1} 1 (vcons {Nat} {0} 2 (vnil {Nat})))";
const L21: &str = "(vcons {Nat} {1} 2 (vcons {Nat} {0} 1 (vnil {Nat})))";

const VSNOC_TRUE: &str = "(pi {A (sort 1)} (pi {n Nat} (pi v (Vec A n) (pi x A \
     (Eq (Vec A (succ n)) (vreverse {A} {(succ n)} (vsnoc {A} {n} v x)) \
         (vcons {A} {n} x (vreverse {A} {n} v)))))))";
// Wrong right-hand side: `vcons x v` instead of `vcons x (vreverse v)`.
const VSNOC_FALSE: &str = "(pi {A (sort 1)} (pi {n Nat} (pi v (Vec A n) (pi x A \
     (Eq (Vec A (succ n)) (vreverse {A} {(succ n)} (vsnoc {A} {n} v x)) \
         (vcons {A} {n} x v))))))";
const INVOL_TRUE: &str = "(pi {A (sort 1)} (pi {n Nat} (pi v (Vec A n) \
     (Eq (Vec A n) (vreverse {A} {n} (vreverse {A} {n} v)) v))))";
// Wrong right-hand side: `vreverse v` instead of `v`.
const INVOL_FALSE: &str = "(pi {A (sort 1)} (pi {n Nat} (pi v (Vec A n) \
     (Eq (Vec A n) (vreverse {A} {n} (vreverse {A} {n} v)) (vreverse {A} {n} v)))))";

enum Value {
    /// The value of a definition admitted from vectors.lrl.
    Admitted(&'static str),
    /// A surface term, elaborated against the given (true) type.
    Elaborated { term: String, ty: String },
}

struct Check {
    label: &'static str,
    ty: String,
    value: Value,
    expect_accept: bool,
}

fn checks() -> Vec<Check> {
    vec![
        Check {
            label: "control: proof of vreverse_vsnoc with its own statement",
            ty: VSNOC_TRUE.to_string(),
            value: Value::Admitted("vreverse_vsnoc"),
            expect_accept: true,
        },
        Check {
            label: "false: proof of vreverse_vsnoc for `vreverse (vsnoc v x) = vcons x v`",
            ty: VSNOC_FALSE.to_string(),
            value: Value::Admitted("vreverse_vsnoc"),
            expect_accept: false,
        },
        Check {
            label: "control: proof of vreverse_involutive with its own statement",
            ty: INVOL_TRUE.to_string(),
            value: Value::Admitted("vreverse_involutive"),
            expect_accept: true,
        },
        Check {
            label: "false: proof of vreverse_involutive for `vreverse (vreverse v) = vreverse v`",
            ty: INVOL_FALSE.to_string(),
            value: Value::Admitted("vreverse_involutive"),
            expect_accept: false,
        },
        Check {
            label: "control: refl [2, 1] for `vreverse [1, 2] = [2, 1]`",
            ty: format!("(Eq (Vec Nat 2) (vreverse {{Nat}} {{2}} {L12}) {L21})"),
            value: Value::Elaborated {
                term: format!("(refl (Vec Nat 2) {L21})"),
                ty: format!("(Eq (Vec Nat 2) {L21} {L21})"),
            },
            expect_accept: true,
        },
        Check {
            label: "false: refl [1, 2] for `vreverse [1, 2] = [1, 2]`",
            ty: format!("(Eq (Vec Nat 2) (vreverse {{Nat}} {{2}} {L12}) {L12})"),
            value: Value::Elaborated {
                term: format!("(refl (Vec Nat 2) {L12})"),
                ty: format!("(Eq (Vec Nat 2) {L12} {L12})"),
            },
            expect_accept: false,
        },
    ]
}

fn short(s: &str, max: usize) -> String {
    let one_line = s.split_whitespace().collect::<Vec<_>>().join(" ");
    if one_line.chars().count() > max {
        format!("{} ...", one_line.chars().take(max).collect::<String>())
    } else {
        one_line
    }
}

/// The sort of a statement, computed by the kernel: `Prop` when the kernel infers `Sort 0` for
/// it (so that its values are proofs), otherwise the inferred sort or the error.
fn statement_sort(env: &Env, ty: &Rc<kernel::ast::Term>) -> String {
    let inferred = kernel::checker::infer(env, &Context::new(), ty.clone())
        .and_then(|s| kernel::checker::whnf(env, s, kernel::ast::Transparency::All));
    match inferred {
        Ok(s) => match &*s {
            kernel::ast::Term::Sort(level) => {
                if matches!(
                    kernel::ast::normalize_level(level.clone()),
                    kernel::ast::Level::Zero
                ) {
                    "Prop".to_string()
                } else {
                    format!("Sort({:?})", kernel::ast::normalize_level(level.clone()))
                }
            }
            other => format!("not-a-sort({})", short(&format!("{:?}", other), 60)),
        },
        Err(e) => format!("error({})", e.diagnostic_code()),
    }
}

/// Parses `(def NAME TYPE VALUE)` and returns the surface type and value.
fn parse_def(
    src: &str,
    expander: &mut Expander,
) -> (
    frontend::surface::SurfaceTerm,
    frontend::surface::SurfaceTerm,
) {
    let nodes = frontend::parser::Parser::new(src)
        .parse()
        .expect("parse check source");
    let decls = frontend::declaration_parser::DeclarationParser::new(expander)
        .parse(nodes)
        .expect("parse check declaration");
    for decl in decls {
        if let Declaration::Def { ty, val, .. } = decl {
            return (ty, val);
        }
    }
    panic!("no definition in check source: {}", src);
}

fn elaborate_type(env: &Env, expander: &mut Expander, ty_src: &str) -> Rc<kernel::ast::Term> {
    let (ty, _) = parse_def(&format!("(def check_type {} unit)", ty_src), expander);
    let mut elab = frontend::elaborator::Elaborator::new(env);
    let (t, _) = elab.infer_type(ty).expect("elaborate check type");
    elab.instantiate_metas(&t)
}

fn elaborate_value(
    env: &Env,
    expander: &mut Expander,
    term_src: &str,
    ty_src: &str,
) -> Rc<kernel::ast::Term> {
    let (ty, val) = parse_def(
        &format!("(def check_value {} {})", ty_src, term_src),
        expander,
    );
    let mut elab = frontend::elaborator::Elaborator::new(env);
    let (t, _) = elab.infer_type(ty).expect("elaborate value type");
    let t = elab.instantiate_metas(&t);
    let v = elab.check(val, &t).expect("elaborate value");
    elab.solve_constraints().expect("solve constraints");
    elab.instantiate_metas(&v)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let file = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| "case_studies/lrl/vectors.lrl".to_string());

    // 1. Prelude stack of `lrl run` (dynamic backend), then the case-study file.
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    let prelude_opts = PipelineOptions {
        allow_axioms: true,
        ..Default::default()
    };
    let mut modules = Vec::new();
    env.set_allow_reserved_primitives(true);
    for path in cli::compiler::prelude_stack_for_backend(cli::compiler::BackendMode::Dynamic) {
        let content = std::fs::read_to_string(path).expect("read prelude file");
        let module = driver::module_id_for_source(path);
        cli::set_prelude_macro_boundary_allowlist(&mut expander, &module);
        if !modules.is_empty() {
            expander.set_default_imports(modules.clone());
        }
        let mut diags = DiagnosticCollector::new();
        let _ = driver::process_code(
            &content,
            path,
            &mut env,
            &mut expander,
            &prelude_opts,
            &mut diags,
        );
        expander.clear_macro_boundary_allowlist();
        modules.push(module);
    }
    env.set_allow_reserved_primitives(false);
    expander.set_default_imports(modules);

    let src = std::fs::read_to_string(&file).expect("read case-study file");
    let opts = PipelineOptions {
        prelude_frozen: true,
        ..Default::default()
    };
    let mut diags = DiagnosticCollector::new();
    let processed = driver::process_code(&src, &file, &mut env, &mut expander, &opts, &mut diags);
    println!("FILE {}", file);
    println!("DIAGNOSTICS {}", diags.diagnostics.len());
    for d in &diags.diagnostics {
        println!("DIAG {}", short(&d.message_with_code(), 300));
    }
    if let Ok(p) = &processed {
        println!("DEPLOYED {}", p.deployed_definitions.join(" "));
    }

    // 2. The admitted theorems: totality, noncomputable flag, axiom set, independent re-check.
    let mut failures = 0usize;
    for name in THEOREMS {
        match env.get_definition(name) {
            None => {
                println!("THEOREM {} MISSING (not admitted)", name);
                failures += 1;
            }
            Some(def) => {
                let recheck = match &def.value {
                    Some(v) => match kernel::checker::check(
                        &env,
                        &Context::new(),
                        v.clone(),
                        def.ty.clone(),
                    ) {
                        Ok(_) => "ok".to_string(),
                        Err(e) => {
                            failures += 1;
                            format!("{} {}", e.diagnostic_code(), short(&e.to_string(), 160))
                        }
                    },
                    None => {
                        failures += 1;
                        "no value".to_string()
                    }
                };
                if !def.axioms.is_empty() || def.noncomputable {
                    failures += 1;
                }
                let sort = statement_sort(&env, &def.ty);
                if sort != "Prop" {
                    failures += 1;
                }
                println!(
                    "THEOREM {} statement_sort={} totality={:?} noncomputable={} axioms=[{}] kernel_recheck={}",
                    name,
                    sort,
                    def.totality,
                    def.noncomputable,
                    def.axioms.join(","),
                    recheck
                );
            }
        }
    }

    // Control for the sort check: the types of program definitions are not propositions.
    for name in ["vhead", "vreverse"] {
        let sort = match env.get_definition(name) {
            Some(def) => statement_sort(&env, &def.ty),
            None => "missing".to_string(),
        };
        let matched = sort != "Prop" && sort != "missing";
        if !matched {
            failures += 1;
        }
        println!(
            "SORT control: type of program definition {} | expected=not Prop | observed={} | match={}",
            name,
            sort,
            if matched { "yes" } else { "NO" }
        );
    }

    // 3. False statements (and controls) submitted directly to the kernel.
    for c in checks() {
        let ty = elaborate_type(&env, &mut expander, &c.ty);
        let value = match &c.value {
            Value::Admitted(name) => env
                .get_definition(name)
                .and_then(|d| d.value.clone())
                .unwrap_or_else(|| panic!("{} was not admitted", name)),
            Value::Elaborated { term, ty } => elaborate_value(&env, &mut expander, term, ty),
        };
        let mut env2 = env.clone();
        let result = env2.add_definition(Definition::total("kernel_check".to_string(), ty, value));
        let observed = match &result {
            Ok(()) => "accepted".to_string(),
            Err(e) => format!(
                "rejected {} {}",
                e.diagnostic_code(),
                short(&e.to_string(), 200)
            ),
        };
        let matched = result.is_ok() == c.expect_accept;
        if !matched {
            failures += 1;
        }
        println!(
            "CHECK {} | expected={} | observed={} | match={}",
            c.label,
            if c.expect_accept {
                "accepted"
            } else {
                "rejected"
            },
            observed,
            if matched { "yes" } else { "NO" }
        );
    }

    println!("FAILURES {}", failures);
    if failures > 0 {
        std::process::exit(1);
    }
}
