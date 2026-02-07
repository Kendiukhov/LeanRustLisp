use cli::compiler::{
    prelude_stack_for_backend, BackendMode, PRELUDE_API_PATH, PRELUDE_IMPL_DYNAMIC_PATH,
    PRELUDE_IMPL_TYPED_PATH,
};
use cli::driver::{module_id_for_source, process_code, PipelineOptions};
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use kernel::checker::Env;
use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;

fn load_prelude_stack(paths: &[&str]) -> Env {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);

    let options = PipelineOptions {
        panic_free: false,
        require_axiom_tags: false,
        allow_axioms: true,
        prelude_frozen: false,
        allow_redefine: false,
        ..Default::default()
    };

    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);

    let mut diagnostics = DiagnosticCollector::new();
    let mut prelude_modules = Vec::new();
    for rel_path in paths {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join(rel_path);
        let path_str = path
            .to_str()
            .expect("prelude path should be valid UTF-8")
            .to_string();
        let content = fs::read_to_string(&path).expect("failed to read prelude file");
        let prelude_module = module_id_for_source(&path_str);
        cli::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
        process_code(
            &content,
            &path_str,
            &mut env,
            &mut expander,
            &options,
            &mut diagnostics,
        )
        .expect("prelude processing failed");
        expander.clear_macro_boundary_allowlist();
        prelude_modules.push(prelude_module);
    }

    assert!(
        !diagnostics.has_errors(),
        "prelude load emitted errors: {:?}",
        diagnostics.diagnostics
    );

    env.set_allow_reserved_primitives(allow_reserved);
    env.init_marker_registry()
        .expect("marker registry initialization should succeed");
    expander.set_default_imports(prelude_modules);
    env
}

fn assert_api_surface(env: &Env) {
    for name in [
        "Nat", "Bool", "False", "List", "VecDyn", "Slice", "Array", "RefCell", "Mutex", "Atomic",
        "Comp", "Eq",
    ] {
        assert!(
            env.get_inductive(name).is_some(),
            "expected API inductive '{}'",
            name
        );
    }

    for name in [
        "add",
        "append",
        "not",
        "if_nat",
        "and",
        "or",
        "print_nat",
        "print_bool",
        "Shared",
        "Mut",
        "Ref",
        "borrow_shared",
        "borrow_mut",
        "index_vec_dyn",
        "index_slice",
        "index_array",
    ] {
        assert!(
            env.get_definition(name).is_some(),
            "expected API definition '{}'",
            name
        );
    }
}

fn extract_def_names(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim_start();
            let rest = trimmed.strip_prefix("(def ")?;
            let mut parts = rest.split_whitespace();
            let first = parts.next()?;
            let name = match first {
                "opaque" | "transparent" | "partial" | "unsafe" | "noncomputable" => parts.next()?,
                _ => first,
            };
            Some(name.trim_end_matches(')').to_string())
        })
        .collect()
}

#[test]
fn prelude_stack_constants_are_expected() {
    assert_eq!(PRELUDE_API_PATH, "stdlib/prelude_api.lrl");
    assert_eq!(PRELUDE_IMPL_DYNAMIC_PATH, "stdlib/prelude_impl_dynamic.lrl");
    assert_eq!(PRELUDE_IMPL_TYPED_PATH, "stdlib/prelude_impl_typed.lrl");
    assert_eq!(
        prelude_stack_for_backend(BackendMode::Dynamic),
        &[PRELUDE_API_PATH, PRELUDE_IMPL_DYNAMIC_PATH]
    );
    assert_eq!(
        prelude_stack_for_backend(BackendMode::Typed),
        &[PRELUDE_API_PATH, PRELUDE_IMPL_TYPED_PATH]
    );
}

#[test]
fn prelude_api_conformance_dynamic_stack() {
    let env = load_prelude_stack(prelude_stack_for_backend(BackendMode::Dynamic));
    assert_api_surface(&env);

    for name in ["Dyn", "EvalCap", "eval"] {
        assert!(
            env.get_definition(name).is_some() || env.get_inductive(name).is_some(),
            "expected dynamic platform symbol '{}'",
            name
        );
    }
}

#[test]
fn prelude_api_conformance_typed_stack() {
    let env = load_prelude_stack(prelude_stack_for_backend(BackendMode::Typed));
    assert_api_surface(&env);

    for name in ["Dyn", "EvalCap", "eval"] {
        assert!(
            env.get_definition(name).is_some() || env.get_inductive(name).is_some(),
            "expected typed platform symbol '{}'",
            name
        );
    }
}

#[test]
fn prelude_impl_layers_stay_small_and_platform_only() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let dynamic_impl = fs::read_to_string(root.join(PRELUDE_IMPL_DYNAMIC_PATH))
        .expect("failed to read dynamic impl prelude");
    let typed_impl = fs::read_to_string(root.join(PRELUDE_IMPL_TYPED_PATH))
        .expect("failed to read typed impl prelude");

    let dynamic_def_names = extract_def_names(&dynamic_impl);
    let typed_def_names = extract_def_names(&typed_impl);
    let allowed_platform_defs: HashSet<&str> = HashSet::from(["eval"]);

    assert!(
        dynamic_def_names
            .iter()
            .all(|name| allowed_platform_defs.contains(name.as_str())),
        "dynamic impl prelude should define platform-only names; found defs: {:?}",
        dynamic_def_names
    );
    assert!(
        typed_def_names
            .iter()
            .all(|name| allowed_platform_defs.contains(name.as_str())),
        "typed impl prelude should define platform-only names; found defs: {:?}",
        typed_def_names
    );

    for forbidden in [
        "(def add",
        "(def append",
        "(def not",
        "(def if_nat",
        "(def and",
        "(def or",
        "(def length",
        "(def map",
        "(def foldl",
        "(def foldr",
        "(def filter",
        "(def reverse",
    ] {
        assert!(
            !dynamic_impl.contains(forbidden),
            "dynamic impl should not carry shared stdlib logic: {}",
            forbidden
        );
        assert!(
            !typed_impl.contains(forbidden),
            "typed impl should not carry shared stdlib logic: {}",
            forbidden
        );
    }
}
