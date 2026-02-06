use cli::expand::{expand_and_format, load_macros_from_source, ExpandMode};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use insta::assert_snapshot;

fn define_macros(expander: &mut Expander, source: &str) {
    load_macros_from_source(expander, source).expect("Failed to define macro");
}

#[test]
fn expand_single_step_and_full() {
    let macros = "(defmacro m1 () (m2))\n(defmacro m2 () 1)\n";
    let input = "(m1)";

    let mut expander = Expander::new();
    define_macros(&mut expander, macros);
    let single = expand_and_format(input, &mut expander, ExpandMode::SingleStep)
        .expect("Single-step expansion should succeed");
    assert_snapshot!("expand_single_step", single);

    let mut expander = Expander::new();
    define_macros(&mut expander, macros);
    let full = expand_and_format(input, &mut expander, ExpandMode::Full)
        .expect("Full expansion should succeed");
    assert_snapshot!("expand_full", full);
}

#[test]
fn trace_expand_output() {
    let macros = "(defmacro m1 () (m2))\n(defmacro m2 () 1)\n";
    let input = "(m1)";

    let mut expander = Expander::new();
    define_macros(&mut expander, macros);
    let traced = expand_and_format(input, &mut expander, ExpandMode::Trace)
        .expect("Trace expansion should succeed");
    assert_snapshot!("trace_expand", traced);
}

#[test]
fn expand_surface_forms() {
    let macros = r#"
        (defmacro mk_opaque (name ty val) (opaque name ty val))
        (defmacro mk_transparent (name ty val) (transparent name ty val))
        (defmacro mk_eval (code cap) (eval code cap))
        (defmacro mk_import_classical () (import classical))
        (defmacro mk_axiom_classical (name ty) (axiom classical name ty))
    "#;

    let input = "\
(mk_opaque secret Ty Val)
(mk_transparent open Ty Val)
(mk_eval dyn_code dyn_cap)
(mk_import_classical)
(mk_axiom_classical choice (sort 0))";

    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Warn);
    define_macros(&mut expander, macros);
    let full = expand_and_format(input, &mut expander, ExpandMode::Full)
        .expect("Surface-form expansion should succeed");
    assert_snapshot!("expand_surface_forms", full);
}
