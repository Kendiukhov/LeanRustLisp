//! User identifiers that collide with Rust names must not break the generated Rust code.
//!
//! Both backends name generated Rust items after LRL definitions, inductive types and
//! constructors (`mir::codegen::sanitize_name`). A user name that is a Rust keyword (`crate`,
//! `self`, `box`, ...), a primitive type (`u64`, `bool`, `usize`), a standard name the
//! generated code uses unqualified (`Box`, `Rc`, `String`, `Clone`, `Fn`, `Some`, `Ok`), or a
//! name of the generated runtime (`LrlCallable`, `runtime_index`, `rec_Nat_entry_0`,
//! `__lrl_main`, generic parameters `T0`, ...) is mangled with the prefix `lrl_`. Before, each of
//! these names made rustc reject the typed backend's output. The dynamic backend also named its
//! recursor functions after the raw inductive name, which is not a Rust identifier for a
//! module-qualified inductive.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate must be inside the workspace")
        .to_path_buf()
}

/// Compiles `source` with `compile --backend <backend>` from the repository root, runs the
/// binary and returns (compile succeeded, binary stdout, compiler output).
fn compile_and_run(prefix: &str, source: &str, backend: &str) -> (bool, String, String) {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "lrl_rust_name_mangling_{}_{}_{}",
        prefix,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join(format!("{}.lrl", prefix));
    fs::write(&file, source).expect("write program");
    let out = dir.join("out_bin");
    let output = Command::new(env!("CARGO_BIN_EXE_cli"))
        .current_dir(repo_root())
        .arg("compile")
        .arg(&file)
        .arg("--backend")
        .arg(backend)
        .arg("-o")
        .arg(&out)
        .output()
        .expect("run cli");
    let compiler_output = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let mut stdout = String::new();
    if output.status.success() && out.exists() {
        let run = Command::new(&out).output().expect("run binary");
        stdout = String::from_utf8_lossy(&run.stdout).to_string();
    }
    let _ = fs::remove_dir_all(&dir);
    (output.status.success(), stdout, compiler_output)
}

fn assert_result(prefix: &str, source: &str, backend: &str, expected: &str) {
    let (ok, stdout, compiler_output) = compile_and_run(prefix, source, backend);
    assert!(
        ok && stdout.lines().any(|line| line.trim() == expected),
        "{} backend: expected `{}`;
binary stdout:
{}
compiler output:
{}",
        backend,
        expected,
        stdout,
        compiler_output
    );
}

const COLLIDING_NAMES: &str = r#"
;; Every name that broke the typed backend's Rust output, in one program.
(inductive Box (sort 1) (ctor mk_box (pi x Nat Box)))
(inductive Rc (sort 1) (ctor mk_rc (pi x Nat Rc)))
(inductive String (sort 1) (ctor mk_string (pi x Nat String)))
(inductive Clone (sort 1) (ctor mk_clone (pi x Nat Clone)))
(inductive Fn (sort 1) (ctor mk_fn (pi x Nat Fn)))
(inductive u64 (sort 1) (ctor mk_u64 (pi x Nat u64)))
(inductive bool (sort 1) (ctor mk_bool (pi x Nat bool)))
(inductive usize (sort 1) (ctor mk_usize (pi x Nat usize)))
(inductive LrlCallable (sort 1) (ctor mk_callable (pi x Nat LrlCallable)))
(inductive LrlRefMut (sort 1) (ctor mk_refmut (pi x Nat LrlRefMut)))
(inductive Wrap (sort 1) (ctor Some (pi x Nat Wrap)) (ctor Ok (pi x Nat Wrap)))
(def unbox (pi b Box Nat) (lam b Box (match b Nat (case (mk_box x) x))))
(def unrc (pi b Rc Nat) (lam b Rc (match b Nat (case (mk_rc x) x))))
(def unstring (pi b String Nat) (lam b String (match b Nat (case (mk_string x) x))))
(def unclone (pi b Clone Nat) (lam b Clone (match b Nat (case (mk_clone x) x))))
(def unfn (pi b Fn Nat) (lam b Fn (match b Nat (case (mk_fn x) x))))
(def unu64 (pi b u64 Nat) (lam b u64 (match b Nat (case (mk_u64 x) x))))
(def unbool (pi b bool Nat) (lam b bool (match b Nat (case (mk_bool x) x))))
(def unusize (pi b usize Nat) (lam b usize (match b Nat (case (mk_usize x) x))))
(def uncallable (pi b LrlCallable Nat) (lam b LrlCallable (match b Nat (case (mk_callable x) x))))
(def unrefmut (pi b LrlRefMut Nat) (lam b LrlRefMut (match b Nat (case (mk_refmut x) x))))
(def unwrap (pi w Wrap Nat) (lam w Wrap (match w Nat (case (Some x) x) (case (Ok x) (succ x)))))
(def __lrl_main (pi n Nat Nat) (lam n Nat (succ n)))
(def box (pi n Nat Nat) (lam n Nat (succ n)))
(def crate (pi n Nat Nat) (lam n Nat (succ n)))
(def self (pi n Nat Nat) (lam n Nat (succ n)))
(def Self (pi n Nat Nat) (lam n Nat (succ n)))
(def super (pi n Nat Nat) (lam n Nat (succ n)))
(def rec_Nat_entry_0 (pi n Nat Nat) (lam n Nat (succ n)))
(def runtime_bounds_check (pi n Nat Nat) (lam n Nat (succ n)))
(def runtime_index (pi n Nat Nat) (lam n Nat (succ n)))
(def T0 (pi n Nat Nat) (lam n Nat (succ n)))
(def sum_types Nat
  (add (unbox (mk_box 1)) (add (unrc (mk_rc 1)) (add (unstring (mk_string 1)) (add (unclone (mk_clone 1))
  (add (unfn (mk_fn 1)) (add (unu64 (mk_u64 1)) (add (unbool (mk_bool 1)) (add (unusize (mk_usize 1))
  (add (uncallable (mk_callable 1)) (add (unrefmut (mk_refmut 1)) (add (unwrap (Some 1)) (unwrap (Ok 0))))))))))))))
(def sum_defs Nat
  (__lrl_main (box (crate (self (Self (super (rec_Nat_entry_0 (runtime_bounds_check (runtime_index (T0 zero)))))))))))
;; 12 + 10 = 22
(def main Nat (add sum_types sum_defs))
"#;

const MODULE_QUALIFIED_INDUCTIVE: &str = r#"
;; Module-qualified inductive and a user type/ctor/def named like Rust and runtime items.
(module shapes)
(inductive Shape (sort 1) (ctor circle (pi r Nat Shape)) (ctor square (pi s Nat Shape)))
(def area (pi s Shape Nat) (lam s Shape (match s Nat (case (circle r) (add r (add r r))) (case (square x) (add x x)))))
(def main Nat (area (circle 2)))
"#;

#[test]
fn colliding_user_names_compile_with_the_typed_backend() {
    assert_result("names_typed", COLLIDING_NAMES, "typed", "Result: 22");
}

#[test]
fn colliding_user_names_compile_with_the_dynamic_backend() {
    assert_result(
        "names_dynamic",
        COLLIDING_NAMES,
        "dynamic",
        "Result: Nat(22)",
    );
}

#[test]
fn module_qualified_inductive_compiles_with_both_backends() {
    assert_result(
        "module_typed",
        MODULE_QUALIFIED_INDUCTIVE,
        "typed",
        "Result: 6",
    );
    assert_result(
        "module_dynamic",
        MODULE_QUALIFIED_INDUCTIVE,
        "dynamic",
        "Result: Nat(6)",
    );
}
