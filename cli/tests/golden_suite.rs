use cli::driver::{process_code, Artifact, PipelineOptions};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use insta::assert_snapshot;
use kernel::checker::Env;
use std::fs;
use std::path::{Path, PathBuf};

fn collect_lrl_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut stack = vec![root.to_path_buf()];

    while let Some(dir) = stack.pop() {
        let entries = fs::read_dir(&dir).unwrap_or_else(|_| panic!("Failed to read {:?}", dir));
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(name) = path.file_name().and_then(|s| s.to_str()) {
                if name.starts_with('.') {
                    continue;
                }
            }
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().and_then(|s| s.to_str()) == Some("lrl") {
                files.push(path);
            }
        }
    }

    files.sort();
    files
}

fn format_path(path: &Path) -> String {
    path.components()
        .map(|c| c.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn snapshot_name(root: &Path, path: &Path) -> String {
    let rel = path.strip_prefix(root).unwrap_or(path);
    let mut name = format_path(rel);
    if name.ends_with(".lrl") {
        let len = name.len();
        name.truncate(len - 4);
    }
    name.replace('/', "_")
}

fn render_artifacts(artifacts: &[Artifact]) -> String {
    let mut out = String::new();
    for artifact in artifacts {
        match artifact {
            Artifact::DefEqConfig {
                fuel,
                source,
                transparency,
            } => {
                out.push_str("DefEqConfig\n");
                out.push_str(&format!("  fuel: {}\n", fuel));
                out.push_str(&format!("  source: {}\n", source));
                out.push_str(&format!("  transparency: {:?}\n", transparency));
            }
            Artifact::ElaboratedDef { name, ty, val } => {
                out.push_str(&format!("ElaboratedDef {}\n", name));
                out.push_str(&format!("  ty: {}\n", ty));
                out.push_str(&format!("  val: {}\n", val));
            }
            Artifact::MirBody { name, body } => {
                out.push_str(&format!("MirBody {}\n", name));
                out.push_str(&format!("  {}\n", body));
            }
            Artifact::BorrowCheck {
                name,
                ownership_errors,
                result,
            } => {
                out.push_str(&format!("BorrowCheck {}\n", name));
                if ownership_errors.is_empty() && result.errors.is_empty() {
                    out.push_str("  ok\n");
                } else {
                    for err in ownership_errors {
                        out.push_str(&format!("  ownership error: {}\n", err));
                    }
                    for err in &result.errors {
                        out.push_str(&format!("  borrow error: {}\n", err));
                    }
                }
                out.push_str("  evidence:\n");
                for line in result.evidence().render_lines() {
                    out.push_str(&format!("    {}\n", line));
                }
            }
            Artifact::AxiomDependencies {
                name,
                axioms,
                classical,
            } => {
                out.push_str(&format!("AxiomDependencies {}\n", name));
                out.push_str(&format!("  axioms: {:?}\n", axioms));
                out.push_str(&format!("  classical: {:?}\n", classical));
            }
        }
        out.push('\n');
    }
    if out.is_empty() {
        out.push_str("(no artifacts)\n");
    }
    out
}

fn run_pipeline(
    source: &str,
    filename: &str,
    include_artifacts: bool,
    macro_boundary_warn: bool,
) -> (String, bool) {
    let mut env = Env::new();
    let mut expander = Expander::new();
    env.set_allow_reserved_primitives(true);
    expander.set_macro_boundary_policy(if macro_boundary_warn {
        MacroBoundaryPolicy::Warn
    } else {
        MacroBoundaryPolicy::Deny
    });
    let mut diagnostics = DiagnosticCollector::new();
    let options = PipelineOptions {
        collect_artifacts: true,
        ..Default::default()
    };

    let result = process_code(
        source,
        filename,
        &mut env,
        &mut expander,
        &options,
        &mut diagnostics,
    );

    let errors: Vec<_> = diagnostics
        .diagnostics
        .iter()
        .filter(|d| d.level == Level::Error)
        .filter(|d| !d.message.starts_with("MIR typing error"))
        .collect();
    let has_errors = !errors.is_empty() || result.is_err();

    let mut out = String::new();

    if let Err(err) = &result {
        out.push_str(&format!("DriverError: {:?}\n", err));
    }

    if !errors.is_empty() {
        out.push_str("Diagnostics:\n");
        for diag in errors {
            out.push_str(&format!("- {}: {}\n", diag.level, diag.message_with_code()));
        }
        out.push('\n');
    }

    if include_artifacts {
        if let Ok(result) = result {
            out.push_str(&render_artifacts(&result.artifacts));
        }
    }

    (out, has_errors)
}

fn run_suite(subdir: &str, expect_errors: bool, include_artifacts: bool) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("golden")
        .join(subdir);
    let files = collect_lrl_files(&root);
    assert!(!files.is_empty(), "No .lrl files found in {:?}", root);

    let macro_boundary_warn = subdir == "frontend";
    for path in files {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|_| panic!("Failed to read {:?}", path));
        let rel = path.strip_prefix(&root).unwrap_or(&path);
        let display_name = format_path(rel);

        let (output, has_errors) = run_pipeline(
            &source,
            &display_name,
            include_artifacts,
            macro_boundary_warn,
        );
        if expect_errors {
            assert!(has_errors, "Expected errors for {}", display_name);
        } else {
            if has_errors {
                eprintln!("Unexpected errors for {}:\n{}", display_name, output);
            }
            assert!(!has_errors, "Unexpected errors for {}", display_name);
            let (second, second_errors) = run_pipeline(
                &source,
                &display_name,
                include_artifacts,
                macro_boundary_warn,
            );
            assert!(
                !second_errors,
                "Unexpected errors on second run for {}",
                display_name
            );
            assert_eq!(
                output, second,
                "Pipeline output should be deterministic for {}",
                display_name
            );
        }

        let snap_name = snapshot_name(&root, &path);
        assert_snapshot!(snap_name, output);
    }
}

#[test]
fn golden_kernel_suite() {
    run_suite("kernel", false, true);
}

#[test]
fn golden_frontend_suite() {
    run_suite("frontend", false, true);
}

#[test]
fn golden_mir_suite() {
    run_suite("mir", false, true);
}

#[test]
fn golden_negative_suite() {
    run_suite("negative", true, false);
}
