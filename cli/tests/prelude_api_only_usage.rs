use std::fs;
use std::path::{Path, PathBuf};

fn collect_lrl_files(root: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(root) {
        Ok(entries) => entries,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_lrl_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("lrl") {
            out.push(path);
        }
    }
}

#[test]
fn lrl_programs_do_not_reference_backend_impl_preludes() {
    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cli crate must be inside workspace root");
    let mut files = Vec::new();
    collect_lrl_files(&workspace_root.join("tests"), &mut files);
    collect_lrl_files(&workspace_root.join("code_examples"), &mut files);

    let mut violations = Vec::new();
    for file in files {
        let content = match fs::read_to_string(&file) {
            Ok(content) => content,
            Err(_) => continue,
        };
        if content.contains("prelude_impl_dynamic.lrl")
            || content.contains("prelude_impl_typed.lrl")
        {
            violations.push(file.display().to_string());
        }
    }

    assert!(
        violations.is_empty(),
        "LRL programs must target prelude_api only, but found backend impl prelude references in:\n{}",
        violations.join("\n")
    );
}
