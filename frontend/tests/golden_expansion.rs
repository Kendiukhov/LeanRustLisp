use frontend::parser::Parser;
use frontend::macro_expander::Expander;
use insta::assert_snapshot;
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

fn expand_source(source: &str) -> String {
    let mut parser = Parser::new(source);
    let syntax_list = parser.parse().expect("Failed to parse");
    let mut expander = Expander::new();

    let mut results = String::new();
    for syntax in syntax_list {
        match expander.expand(syntax) {
            Ok(Some(term)) => {
                results.push_str(&format!("{:?}\n", term));
            }
            Ok(None) => {
                results.push_str("Macro defined\n");
            }
            Err(e) => {
                results.push_str(&format!("Error: {}\n", e));
            }
        }
    }
    results
}

#[test]
fn golden_macro_expansion_suite() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("cli")
        .join("tests")
        .join("golden")
        .join("frontend");

    let files = collect_lrl_files(&root);
    assert!(!files.is_empty(), "No .lrl files found in {:?}", root);

    for path in files {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("Failed to read {:?}", path));
        let output = expand_source(&source);
        let output_second = expand_source(&source);
        assert_eq!(output, output_second, "Macro expansion should be deterministic");

        let snap_name = snapshot_name(&root, &path);
        assert_snapshot!(snap_name, output);
    }
}
