use std::fs;
use std::path::PathBuf;

#[test]
fn core_calculus_spec_mentions_fnmut() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("docs")
        .join("spec")
        .join("core_calculus.md");
    let contents = fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("Failed to read {}: {}", path.display(), err));

    assert!(
        contents.contains("FnMut"),
        "core_calculus spec should mention FnMut; missing in {}",
        path.display()
    );
}
