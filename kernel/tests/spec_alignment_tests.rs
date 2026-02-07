use std::fs;
use std::path::PathBuf;

fn read_spec(path: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(path);
    fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("Failed to read {}: {}", path.display(), err))
}

#[test]
fn core_calculus_spec_mentions_fnmut() {
    let contents = read_spec("docs/spec/core_calculus.md");

    assert!(
        contents.contains("FnMut"),
        "core_calculus spec should mention FnMut; missing in docs/spec/core_calculus.md"
    );
}

#[test]
fn macro_hygiene_specs_use_subset_resolution_consistently() {
    let macro_system = read_spec("docs/spec/macro_system.md");
    let hygiene = read_spec("docs/spec/macros/hygiene.md");

    assert!(
        macro_system.contains("subset"),
        "docs/spec/macro_system.md should describe subset-based hygiene resolution"
    );
    assert!(
        hygiene.contains("subset of the use-site scopes"),
        "docs/spec/macros/hygiene.md should describe subset-based hygiene resolution"
    );
    assert!(
        !macro_system.contains("exactly matches"),
        "docs/spec/macro_system.md should not claim strict exact-match resolution"
    );
}
