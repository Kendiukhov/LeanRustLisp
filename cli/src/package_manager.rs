use crate::compiler;
use crate::driver::{self, PipelineOptions};
use crate::repl;
use anyhow::{anyhow, bail, Context, Result};
use frontend::diagnostics::{DiagnosticCollector, Level};
use frontend::macro_expander::{Expander, MacroBoundaryPolicy};
use frontend::parser::Parser;
use frontend::surface::{Syntax, SyntaxKind};
use kernel::checker::Env;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const MANIFEST_FILE: &str = "lrl.toml";
const LOCK_FILE: &str = "lrl.lock";
const CACHE_FILE: &str = "build/lrl/cache.toml";
const LOCK_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, Default)]
pub struct BuildOptions {
    pub release: bool,
    pub locked: bool,
}

impl BuildOptions {
    fn enforce_lockfile(self) -> bool {
        self.release || self.locked
    }
}

#[derive(Debug, Default)]
pub struct BuildReport {
    pub built: Vec<String>,
    pub skipped: Vec<String>,
    pub lockfile_updated: bool,
}

#[derive(Debug, Deserialize)]
struct RawManifest {
    package: Option<RawPackage>,
    workspace: Option<RawWorkspace>,
    dependencies: Option<BTreeMap<String, RawDependency>>,
}

#[derive(Debug, Deserialize)]
struct RawPackage {
    name: String,
    version: String,
    edition: Option<String>,
    root: Option<String>,
    module: Option<String>,
}

#[derive(Debug, Deserialize)]
struct RawWorkspace {
    members: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
enum RawDependency {
    Path(String),
    Detailed(DependencySpec),
}

impl RawDependency {
    fn into_spec(self) -> DependencySpec {
        match self {
            RawDependency::Path(path) => DependencySpec {
                path: Some(path),
                git: None,
                rev: None,
                version: None,
                package: None,
            },
            RawDependency::Detailed(spec) => spec,
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
struct DependencySpec {
    path: Option<String>,
    git: Option<String>,
    rev: Option<String>,
    version: Option<String>,
    package: Option<String>,
}

#[derive(Debug, Clone)]
struct ResolvedWorkspace {
    root_dir: PathBuf,
    packages: BTreeMap<String, ResolvedPackage>,
    member_ids: Vec<String>,
    topo_order: Vec<String>,
}

#[derive(Debug, Clone)]
struct ResolvedPackage {
    package_id: String,
    name: String,
    version: String,
    edition: String,
    manifest_path: PathBuf,
    root_dir: PathBuf,
    root_module: String,
    entry_file: PathBuf,
    dependencies: Vec<ResolvedDependency>,
}

impl ResolvedPackage {
    fn label(&self) -> String {
        format!("{}@{}", self.name, self.version)
    }
}

#[derive(Debug, Clone)]
struct ResolvedDependency {
    declared_name: String,
    package_name: String,
    package_id: String,
}

#[derive(Debug, Clone)]
enum SourceKind {
    Path(PathBuf),
}

impl SourceKind {
    fn as_lock_source(&self) -> String {
        match self {
            SourceKind::Path(path) => format!("path:{}", path.display()),
        }
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
struct BuildCache {
    package_fingerprints: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
struct Lockfile {
    version: u32,
    package: Vec<LockPackage>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
struct LockPackage {
    package_id: String,
    name: String,
    resolved_version: String,
    source: String,
    content_hash: String,
    dependencies: Vec<String>,
}

#[derive(Debug, Default)]
struct ResolveContext {
    packages: BTreeMap<String, ResolvedPackage>,
    by_manifest: BTreeMap<PathBuf, String>,
    loading: BTreeSet<PathBuf>,
}

struct CompileOutcome {
    last_result: Option<driver::ProcessingResult>,
}

#[derive(Debug, Default)]
struct LockfileStatus {
    updated: bool,
}

pub fn build_workspace(cwd: &Path, options: BuildOptions) -> Result<BuildReport> {
    let workspace_root = find_workspace_root(cwd)?;
    build_workspace_at(&workspace_root, options)
}

pub fn build_workspace_at(root: &Path, options: BuildOptions) -> Result<BuildReport> {
    // Resolve graph + lockfile first so every build operates on a deterministic package set.
    let workspace = resolve_workspace(root)?;
    let lock_status = ensure_lockfile(&workspace, options.enforce_lockfile())?;
    let mut cache = load_build_cache(&workspace.root_dir)?;
    let mut report = BuildReport {
        lockfile_updated: lock_status.updated,
        ..BuildReport::default()
    };
    let mut fingerprint_cache = BTreeMap::new();

    for package_id in &workspace.topo_order {
        let package = workspace
            .packages
            .get(package_id)
            .ok_or_else(|| anyhow!("internal resolver error: unknown package '{}'", package_id))?;
        let fingerprint = package_fingerprint(&workspace, package_id, &mut fingerprint_cache)?;
        let marker = marker_path(&workspace.root_dir, package_id);
        let cached =
            cache.package_fingerprints.get(package_id) == Some(&fingerprint) && marker.exists();

        if cached {
            report.skipped.push(package.label());
            continue;
        }

        compile_package_closure(&workspace, package_id)?;
        if let Some(parent) = marker.parent() {
            fs::create_dir_all(parent).with_context(|| {
                format!(
                    "failed to create package artifact directory '{}'",
                    parent.display()
                )
            })?;
        }
        fs::write(
            &marker,
            format!(
                "status = \"ok\"\npackage = \"{}\"\nfingerprint = \"{}\"\n",
                package.label(),
                fingerprint
            ),
        )
        .with_context(|| format!("failed to write build marker '{}'", marker.display()))?;

        cache
            .package_fingerprints
            .insert(package_id.clone(), fingerprint);
        report.built.push(package.label());
    }

    write_build_cache(&workspace.root_dir, &cache)?;
    Ok(report)
}

pub fn run_workspace_package(cwd: &Path, package_name: Option<&str>) -> Result<()> {
    let workspace_root = find_workspace_root(cwd)?;
    let workspace = resolve_workspace(&workspace_root)?;
    let package_id = select_run_package(&workspace, package_name)?;
    let package = workspace
        .packages
        .get(&package_id)
        .ok_or_else(|| anyhow!("internal resolver error: unknown package '{}'", package_id))?;

    let outcome = compile_package_closure(&workspace, &package_id)?;
    if let Some(last_result) = outcome.last_result {
        if let Some((_, value)) = last_result.evaluated_terms.last() {
            println!("Result ({}) = {:?}", package.label(), value);
        } else {
            println!(
                "Package '{}' built and loaded successfully.",
                package.label()
            );
        }
    } else {
        println!(
            "Package '{}' built and loaded successfully.",
            package.label()
        );
    }
    Ok(())
}

pub fn run_workspace_file(file: &Path) -> Result<()> {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    load_prelude(&mut env, &mut expander)?;

    let path = file
        .to_str()
        .ok_or_else(|| anyhow!("file path '{}' is not valid UTF-8", file.display()))?;
    let _ = repl::run_file(
        path,
        &mut env,
        &mut expander,
        repl::RunFileOptions {
            verbose: false,
            panic_free: false,
            require_axiom_tags: false,
            allow_axioms: true,
            prelude_frozen: true,
            allow_redefine: false,
        },
    );
    Ok(())
}

pub fn run_workspace_tests(cwd: &Path) -> Result<()> {
    let status = Command::new("cargo")
        .arg("test")
        .arg("--all")
        .current_dir(cwd)
        .status()
        .with_context(|| format!("failed to execute cargo test in '{}'", cwd.display()))?;
    if !status.success() {
        bail!("cargo test --all failed");
    }
    Ok(())
}

pub fn scaffold_new_package(
    cwd: &Path,
    name: &str,
    explicit_path: Option<&Path>,
) -> Result<PathBuf> {
    let package_dir = match explicit_path {
        Some(path) if path.is_absolute() => path.to_path_buf(),
        Some(path) => cwd.join(path),
        None => cwd.join(name),
    };
    fs::create_dir_all(package_dir.join("src")).with_context(|| {
        format!(
            "failed to create package directory '{}'",
            package_dir.display()
        )
    })?;
    let manifest_path = package_dir.join(MANIFEST_FILE);
    if manifest_path.exists() {
        bail!("manifest already exists at '{}'", manifest_path.display());
    }
    let module_name = sanitize_symbol(name);
    let manifest = format!(
        "[package]\nname = \"{}\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[dependencies]\n",
        name
    );
    fs::write(&manifest_path, manifest)
        .with_context(|| format!("failed to write manifest '{}'", manifest_path.display()))?;
    let main_path = package_dir.join("src/main.lrl");
    let source = format!("(module {})\n(def main (sort 1) (sort 0))\n", module_name);
    fs::write(&main_path, source)
        .with_context(|| format!("failed to write source '{}'", main_path.display()))?;
    Ok(package_dir)
}

pub fn clean_workspace(cwd: &Path) -> Result<()> {
    let workspace_root = find_workspace_root(cwd)?;
    let build_dir = workspace_root.join("build/lrl");
    if build_dir.exists() {
        fs::remove_dir_all(&build_dir).with_context(|| {
            format!("failed to remove build directory '{}'", build_dir.display())
        })?;
    }
    Ok(())
}

fn find_workspace_root(start: &Path) -> Result<PathBuf> {
    let mut current = fs::canonicalize(start)
        .with_context(|| format!("failed to canonicalize '{}'", start.display()))?;
    loop {
        let candidate = current.join(MANIFEST_FILE);
        if candidate.exists() {
            return Ok(current);
        }
        if !current.pop() {
            break;
        }
    }
    bail!(
        "no '{}' found at or above '{}'",
        MANIFEST_FILE,
        start.display()
    )
}

fn resolve_workspace(root: &Path) -> Result<ResolvedWorkspace> {
    // Workspace resolution is path-based and deterministic: same manifests => same graph/order.
    let root_dir = fs::canonicalize(root)
        .with_context(|| format!("failed to canonicalize workspace root '{}'", root.display()))?;
    let root_manifest_path = root_dir.join(MANIFEST_FILE);
    if !root_manifest_path.exists() {
        bail!(
            "workspace manifest '{}' does not exist",
            root_manifest_path.display()
        );
    }
    let root_manifest = read_manifest(&root_manifest_path)?;
    let mut ctx = ResolveContext::default();

    let mut member_ids = Vec::new();
    if let Some(workspace) = &root_manifest.workspace {
        if workspace.members.is_empty() {
            bail!(
                "workspace manifest '{}' has an empty [workspace].members list",
                root_manifest_path.display()
            );
        }
        for member in &workspace.members {
            let member_root = root_dir.join(member);
            let member_id = load_package(
                &member_root,
                SourceKind::Path(member_root.clone()),
                &mut ctx,
            )?;
            if !member_ids.contains(&member_id) {
                member_ids.push(member_id);
            }
        }
    } else if root_manifest.package.is_some() {
        let root_id = load_package(&root_dir, SourceKind::Path(root_dir.clone()), &mut ctx)?;
        member_ids.push(root_id);
    } else {
        bail!(
            "manifest '{}' must define either [workspace] or [package]",
            root_manifest_path.display()
        );
    }

    member_ids.sort();
    member_ids.dedup();
    let topo_order = topological_order(&ctx.packages)?;

    Ok(ResolvedWorkspace {
        root_dir,
        packages: ctx.packages,
        member_ids,
        topo_order,
    })
}

fn load_package(root: &Path, source: SourceKind, ctx: &mut ResolveContext) -> Result<String> {
    let root_dir = fs::canonicalize(root)
        .with_context(|| format!("failed to canonicalize package root '{}'", root.display()))?;
    let manifest_path = root_dir.join(MANIFEST_FILE);
    let manifest_path = fs::canonicalize(&manifest_path).with_context(|| {
        format!(
            "failed to locate package manifest '{}'",
            manifest_path.display()
        )
    })?;

    if ctx.loading.contains(&manifest_path) {
        bail!("dependency cycle detected at '{}'", manifest_path.display());
    }
    if let Some(existing) = ctx.by_manifest.get(&manifest_path) {
        return Ok(existing.clone());
    }

    let manifest = read_manifest(&manifest_path)?;
    let package = manifest.package.ok_or_else(|| {
        anyhow!(
            "manifest '{}' is missing required [package] section",
            manifest_path.display()
        )
    })?;
    if package.name.trim().is_empty() {
        bail!(
            "manifest '{}' has an empty [package].name",
            manifest_path.display()
        );
    }
    if package.version.trim().is_empty() {
        bail!(
            "manifest '{}' has an empty [package].version",
            manifest_path.display()
        );
    }

    let lock_source = source.as_lock_source();
    let package_id = package_id(&package.name, &package.version, &lock_source);
    ctx.loading.insert(manifest_path.clone());
    ctx.by_manifest
        .insert(manifest_path.clone(), package_id.clone());

    let mut resolved = ResolvedPackage {
        package_id: package_id.clone(),
        name: package.name.clone(),
        version: package.version.clone(),
        edition: package.edition.unwrap_or_else(|| "2026".to_string()),
        manifest_path: manifest_path.clone(),
        root_dir: root_dir.clone(),
        root_module: package.module.unwrap_or_else(|| package.name.clone()),
        entry_file: root_dir.join(package.root.unwrap_or_else(|| "src/main.lrl".to_string())),
        dependencies: Vec::new(),
    };

    // Resolve direct dependency edges now; transitive closure is derived later from these edges.
    let mut dependencies = Vec::new();
    for (declared_name, raw_spec) in manifest.dependencies.unwrap_or_default() {
        let spec = raw_spec.into_spec();
        if let Some(git) = spec.git {
            let rev = spec.rev.unwrap_or_else(|| "HEAD".to_string());
            bail!(
                "dependency '{}': git source '{}' at rev '{}' is declared, but git dependencies are not implemented yet",
                declared_name,
                git,
                rev
            );
        }

        let dep_path = match spec.path {
            Some(path) => root_dir.join(path),
            None => {
                bail!(
                    "dependency '{}' in '{}' must declare at least a 'path' source",
                    declared_name,
                    manifest_path.display()
                )
            }
        };
        let dep_id = load_package(&dep_path, SourceKind::Path(dep_path.clone()), ctx)?;
        let dep_pkg = ctx
            .packages
            .get(&dep_id)
            .ok_or_else(|| anyhow!("internal resolver error: missing dependency '{}'", dep_id))?;

        if let Some(package_name) = spec.package {
            if package_name != dep_pkg.name {
                bail!(
                    "dependency '{}' expected package '{}' but resolved '{}'",
                    declared_name,
                    package_name,
                    dep_pkg.name
                );
            }
        }

        if let Some(version_req) = spec.version {
            if version_req != dep_pkg.version {
                bail!(
                    "dependency '{}' requested version '{}' but resolved '{}'",
                    declared_name,
                    version_req,
                    dep_pkg.version
                );
            }
        }

        dependencies.push(ResolvedDependency {
            declared_name,
            package_name: dep_pkg.name.clone(),
            package_id: dep_id,
        });
    }

    dependencies.sort_by(|left, right| {
        left.package_name
            .cmp(&right.package_name)
            .then(left.package_id.cmp(&right.package_id))
            .then(left.declared_name.cmp(&right.declared_name))
    });
    resolved.dependencies = dependencies;

    ctx.packages.insert(package_id.clone(), resolved);
    ctx.loading.remove(&manifest_path);
    Ok(package_id)
}

fn read_manifest(path: &Path) -> Result<RawManifest> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read manifest '{}'", path.display()))?;
    toml::from_str(&text).with_context(|| format!("failed to parse manifest '{}'", path.display()))
}

fn topological_order(packages: &BTreeMap<String, ResolvedPackage>) -> Result<Vec<String>> {
    #[derive(Clone, Copy, Eq, PartialEq)]
    enum VisitState {
        Visiting,
        Visited,
    }

    fn visit(
        package_id: &str,
        packages: &BTreeMap<String, ResolvedPackage>,
        state: &mut BTreeMap<String, VisitState>,
        order: &mut Vec<String>,
    ) -> Result<()> {
        if let Some(existing) = state.get(package_id).copied() {
            return match existing {
                VisitState::Visited => Ok(()),
                VisitState::Visiting => {
                    bail!("dependency graph cycle detected at '{}'", package_id)
                }
            };
        }

        state.insert(package_id.to_string(), VisitState::Visiting);
        let package = packages.get(package_id).ok_or_else(|| {
            anyhow!(
                "internal topological sort error: package '{}' not found",
                package_id
            )
        })?;
        for dep in &package.dependencies {
            visit(&dep.package_id, packages, state, order)?;
        }
        state.insert(package_id.to_string(), VisitState::Visited);
        order.push(package_id.to_string());
        Ok(())
    }

    let mut order = Vec::new();
    let mut state: BTreeMap<String, VisitState> = BTreeMap::new();
    for package_id in packages.keys() {
        visit(package_id, packages, &mut state, &mut order)?;
    }
    Ok(order)
}

fn ensure_lockfile(workspace: &ResolvedWorkspace, enforce: bool) -> Result<LockfileStatus> {
    // In release/locked mode we refuse stale lockfiles instead of auto-rewriting.
    let lock_path = workspace.root_dir.join(LOCK_FILE);
    let generated = generate_lockfile(workspace)?;

    if !lock_path.exists() {
        if enforce {
            bail!(
                "lockfile '{}' is required in release/locked mode",
                lock_path.display()
            );
        }
        write_lockfile(&lock_path, &generated)?;
        return Ok(LockfileStatus { updated: true });
    }

    let existing_text = fs::read_to_string(&lock_path)
        .with_context(|| format!("failed to read lockfile '{}'", lock_path.display()))?;
    let existing: Lockfile = toml::from_str(&existing_text)
        .with_context(|| format!("failed to parse lockfile '{}'", lock_path.display()))?;

    if existing == generated {
        return Ok(LockfileStatus { updated: false });
    }

    if enforce {
        bail!(
            "lockfile '{}' is out of date; run `lrl build` to refresh it",
            lock_path.display()
        );
    }

    write_lockfile(&lock_path, &generated)?;
    Ok(LockfileStatus { updated: true })
}

fn generate_lockfile(workspace: &ResolvedWorkspace) -> Result<Lockfile> {
    let mut package_entries = Vec::new();
    for package_id in workspace.packages.keys() {
        let package = workspace.packages.get(package_id).ok_or_else(|| {
            anyhow!(
                "internal lockfile error: package '{}' not found",
                package_id
            )
        })?;
        let source = format!("path:{}", package.root_dir.display());
        let mut dependencies: Vec<String> = package
            .dependencies
            .iter()
            .map(|dep| dep.package_id.clone())
            .collect();
        dependencies.sort();
        package_entries.push(LockPackage {
            package_id: package.package_id.clone(),
            name: package.name.clone(),
            resolved_version: package.version.clone(),
            source,
            content_hash: own_content_hash(package)?,
            dependencies,
        });
    }
    package_entries.sort_by(|left, right| left.package_id.cmp(&right.package_id));
    Ok(Lockfile {
        version: LOCK_VERSION,
        package: package_entries,
    })
}

fn write_lockfile(path: &Path, lockfile: &Lockfile) -> Result<()> {
    let text = toml::to_string_pretty(lockfile)
        .with_context(|| format!("failed to serialize lockfile '{}'", path.display()))?;
    fs::write(path, text).with_context(|| format!("failed to write lockfile '{}'", path.display()))
}

fn load_build_cache(root: &Path) -> Result<BuildCache> {
    let path = root.join(CACHE_FILE);
    if !path.exists() {
        return Ok(BuildCache::default());
    }
    let text = fs::read_to_string(&path)
        .with_context(|| format!("failed to read build cache '{}'", path.display()))?;
    toml::from_str(&text)
        .with_context(|| format!("failed to parse build cache '{}'", path.display()))
}

fn write_build_cache(root: &Path, cache: &BuildCache) -> Result<()> {
    let path = root.join(CACHE_FILE);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| {
            format!(
                "failed to create build cache directory '{}'",
                parent.display()
            )
        })?;
    }
    let text = toml::to_string_pretty(cache)
        .with_context(|| format!("failed to serialize build cache '{}'", path.display()))?;
    fs::write(&path, text)
        .with_context(|| format!("failed to write build cache '{}'", path.display()))
}

fn marker_path(workspace_root: &Path, package_id: &str) -> PathBuf {
    workspace_root
        .join("build/lrl")
        .join(sanitize_for_path(package_id))
        .join("checked.ok")
}

fn package_fingerprint(
    workspace: &ResolvedWorkspace,
    package_id: &str,
    cache: &mut BTreeMap<String, String>,
) -> Result<String> {
    if let Some(existing) = cache.get(package_id) {
        return Ok(existing.clone());
    }
    let package = workspace.packages.get(package_id).ok_or_else(|| {
        anyhow!(
            "internal fingerprint error: package '{}' not found",
            package_id
        )
    })?;

    let mut parts = Vec::new();
    parts.push(package.package_id.as_bytes().to_vec());
    parts.push(package.edition.as_bytes().to_vec());
    parts.push(fs::read(&package.manifest_path).with_context(|| {
        format!(
            "failed to read manifest for fingerprint '{}'",
            package.manifest_path.display()
        )
    })?);
    for file in package_source_files(package)? {
        parts.push(file.to_string_lossy().as_bytes().to_vec());
        parts.push(
            fs::read(&file)
                .with_context(|| format!("failed to read source file '{}'", file.display()))?,
        );
    }

    let mut dep_ids: Vec<String> = package
        .dependencies
        .iter()
        .map(|dep| dep.package_id.clone())
        .collect();
    dep_ids.sort();
    for dep_id in dep_ids {
        let dep_fp = package_fingerprint(workspace, &dep_id, cache)?;
        parts.push(dep_id.into_bytes());
        parts.push(dep_fp.into_bytes());
    }

    let fingerprint = stable_hash(&parts);
    cache.insert(package_id.to_string(), fingerprint.clone());
    Ok(fingerprint)
}

fn own_content_hash(package: &ResolvedPackage) -> Result<String> {
    let mut parts = Vec::new();
    parts.push(package.package_id.as_bytes().to_vec());
    parts.push(fs::read(&package.manifest_path).with_context(|| {
        format!(
            "failed to read manifest for content hash '{}'",
            package.manifest_path.display()
        )
    })?);
    for file in package_source_files(package)? {
        parts.push(file.to_string_lossy().as_bytes().to_vec());
        parts.push(
            fs::read(&file)
                .with_context(|| format!("failed to read source file '{}'", file.display()))?,
        );
    }
    Ok(stable_hash(&parts))
}

fn compile_package_closure(
    workspace: &ResolvedWorkspace,
    target_package_id: &str,
) -> Result<CompileOutcome> {
    // Compile the full transitive closure in topological order into one env so imports
    // see the same dependency universe the resolver validated.
    let mut required = BTreeSet::new();
    collect_transitive_dependencies(workspace, target_package_id, &mut required)?;
    required.insert(target_package_id.to_string());

    let order: Vec<String> = workspace
        .topo_order
        .iter()
        .filter(|id| required.contains(id.as_str()))
        .cloned()
        .collect();
    let (mut env, mut expander) = fresh_compile_state()?;
    let options = PipelineOptions {
        prelude_frozen: true,
        allow_redefine: false,
        ..Default::default()
    };

    let mut last_result: Option<driver::ProcessingResult> = None;
    for package_id in order {
        let package = workspace
            .packages
            .get(&package_id)
            .ok_or_else(|| anyhow!("internal compile error: package '{}' not found", package_id))?;
        for source_file in package_source_files(package)? {
            let source = fs::read_to_string(&source_file).with_context(|| {
                format!("failed to read source file '{}'", source_file.display())
            })?;
            let rewritten = rewrite_package_imports(workspace, &package_id, &source_file, &source)?;
            let mut diagnostics = DiagnosticCollector::new();
            let filename = source_file.to_string_lossy().to_string();
            let result = driver::process_code(
                &rewritten,
                &filename,
                &mut env,
                &mut expander,
                &options,
                &mut diagnostics,
            );
            if diagnostics.has_errors() {
                let errors: Vec<String> = diagnostics
                    .diagnostics
                    .iter()
                    .filter(|diag| diag.level == Level::Error)
                    .map(|diag| diag.message_with_code())
                    .collect();
                bail!(
                    "failed to build package '{}' while compiling '{}': {}",
                    package.label(),
                    source_file.display(),
                    errors.join(" | ")
                );
            }
            let result = match result {
                Ok(processed) => processed,
                Err(err) => {
                    bail!(
                        "driver pipeline failed for package '{}' in '{}': {:?}",
                        package.label(),
                        source_file.display(),
                        err
                    );
                }
            };
            if package_id == target_package_id {
                last_result = Some(result);
            }
        }
    }

    Ok(CompileOutcome { last_result })
}

fn fresh_compile_state() -> Result<(Env, Expander)> {
    let mut env = Env::new();
    let mut expander = Expander::new();
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    load_prelude(&mut env, &mut expander)?;
    Ok((env, expander))
}

fn load_prelude(env: &mut Env, expander: &mut Expander) -> Result<()> {
    let prelude_options = PipelineOptions {
        prelude_frozen: false,
        allow_redefine: false,
        allow_axioms: true,
        ..Default::default()
    };
    let mut prelude_modules = Vec::new();
    let cli_manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = cli_manifest_dir
        .parent()
        .ok_or_else(|| anyhow!("failed to compute repository root from CARGO_MANIFEST_DIR"))?;

    let allow_reserved = env.allows_reserved_primitives();
    env.set_allow_reserved_primitives(true);
    for relative in compiler::prelude_stack_for_backend(compiler::BackendMode::Dynamic) {
        let path = repo_root.join(relative);
        if !path.exists() {
            continue;
        }
        let content = fs::read_to_string(&path)
            .with_context(|| format!("failed to read prelude '{}'", path.display()))?;
        let module_id = driver::module_id_for_source(path.to_string_lossy().as_ref());
        expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
        crate::set_prelude_macro_boundary_allowlist(expander, &module_id);
        if !prelude_modules.is_empty() {
            expander.set_default_imports(prelude_modules.clone());
        }
        let mut diagnostics = DiagnosticCollector::new();
        let _ = driver::process_code(
            &content,
            path.to_string_lossy().as_ref(),
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
                .filter(|diag| diag.level == Level::Error)
                .map(|diag| diag.message_with_code())
                .collect();
            bail!(
                "failed to load prelude '{}': {}",
                path.display(),
                errors.join(" | ")
            );
        }
        prelude_modules.push(module_id);
    }
    env.set_allow_reserved_primitives(allow_reserved);

    if !prelude_modules.is_empty() {
        env.init_marker_registry().map_err(|err| {
            anyhow!(
                "failed to initialize marker registry from prelude: {:?}",
                err
            )
        })?;
        expander.set_default_imports(prelude_modules);
    }
    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
    Ok(())
}

fn package_source_files(package: &ResolvedPackage) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    let src_dir = package.root_dir.join("src");
    if src_dir.exists() {
        collect_lrl_files(&src_dir, &mut files)?;
    }
    if package.entry_file.exists() && !files.contains(&package.entry_file) {
        files.push(package.entry_file.clone());
    }
    files.sort();
    files.dedup();
    if files.is_empty() {
        bail!(
            "package '{}' has no source files under '{}' and entry file '{}' does not exist",
            package.label(),
            src_dir.display(),
            package.entry_file.display()
        );
    }
    Ok(files)
}

fn collect_lrl_files(dir: &Path, output: &mut Vec<PathBuf>) -> Result<()> {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .with_context(|| format!("failed to read source directory '{}'", dir.display()))?
        .filter_map(|entry| entry.ok().map(|item| item.path()))
        .collect();
    entries.sort();

    for path in entries {
        if is_apple_double(&path) {
            continue;
        }
        if path.is_dir() {
            collect_lrl_files(&path, output)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("lrl") {
            output.push(path);
        }
    }
    Ok(())
}

fn is_apple_double(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(|name| name.starts_with("._"))
        .unwrap_or(false)
}

fn rewrite_package_imports(
    workspace: &ResolvedWorkspace,
    package_id: &str,
    source_path: &Path,
    source: &str,
) -> Result<String> {
    // Parse and rewrite only top-level import forms. All other syntax is preserved
    // through stable pretty-printing for deterministic downstream compilation.
    let mut parser = Parser::new(source);
    let nodes = parser.parse().with_context(|| {
        format!(
            "failed to parse source '{}' before import resolution",
            source_path.display()
        )
    })?;

    let mut rewritten = Vec::with_capacity(nodes.len());
    for node in nodes {
        rewritten.push(rewrite_import_node(
            workspace,
            package_id,
            source_path,
            &node,
        )?);
    }
    Ok(rewritten.join("\n"))
}

fn rewrite_import_node(
    workspace: &ResolvedWorkspace,
    package_id: &str,
    source_path: &Path,
    node: &Syntax,
) -> Result<String> {
    let (target, alias, import_span) = match parse_import_shape(node) {
        Some(shape) => shape,
        None => return Ok(node.pretty_print_stable()),
    };

    let (import_name, explicit_version) = parse_import_target(&target);
    let candidates = candidates_for_name(workspace, package_id, import_name)?;

    let selected = if let Some(version) = explicit_version {
        if candidates.is_empty() {
            bail!(
                "Unknown import: {}@{} is not reachable from package '{}'",
                import_name,
                version,
                package_label(workspace, package_id)?
            );
        }
        let mut matching: Vec<&ResolvedPackage> = candidates
            .into_iter()
            .filter(|package| package.version == version)
            .collect();
        matching.sort_by(|left, right| left.package_id.cmp(&right.package_id));
        if matching.is_empty() {
            bail!(
                "Unknown import: {}@{} is not reachable from package '{}' ({}:{})",
                import_name,
                version,
                package_label(workspace, package_id)?,
                source_path.display(),
                import_span.line
            );
        }
        if matching.len() > 1 {
            let details: Vec<String> = matching
                .iter()
                .map(|package| format!("{} ({})", package.label(), package.package_id))
                .collect();
            bail!(
                "Ambiguous import: {}@{} resolves to multiple packages: {}. Use a unique dependency source.",
                import_name,
                version,
                details.join(", ")
            );
        }
        matching[0]
    } else {
        if candidates.is_empty() {
            return Ok(node.pretty_print_stable());
        }
        if candidates.len() > 1 {
            let mut versions: Vec<String> =
                candidates.iter().map(|package| package.label()).collect();
            versions.sort();
            versions.dedup();
            bail!(
                "Ambiguous import: {} resolves to {}. Use explicit import alias: (import {}@<version> as <alias>).",
                import_name,
                versions.join(" and "),
                import_name
            );
        }
        candidates[0]
    };

    let alias = alias.unwrap_or_else(|| import_name.to_string());
    let module = selected.root_module.as_str();
    if module == alias {
        Ok(format!("(import {})", module))
    } else {
        Ok(format!("(import {} as {})", module, alias))
    }
}

fn parse_import_shape(node: &Syntax) -> Option<(String, Option<String>, frontend::surface::Span)> {
    let items = match &node.kind {
        SyntaxKind::List(items) if !items.is_empty() => items,
        _ => return None,
    };

    match &items[0].kind {
        SyntaxKind::Symbol(symbol) if symbol == "import" => {}
        _ => return None,
    }

    match items.len() {
        2 => match &items[1].kind {
            SyntaxKind::Symbol(symbol) if symbol != "classical" => {
                Some((symbol.clone(), None, node.span))
            }
            _ => Some((String::new(), None, node.span)),
        },
        4 => {
            let target = match &items[1].kind {
                SyntaxKind::Symbol(symbol) => symbol.clone(),
                _ => return Some((String::new(), None, node.span)),
            };
            let is_as = matches!(&items[2].kind, SyntaxKind::Symbol(symbol) if symbol == "as");
            if !is_as {
                return Some((String::new(), None, node.span));
            }
            let alias = match &items[3].kind {
                SyntaxKind::Symbol(symbol) => Some(symbol.clone()),
                _ => return Some((String::new(), None, node.span)),
            };
            Some((target, alias, node.span))
        }
        _ => Some((String::new(), None, node.span)),
    }
}

fn parse_import_target(target: &str) -> (&str, Option<&str>) {
    if target.is_empty() {
        return ("", None);
    }
    if let Some((name, version)) = target.split_once('@') {
        if !name.is_empty() && !version.is_empty() {
            return (name, Some(version));
        }
    }
    (target, None)
}

fn candidates_for_name<'a>(
    workspace: &'a ResolvedWorkspace,
    package_id: &str,
    name: &str,
) -> Result<Vec<&'a ResolvedPackage>> {
    let mut transitive = BTreeSet::new();
    collect_transitive_dependencies(workspace, package_id, &mut transitive)?;
    transitive.remove(package_id);

    let mut candidates = Vec::new();
    for dep_id in transitive {
        let package = workspace.packages.get(&dep_id).ok_or_else(|| {
            anyhow!(
                "internal import resolver error: dependency '{}' not found",
                dep_id
            )
        })?;
        if package.name == name {
            candidates.push(package);
        }
    }

    candidates.sort_by(|left, right| {
        left.version
            .cmp(&right.version)
            .then(left.package_id.cmp(&right.package_id))
    });
    Ok(candidates)
}

fn collect_transitive_dependencies(
    workspace: &ResolvedWorkspace,
    package_id: &str,
    visited: &mut BTreeSet<String>,
) -> Result<()> {
    if !visited.insert(package_id.to_string()) {
        return Ok(());
    }
    let package = workspace.packages.get(package_id).ok_or_else(|| {
        anyhow!(
            "internal dependency traversal error: package '{}' not found",
            package_id
        )
    })?;
    for dep in &package.dependencies {
        collect_transitive_dependencies(workspace, &dep.package_id, visited)?;
    }
    Ok(())
}

fn select_run_package(workspace: &ResolvedWorkspace, package_name: Option<&str>) -> Result<String> {
    let mut members: Vec<&ResolvedPackage> = workspace
        .member_ids
        .iter()
        .filter_map(|id| workspace.packages.get(id))
        .collect();
    members.sort_by_key(|package| package.label());

    if let Some(name) = package_name {
        let matches: Vec<&ResolvedPackage> = members
            .into_iter()
            .filter(|package| package.name == name || package.label() == name)
            .collect();
        if matches.is_empty() {
            bail!("workspace member '{}' not found", name);
        }
        if matches.len() > 1 {
            let labels: Vec<String> = matches.iter().map(|package| package.label()).collect();
            bail!(
                "workspace member '{}' is ambiguous; matching packages: {}",
                name,
                labels.join(", ")
            );
        }
        return Ok(matches[0].package_id.clone());
    }

    if members.is_empty() {
        bail!("workspace has no buildable members");
    }
    if members.len() > 1 {
        let labels: Vec<String> = members.iter().map(|package| package.label()).collect();
        bail!(
            "workspace has multiple members ({}); specify one with `lrl run <pkg>`",
            labels.join(", ")
        );
    }
    Ok(members[0].package_id.clone())
}

fn package_label(workspace: &ResolvedWorkspace, package_id: &str) -> Result<String> {
    workspace
        .packages
        .get(package_id)
        .map(ResolvedPackage::label)
        .ok_or_else(|| {
            anyhow!(
                "internal resolver error: package '{}' not found",
                package_id
            )
        })
}

fn package_id(name: &str, version: &str, source: &str) -> String {
    let source_hash = stable_hash(&[source.as_bytes().to_vec()]);
    format!("{}@{}#{}", name, version, source_hash)
}

fn sanitize_for_path(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn sanitize_symbol(value: &str) -> String {
    let mut sanitized = String::new();
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '.' {
            sanitized.push(ch);
        } else {
            sanitized.push('_');
        }
    }
    if sanitized.is_empty() {
        "main".to_string()
    } else {
        sanitized
    }
}

fn stable_hash(parts: &[Vec<u8>]) -> String {
    let mut hash: u64 = 0xcbf29ce484222325;
    for part in parts {
        for byte in part {
            hash ^= *byte as u64;
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash ^= 0xff;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{:016x}", hash)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_temp_dir(name: &str) -> PathBuf {
        let mut path = env::temp_dir();
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock must be after unix epoch")
            .as_nanos();
        path.push(format!("lrl_pkg_mgr_{}_{}", name, stamp));
        path
    }

    fn write_file(path: &Path, content: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("failed to create parent directory");
        }
        fs::write(path, content).expect("failed to write fixture file");
    }

    fn basic_workspace_layout(root: &Path) {
        write_file(
            &root.join("lrl.toml"),
            r#"
[workspace]
members = ["app", "dep"]
"#,
        );
        write_file(
            &root.join("dep/lrl.toml"),
            r#"
[package]
name = "dep"
version = "1.0.0"
edition = "2026"
module = "dep_mod"

[dependencies]
"#,
        );
        write_file(
            &root.join("dep/src/main.lrl"),
            "(module dep_mod)\n(def v (sort 1) (sort 0))\n",
        );
        write_file(
            &root.join("app/lrl.toml"),
            r#"
[package]
name = "app"
version = "1.0.0"
edition = "2026"

[dependencies]
dep = { path = "../dep" }
"#,
        );
        write_file(
            &root.join("app/src/main.lrl"),
            "(module app)\n(import dep)\n(def use_dep (sort 1) dep.v)\n",
        );
    }

    #[test]
    fn rewrite_single_dependency_import_uses_resolved_module() {
        let root = unique_temp_dir("single_dep");
        basic_workspace_layout(&root);
        let workspace = resolve_workspace(&root).expect("workspace should resolve");
        let app_id = workspace
            .packages
            .values()
            .find(|package| package.name == "app")
            .expect("app package should exist")
            .package_id
            .clone();

        let rewritten = rewrite_package_imports(
            &workspace,
            &app_id,
            &root.join("app/src/main.lrl"),
            "(module app)\n(import dep)\n(def use_dep (sort 1) dep.v)\n",
        )
        .expect("rewrite should succeed");
        assert!(
            rewritten.contains("(import dep_mod as dep)"),
            "rewritten source must import resolved module with stable alias: {}",
            rewritten
        );
    }

    #[test]
    fn rewrite_reports_ambiguous_import() {
        let root = unique_temp_dir("ambiguous_dep");
        write_file(
            &root.join("lrl.toml"),
            r#"
[workspace]
members = ["b1", "b2", "a", "c", "d"]
"#,
        );
        write_file(
            &root.join("b1/lrl.toml"),
            r#"
[package]
name = "b"
version = "1.0.0"
edition = "2026"
module = "b_v1"
[dependencies]
"#,
        );
        write_file(
            &root.join("b1/src/main.lrl"),
            "(module b_v1)\n(def value (sort 1) (sort 0))\n",
        );
        write_file(
            &root.join("b2/lrl.toml"),
            r#"
[package]
name = "b"
version = "2.0.0"
edition = "2026"
module = "b_v2"
[dependencies]
"#,
        );
        write_file(
            &root.join("b2/src/main.lrl"),
            "(module b_v2)\n(def value (sort 1) (sort 0))\n",
        );
        write_file(
            &root.join("a/lrl.toml"),
            r#"
[package]
name = "a"
version = "1.0.0"
edition = "2026"
[dependencies]
b = { path = "../b1" }
"#,
        );
        write_file(
            &root.join("a/src/main.lrl"),
            "(module a)\n(import b)\n(def a_val (sort 1) b.value)\n",
        );
        write_file(
            &root.join("c/lrl.toml"),
            r#"
[package]
name = "c"
version = "1.0.0"
edition = "2026"
[dependencies]
b = { path = "../b2" }
"#,
        );
        write_file(
            &root.join("c/src/main.lrl"),
            "(module c)\n(import b)\n(def c_val (sort 1) b.value)\n",
        );
        write_file(
            &root.join("d/lrl.toml"),
            r#"
[package]
name = "d"
version = "1.0.0"
edition = "2026"
[dependencies]
a = { path = "../a" }
c = { path = "../c" }
"#,
        );
        write_file(
            &root.join("d/src/main.lrl"),
            "(module d)\n(import b)\n(def bad (sort 1) b.value)\n",
        );

        let workspace = resolve_workspace(&root).expect("workspace should resolve");
        let d_id = workspace
            .packages
            .values()
            .find(|package| package.name == "d")
            .expect("d package should exist")
            .package_id
            .clone();
        let err = rewrite_package_imports(
            &workspace,
            &d_id,
            &root.join("d/src/main.lrl"),
            "(module d)\n(import b)\n(def bad (sort 1) b.value)\n",
        )
        .expect_err("ambiguous import must fail");
        assert!(
            err.to_string().contains("Ambiguous import: b resolves to"),
            "expected ambiguity message, got: {}",
            err
        );
    }

    #[test]
    fn rewrite_explicit_version_import_selects_correct_dependency() {
        let root = unique_temp_dir("explicit_version");
        write_file(
            &root.join("lrl.toml"),
            r#"
[workspace]
members = ["b1", "b2", "a", "c", "d"]
"#,
        );
        write_file(
            &root.join("b1/lrl.toml"),
            r#"
[package]
name = "b"
version = "1.0.0"
edition = "2026"
module = "b_v1"
[dependencies]
"#,
        );
        write_file(
            &root.join("b1/src/main.lrl"),
            "(module b_v1)\n(def value (sort 1) (sort 0))\n",
        );
        write_file(
            &root.join("b2/lrl.toml"),
            r#"
[package]
name = "b"
version = "2.0.0"
edition = "2026"
module = "b_v2"
[dependencies]
"#,
        );
        write_file(
            &root.join("b2/src/main.lrl"),
            "(module b_v2)\n(def value (sort 1) (sort 0))\n",
        );
        write_file(
            &root.join("a/lrl.toml"),
            r#"
[package]
name = "a"
version = "1.0.0"
edition = "2026"
[dependencies]
b = { path = "../b1" }
"#,
        );
        write_file(
            &root.join("a/src/main.lrl"),
            "(module a)\n(import b)\n(def a_val (sort 1) b.value)\n",
        );
        write_file(
            &root.join("c/lrl.toml"),
            r#"
[package]
name = "c"
version = "1.0.0"
edition = "2026"
[dependencies]
b = { path = "../b2" }
"#,
        );
        write_file(
            &root.join("c/src/main.lrl"),
            "(module c)\n(import b)\n(def c_val (sort 1) b.value)\n",
        );
        write_file(
            &root.join("d/lrl.toml"),
            r#"
[package]
name = "d"
version = "1.0.0"
edition = "2026"
[dependencies]
a = { path = "../a" }
c = { path = "../c" }
"#,
        );
        write_file(
            &root.join("d/src/main.lrl"),
            "(module d)\n(import b@1.0.0 as b1)\n(import b@2.0.0 as b2)\n(def pick1 (sort 1) b1.value)\n(def pick2 (sort 1) b2.value)\n",
        );

        let workspace = resolve_workspace(&root).expect("workspace should resolve");
        let d_id = workspace
            .packages
            .values()
            .find(|package| package.name == "d")
            .expect("d package should exist")
            .package_id
            .clone();
        let rewritten = rewrite_package_imports(
            &workspace,
            &d_id,
            &root.join("d/src/main.lrl"),
            "(module d)\n(import b@1.0.0 as b1)\n(import b@2.0.0 as b2)\n(def pick1 (sort 1) b1.value)\n(def pick2 (sort 1) b2.value)\n",
        )
        .expect("explicit import rewrite should succeed");
        assert!(
            rewritten.contains("(import b_v1 as b1)"),
            "rewritten source must import b_v1: {}",
            rewritten
        );
        assert!(
            rewritten.contains("(import b_v2 as b2)"),
            "rewritten source must import b_v2: {}",
            rewritten
        );
    }
}
