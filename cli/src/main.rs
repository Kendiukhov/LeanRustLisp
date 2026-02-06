use clap::{Parser, Subcommand};
use cli::expand::{expand_source_with_imports, load_macros_from_source, ExpandMode};
use cli::{compiler, driver, repl};
use frontend::macro_expander::MacroBoundaryPolicy;
use std::fs;
use std::path::Path;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Source file to run (interprets)
    #[arg(required = false)]
    file: Option<String>,

    /// Show expanded macro syntax (legacy, prints during processing)
    #[arg(long, conflicts_with_all = ["expand_1", "expand_full", "trace_expand"])]
    show_expanded: bool,

    /// Print macro expansion trace during normal processing
    #[arg(long)]
    trace_macros: bool,

    /// Print one-step macro expansion for each top-level form
    #[arg(long, requires = "file", conflicts_with_all = ["show_expanded", "expand_full", "trace_expand"])]
    expand_1: bool,

    /// Print fully expanded syntax for each top-level form
    #[arg(long, requires = "file", conflicts_with_all = ["show_expanded", "expand_1", "trace_expand"])]
    expand_full: bool,

    /// Print expanded syntax plus macro trace
    #[arg(long, requires = "file", conflicts_with_all = ["show_expanded", "expand_1", "expand_full"])]
    trace_expand: bool,

    /// Enable panic-free profile (reject interior mutability)
    #[arg(long)]
    panic_free: bool,

    /// Downgrade macro boundary violations (unsafe/classical expansions) to warnings
    #[arg(long)]
    macro_boundary_warn: bool,

    /// Require axiom declarations to include at least one tag (classical/unsafe)
    #[arg(long)]
    require_axiom_tags: bool,

    /// Allow redefinition of existing names (unsafe; disables prelude freeze guard)
    #[arg(long)]
    allow_redefine: bool,

    /// Allow codegen/run of axiom-dependent definitions (unsafe; may panic at runtime)
    #[arg(long)]
    allow_axioms: bool,

    /// Definitional equality fuel (defaults to 100_000 unless LRL_DEFEQ_FUEL is set).
    /// Overrides LRL_DEFEQ_FUEL for this run (diagnostics report the active source).
    #[arg(long)]
    defeq_fuel: Option<usize>,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Compile a file to Rust
    Compile {
        file: String,
        /// Output binary path
        #[arg(short, long)]
        output: Option<String>,
        /// Select codegen backend
        #[arg(long, value_enum, default_value_t = compiler::BackendMode::Auto)]
        backend: compiler::BackendMode,
    },
    /// Compile a file to Rust using the typed-backend prelude only
    CompileTyped {
        file: String,
        /// Output binary path
        #[arg(short, long)]
        output: Option<String>,
    },
    /// Compile a file to Rust via MIR
    CompileMir {
        file: String,
        /// Select codegen backend
        #[arg(long, value_enum, default_value_t = compiler::BackendMode::Auto)]
        backend: compiler::BackendMode,
    },
}

fn main() {
    let cli = Cli::parse();

    if let Err(err) = cli::configure_defeq_fuel(cli.defeq_fuel) {
        match cli.defeq_fuel {
            Some(fuel) => {
                eprintln!(
                    "Invalid --defeq-fuel value ({}): {:?}. Provide a positive integer.",
                    fuel, err
                );
            }
            None => {
                eprintln!(
                    "Invalid LRL_DEFEQ_FUEL value: {:?}. Provide a positive integer.",
                    err
                );
            }
        }
        std::process::exit(2);
    }

    match &cli.command {
        Some(Commands::Compile {
            file,
            output,
            backend,
        }) => {
            compiler::compile_file(
                file,
                output.clone(),
                cli.trace_macros,
                cli.panic_free,
                cli.require_axiom_tags,
                cli.macro_boundary_warn,
                cli.allow_redefine,
                cli.allow_axioms,
                *backend,
            );
        }
        Some(Commands::CompileTyped { file, output }) => {
            compiler::compile_file_with_prelude(
                file,
                output.clone(),
                cli.trace_macros,
                cli.panic_free,
                cli.require_axiom_tags,
                cli.macro_boundary_warn,
                cli.allow_redefine,
                cli.allow_axioms,
                compiler::BackendMode::Typed,
                "stdlib/prelude_typed.lrl",
            );
        }
        Some(Commands::CompileMir { file, backend }) => {
            compiler::compile_file_to_mir(
                file,
                cli.trace_macros,
                cli.panic_free,
                cli.require_axiom_tags,
                cli.macro_boundary_warn,
                cli.allow_redefine,
                cli.allow_axioms,
                *backend,
            );
        }
        None => {
            if let Some(file) = cli.file {
                let expand_mode = if cli.expand_1 {
                    Some(ExpandMode::SingleStep)
                } else if cli.expand_full {
                    Some(ExpandMode::Full)
                } else if cli.trace_expand {
                    Some(ExpandMode::Trace)
                } else {
                    None
                };

                if let Some(mode) = expand_mode {
                    print_expansion_output(&file, mode, cli.macro_boundary_warn);
                }

                let mut env = kernel::checker::Env::new();
                let mut expander = frontend::macro_expander::Expander::new();
                expander.verbose = cli.show_expanded;
                expander.trace_verbose = cli.trace_macros;
                let user_policy = if cli.macro_boundary_warn {
                    MacroBoundaryPolicy::Warn
                } else {
                    MacroBoundaryPolicy::Deny
                };
                expander.set_macro_boundary_policy(user_policy);

                let prelude_path = "stdlib/prelude.lrl";
                if Path::new(prelude_path).exists() {
                    let prelude_module = driver::module_id_for_source(prelude_path);
                    expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
                    cli::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
                    let allow_reserved = env.allows_reserved_primitives();
                    env.set_allow_reserved_primitives(true);
                    let _ = repl::run_file(
                        prelude_path,
                        &mut env,
                        &mut expander,
                        false,
                        cli.panic_free,
                        false,
                        true,
                        false,
                        false,
                    );
                    env.set_allow_reserved_primitives(allow_reserved);
                    expander.clear_macro_boundary_allowlist();
                    expander.set_default_imports(vec![prelude_module]);
                    expander.set_macro_boundary_policy(user_policy);
                }

                env.set_allow_redefinition(cli.allow_redefine);
                let _ = repl::run_file(
                    &file,
                    &mut env,
                    &mut expander,
                    false,
                    cli.panic_free,
                    cli.require_axiom_tags,
                    cli.allow_axioms,
                    true,
                    cli.allow_redefine,
                );
                return;
            }
            repl::start(
                cli.trace_macros,
                cli.panic_free,
                cli.macro_boundary_warn,
                cli.require_axiom_tags,
                cli.allow_redefine,
                cli.allow_axioms,
            );
        }
    }
}

fn print_expansion_output(path: &str, mode: ExpandMode, macro_boundary_warn: bool) {
    let mut expander = frontend::macro_expander::Expander::new();
    let user_policy = if macro_boundary_warn {
        MacroBoundaryPolicy::Warn
    } else {
        MacroBoundaryPolicy::Deny
    };
    expander.set_macro_boundary_policy(user_policy);
    let prelude_path = "stdlib/prelude.lrl";

    if Path::new(prelude_path).exists() {
        match fs::read_to_string(prelude_path) {
            Ok(content) => {
                let prelude_module = driver::module_id_for_source(prelude_path);
                expander.enter_module(prelude_module.clone());
                expander.set_macro_boundary_policy(MacroBoundaryPolicy::Deny);
                cli::set_prelude_macro_boundary_allowlist(&mut expander, &prelude_module);
                if let Err(err) = load_macros_from_source(&mut expander, &content) {
                    eprintln!("{}", err);
                }
                expander.clear_macro_boundary_allowlist();
                expander.set_macro_boundary_policy(user_policy);
                expander.set_default_imports(vec![prelude_module]);
            }
            Err(e) => eprintln!("Error reading prelude {}: {:?}", prelude_path, e),
        }
    }

    let content = match fs::read_to_string(path) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("Error reading file {}: {:?}", path, e);
            return;
        }
    };

    match expand_source_with_imports(&content, path, &mut expander, mode) {
        Ok(output) => println!("{}", output),
        Err(err) => eprintln!("{}", err),
    }
}
