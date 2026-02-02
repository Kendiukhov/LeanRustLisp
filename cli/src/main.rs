use clap::{Parser, Subcommand};
use cli::{compiler, repl};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Source file to run (interprets)
    #[arg(required = false)]
    file: Option<String>,

    /// Show expanded macro syntax
    #[arg(long)]
    show_expanded: bool,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Compile a file to Rust
    Compile {
        file: String,
        /// Output binary path
        #[arg(short, long)]
        output: Option<String>,
    },
    /// Compile a file to Rust via MIR
    CompileMir {
        file: String,
    },
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Some(Commands::Compile { file, output }) => {
            compiler::compile_file(file, output.clone());
        }
        Some(Commands::CompileMir { file }) => {
             compiler::compile_file_to_mir(file);
        }
        None => {
            if let Some(file) = cli.file {
                let mut env = kernel::checker::Env::new();
                let mut expander = frontend::macro_expander::Expander::new();
                expander.verbose = cli.show_expanded;
                
                let prelude_path = "stdlib/prelude.lrl";
                if std::path::Path::new(prelude_path).exists() {
                     let _ = repl::run_file(prelude_path, &mut env, &mut expander, false);
                }
                
                let _ = repl::run_file(&file, &mut env, &mut expander, false);
                return;
            } else {
                repl::start();
            }
        }
    }
}
