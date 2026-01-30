use clap::{Parser, Subcommand};
mod repl;
mod compiler;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Source file to run (interprets)
    #[arg(required = false)]
    file: Option<String>,
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
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Some(Commands::Compile { file, output }) => {
            compiler::compile_file(file, output.clone());
        }
        None => {
            if let Some(file) = cli.file {
                let mut env = kernel::checker::Env::new();
                let mut expander = frontend::macro_expander::Expander::new();
                repl::run_file(&file, &mut env, &mut expander, false);
            } else {
                repl::start();
            }
        }
    }
}
