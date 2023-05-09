use clap::{Parser, Subcommand};
use itertools::Itertools;
use lib::{verify, Options, parse_program, type_compilation_unit, SymbolTable};

/// OOX symbolic verification
#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Verify an OOX file using symbolic execution.
    Verify {
        // The OOX source file to verify
        source_path: String,
        // The maximum program path depth
        #[arg(short, long, default_value_t = 10)]
        k: u64,
        // The OOX function to verify
        #[arg(short, long)]
        function: String,
        // When quiet is passed, the only output returned is valid, invalid or error.
        #[arg(short, long, default_value_t = false)]
        quiet: bool,

        // The heuristic used to choose branches
        #[arg(value_enum, long, default_value_t = lib::Heuristic::DepthFirstSearch)]
        heuristic: lib::Heuristic,
    },
    /// Parse and typecheck an OOX source file
    Check {
        // The OOX source file to type check
        source_path: String,
    }
}

fn main() -> Result<(), String> {
    let args = Args::parse();
    match args.command {
        Commands::Verify { source_path, k, function, quiet, heuristic } => {
            if let Some((class_name, method_name)) = function.split(".").collect_tuple() {
                let options = Options {k: k, quiet: quiet, with_exceptional_clauses: true, heuristic: 
                    heuristic};
                verify(
                    &source_path,
                    class_name,
                    method_name,
                    options
                )?;
            } else {
                println!("Entry point must be of the form 'class.method' and be unambiguous");
            }
        },
        Commands::Check { source_path } => {
            let file_content = std::fs::read_to_string(&source_path).map_err(|err| err.to_string())?;
            let c =
                parse_program(&file_content, true).map_err(
                    |error| match error {
                        lib::Error::ParseError(err) => err.to_string(),
                        lib::Error::LexerError((line, col)) => {
                            format!("Lexer error at {}:{}:{}", source_path.to_string(), line, col)
                        }
                    },
                )?;
            let symbol_table = SymbolTable::from_ast(&c)?;
            type_compilation_unit(c, &symbol_table)?;
            println!("Type check OK");
        },
    }    

    

    Ok(())
}
