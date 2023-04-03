use clap::Parser;
use itertools::Itertools;
use lib::{verify, Options};

/// OOX symbolic verification
#[derive(Parser)]
struct Args {
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
}

fn main() -> Result<(), String> {
    let args = Args::parse();

    if let Some((class_name, method_name)) = args.function.split(".").collect_tuple() {
        let options = Options {k: args.k, quiet: args.quiet, with_exceptional_clauses: true, heuristic: 
            args.heuristic};
        verify(
            &args.source_path,
            class_name,
            method_name,
            options
        )?;
    } else {
        println!("Entry point must be of the form 'class.method' and be unambiguous");
    }

    Ok(())
}
