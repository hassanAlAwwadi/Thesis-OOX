use clap::Parser;
use itertools::Itertools;
use lib::verify;

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
        verify(
            &args.source_path,
            class_name,
            method_name,
            args.k,
            args.quiet,
            args.heuristic,
        )?;
    } else {
        println!("Entry point must be of the form 'class.method' and be unambiguous");
    }

    Ok(())
}
