use clap::{Parser, Subcommand};
use itertools::Itertools;
use lib::{
    insert_exceptional_clauses, parse_program, type_compilation_unit, verify, CompilationUnit,
    Options, SymbolTable, FILE_NAMES, mutate_program,
};
use pretty::BoxAllocator;

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
        /// The OOX source file to verify
        #[arg(num_args(0..))]
        source_paths: Vec<String>,
        /// The maximum program path depth
        #[arg(short, long, default_value_t = 40)]
        k: u64,
        /// The allowed time budget of the verification, in seconds.
        #[arg(short, long, default_value_t = 900)]
        time_budget: u64,
        /// The OOX function to verify
        #[arg(short, long)]
        function: String,

        /// Maximum symbolic array size
        #[arg(short, long, default_value_t = 3)]
        symbolic_array_size: u64,

        /// When quiet is passed, the only output returned is valid, invalid or error.
        #[arg(short, long, default_value_t = false)]
        quiet: bool,

        /// The heuristic used to choose branches
        #[arg(value_enum, long, default_value_t = lib::Heuristic::DepthFirstSearch)]
        heuristic: lib::Heuristic,

        /// After execution it prints a visualization of the coverage for each method.
        #[arg(long, default_value_t = false)]
        visualize_coverage: bool,

        /// Will create a file visualize.txt, showing the current program exploration guided by heuristic.
        #[arg(long, default_value_t = false)]
        visualize_heuristic: bool,

        /// The path where the log file should be written.
        #[arg(long, default_value = "./logs/log.txt")]
        log_path: String,

        /// Prune paths using Z3. This may alter performance or not work well with some heuristics. But it will ensure we don't visit unfeasible paths.
        #[arg(long, default_value_t = false)]
        prune_path_z3: bool,

        /// Local concretization solving threshold for symbolic variables. If there are more than this threshold combinations of variables we leave it to Z3.
        #[arg(long, default_value = "1000")]
        local_solving_threshold: u128,

        /// Turn off local solving threshold
        #[arg(long, default_value_t = false)]
        no_local_solving_threshold: bool
    },
    /// Parse and typecheck an OOX source file
    Check {
        /// The OOX source file to type check
        #[arg(num_args(0..))]
        source_paths: Vec<String>,
        /// Print the program to be evaluated.
        #[arg(short, long, default_value_t = false)]
        print: bool,
    },
    /// Generate a mutation in an OOX source file. 
    Mutate {
        /// The source files, can be multiple. They will be merged into a single file.
        #[arg(num_args(0..))]
        source_paths: Vec<String>,

        /// Upper limit of how many mutated programs to generate
        #[arg(long, default_value = None)]
        n: Option<u64>,
        
        /// Output path for the mutated program.
        #[arg(long, default_value = ".")]
        out: String
    }
}

fn main() -> Result<(), String> {
    let args = Args::parse();
    match args.command {
        Commands::Verify {
            source_paths,
            k,
            function,
            symbolic_array_size,
            quiet,
            heuristic,
            visualize_heuristic,
            visualize_coverage,
            time_budget,
            log_path,
            prune_path_z3,
            local_solving_threshold,
            no_local_solving_threshold
        } => {
            if let Some((class_name, method_name)) = function.split('.').collect_tuple() {
                let options = Options {
                    k,
                    quiet,
                    with_exceptional_clauses: true,
                    heuristic,
                    visualize_heuristic,
                    visualize_coverage,
                    symbolic_array_size,
                    time_budget,
                    log_path: &log_path,
                    discard_logs: false,
                    prune_path_z3,
                    local_solving_threshold: if no_local_solving_threshold { None } else { Some(local_solving_threshold) }
                };
                verify(source_paths.as_slice(), class_name, method_name, options)?;
            } else {
                println!("Entry point must be of the form 'class.method' and be unambiguous");
            }
        }
        Commands::Check {
            source_paths,
            print,
        } => {
            check(source_paths, print)?;
        }
        Commands::Mutate { source_paths, n, out } => {
            let mut c = CompilationUnit::empty();

            let resulting_prefix = if source_paths.len() == 1 {
                source_paths[0].split("/").last().unwrap()
            } else {
                "RESULT"
            };

            // Set global file names
            *FILE_NAMES.lock().unwrap() = source_paths.iter().map(ToString::to_string).collect();

            for (file_number, path) in (0..).zip(&source_paths) {
                let file_content = std::fs::read_to_string(path).map_err(|err| err.to_string())?;
                let file_c =
                    parse_program(&file_content, file_number, true).map_err(|error| match error {
                        lib::Error::ParseError(err) => err.to_string(),
                        lib::Error::LexerError((line, col)) => {
                            format!("Lexer error at {}:{}:{}", path, line, col)
                        }
                    })?;
                c = c.merge(file_c);
            }

            let symbol_table = SymbolTable::from_ast(&c)?;
            c = type_compilation_unit(c, &symbol_table)?;

            let mutated_units = mutate_program(&c);

            for (mutation_name, mutated_unit) in mutated_units {
                // only write the mutation if it is type correct.
                if let Ok(symbol_table) = SymbolTable::from_ast(&c) {
                    if let Ok(typed_compilation_unit) = type_compilation_unit(mutated_unit, &symbol_table) {
                        let path = format!("{}/{}_{}", out, resulting_prefix, mutation_name);
                        std::fs::write(path, typed_compilation_unit.to_string()).unwrap();
                    }
                }
            }
        },
    }

    Ok(())
}


fn check(source_paths: Vec<String>, print: bool) -> Result<(), String> {
    let mut c = CompilationUnit::empty();

    // Set global file names
    *FILE_NAMES.lock().unwrap() = source_paths.iter().map(ToString::to_string).collect();

    for (file_number, path) in (0..).zip(source_paths) {
        let file_content = std::fs::read_to_string(&path).map_err(|err| err.to_string())?;
        let file_c =
            parse_program(&file_content, file_number, false).map_err(|error| match error {
                lib::Error::ParseError(err) => err.to_string(),
                lib::Error::LexerError((line, col)) => {
                    format!("Lexer error at {}:{}:{}", path, line, col)
                }
            })?;
        c = c.merge(file_c);
    }

    c = insert_exceptional_clauses(c);
    let symbol_table = SymbolTable::from_ast(&c)?;
    c = type_compilation_unit(c, &symbol_table)?;

    if print {
        println!("{}", pretty::Pretty::pretty(&c, &BoxAllocator).1.pretty(30));
    }
    println!("Type check OK");
    Ok(())
}