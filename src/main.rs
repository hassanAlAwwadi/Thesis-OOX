

use clap::{Parser, Subcommand};
use itertools::Itertools;
use lib::{
    insert_exceptional_clauses, parse_program, type_compilation_unit, verify, CompilationUnit, Heuristic, Options, SourcePos, SymResult, SymbolTable, FILE_NAMES
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
        no_local_solving_threshold: bool,

        /// Run as a benchmark, exporting results to the file 'benchmark'
        #[arg(long, default_value_t = false)]
        run_as_benchmark: bool,

        /// When run as a benchmark, repeat for this often
        #[arg(long, default_value_t = 3)]
        benchmark_repeat: u64,

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

        /// Output path for the mutated program.
        #[arg(short, long, default_value = ".")]
        out: String,

        /// Methods to exclude from mutation, in the form `Main.test`
        #[arg(short, long, num_args(0..))]
        exclude: Vec<String>,
    },
}

fn main() -> Result<(), String> {
    if let Some((class_name, method_name)) = Some(("Main", "main")) {
        let k = 200;
        let quiet = false;
        let heuristic = Heuristic::PathMerging;
        let visualize_heuristic= false;
        let visualize_coverage = false;
        let time_budget = 900;
        let symbolic_array_size = 100;
    
        let options = Options {
            k,
            quiet,
            with_exceptional_clauses: true,
            heuristic,
            visualize_heuristic,
            visualize_coverage,
            symbolic_array_size,
            time_budget,
            log_path: "log/log.txt",
            discard_logs: true,
            prune_path_z3: false,
            local_solving_threshold: None
        };

        let source_paths = vec!["./benchmark_programs/experiment_m/0.oox"];
        let (sym_result_1, sym_result_2, _statistics) =
            verify(source_paths.as_slice(), class_name, method_name, options)?;
        println!("merging got result: {:?}, depth_first got result {:?}", sym_result_1, sym_result_2)
        /* 
        let result_text = result_text(sym_result_1, source_paths);

        if options.quiet && sym_result_1 != SymResult::Valid {
            println!("{}", result_text);
        } else if !options.quiet {
            println!("Statistics");
            println!("  Final result:     {}", result_text);
            println!("  time:             {:?}s", duration.as_secs_f64());
            println!("  #branches:        {}", statistics.number_of_branches);
            println!("  #prunes:          {}", statistics.number_of_prunes);
            println!(
                "  #complete_paths:  {}",
                statistics.number_of_complete_paths
            );
            println!("  #locally_solved:  {}", statistics.number_of_local_solves);
            println!(
                "  #Z3 invocations:  {}",
                statistics.number_of_z3_invocations
            );
            println!(
                "  #paths explored:  {}",
                statistics.number_of_paths_explored
            );
            println!(
                "  #coverage:        {}/{} ({:.1}%)",
                statistics.covered_statements,
                statistics.reachable_statements,
                (statistics.covered_statements as f32
                    / statistics.reachable_statements as f32)
                    * 100.0
            )
            
        }
        */
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

fn result_text(sym_result: SymResult, source_paths: &[String]) -> String {
    match sym_result {
        SymResult::Valid => "VALID".to_string(),
        SymResult::Invalid(SourcePos::SourcePos {
            line,
            col,
            file_number,
        }) => {
            format!("INVALID at {}:{}:{}", source_paths[file_number], line, col)
        }
        SymResult::Invalid(SourcePos::UnknownPosition) => "INVALID at unknown position".to_string(),
    }
}
