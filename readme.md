
# How to run (in release):

`cargo run --release -- "./examples/intLinkedList.oox" --heuristic depth-first-search --function Node.test2 --k 50`
If you want to run in debug mode, remove the --release before the --.


# Tests
`cargo test --release`
I recommend running the tests with the `--release` flag unless you are debugging, to speed it up.

# Editor tips
I recommend to use the visual studio code editor, with the 'rust analyzer' extension.

In vscode, you can add settings for file associations. Since OOX is somewhat similar to Java syntax, we can use this to add syntax highlighting to `.oox` files.
Lookup 'File associations' in settings and add *.oox : java

# Logging
The project uses a library 'slog' for logging purposes.
There are some macros provided by the library that look similar to existing macros, like debug!() and dbg!(). 
The first is from slog the latter is from the Rust itself.

To pretty print a log: 
debug!(logger, "message"; "key1" => #?value, key2 => "string value");

The #? prefix ensures the pretty-print: 
https://docs.rs/slog/latest/slog/trait.Value.html

other log macro's exist such as info!(..), warning!(..), etc.


Running the project with the `--release` flag will disable any debug or below logs.
This can be changed with feature flags from slog: https://docs.rs/crate/slog/latest/features

# Minor issues
- Error path does not point to the right file
    - This can occur when multiple tests are ran after one another due to the way I implemented global files....
    - When running the test in isolation this will not happen.