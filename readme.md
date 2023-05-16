
# How to run (in release):

`cargo run --release -- "./examples/intLinkedList.oox" --heuristic depth-first-search --function Node.test2 --k 50`
If you want to run in debug mode, remove the --release before the --.


# Editor tips
In vscode, you can add settings for file associations. Since OOX is somewhat similar to Java syntax, we can use this to our advantage.
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

