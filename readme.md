

# Logging
The project uses a library 'slog' for logging purposes.
There are some macros provided by the library that look similar to existing macros, like debug!() and dbg!(). 
The first is from slog the latter is from the Rust itself.

To pretty print a log: 
debug!(logger, "message"; "key1" => #?value, key2 => "string value");

The #? prefix ensures the pretty-print: 
https://docs.rs/slog/latest/slog/trait.Value.html

other log macro's exist such as info!(..), warning!(..), etc.