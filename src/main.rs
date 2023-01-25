use lib::playground;

#[macro_use]
extern crate slog;
use slog::Drain;
use std::sync::Mutex;

/// # Examples
///
/// ```
/// let x = 5;
/// ```
fn main() {
    // playground();
    // let log = slog::Logger::root(
    //     Mutex::new(
    //         slog_bunyan::default(
    //             std::io::stdout()
    //         )
    //     ).fuse(),
    //     o!()
    // );
    
    // // log.new(values)
    // info!(log, "all gucci here"; "stage" => "start");
}


