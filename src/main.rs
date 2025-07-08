//! Run a given lambda calculus program and print the result to standard
//! output.
//!
//! Example usage:
//!
//!     cargo run -- \
//!         --impl-name box_tree \
//!         --src-filepath test_programs/linked_list_length.lc

use clap::Parser;
use rust_lambda_calc::end_to_end::{run_interpreter, InterpreterConfig};

fn main() {
    let interpreter_config = InterpreterConfig::parse();

    let interpreter_result = run_interpreter(&interpreter_config);

    match interpreter_result {
        Ok(execution_result) => {
            println!("{}", execution_result);
        }

        Err(run_error) => {
            println!("{}", run_error);
        }
    }
}
