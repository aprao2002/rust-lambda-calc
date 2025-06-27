//! Code to configure and run the interpreter on an input source code file.

use std::fs;

use clap::Parser;

use crate::box_tree_impl::{box_tree_execution, box_tree_recursive_descent_parsing};
use crate::lexical_analysis::run_lexical_analysis;

/// Supported interpreter implemenations.
pub const SUPPORTED_IMPLS: [&str; 1] = ["box_tree"];

/// Config for the interpreter. Instantiate via `InterpterConfig::parse()`.
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct InterpreterConfig {
    /// Which implemenation to use. Must be present inside `SUPPORTED_IMPLS`.
    #[arg(short, long, default_value_t = String::from("box_tree"))]
    pub impl_name: String,

    /// The input filepath to run on.
    #[arg(short, long)]
    pub src_filepath: String,
}

/// Errors that may be thrown when running the interpreter.
#[derive(Debug)]
pub enum RunError {
    ConfigError(String),
    InputFileError(std::io::Error),
    BoxTreeParseError(box_tree_recursive_descent_parsing::ParseError),
}

/// Display trait implementation for RunError.
impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConfigError(config_err_string) => {
                return write!(f, "Interpreter configuration error: {}", config_err_string);
            }

            Self::InputFileError(io_err) => {
                return write!(f, "Input file error: {}", io_err);
            }

            Self::BoxTreeParseError(box_tree_parse_error) => {
                return write!(f, "Box tree parse error: {}", box_tree_parse_error);
            }
        }
    }
}

/// Type conversions for errors.
impl From<std::io::Error> for RunError {
    fn from(value: std::io::Error) -> Self {
        return Self::InputFileError(value);
    }
}

impl From<box_tree_recursive_descent_parsing::ParseError> for RunError {
    fn from(value: box_tree_recursive_descent_parsing::ParseError) -> Self {
        return Self::BoxTreeParseError(value);
    }
}

/// Run the box-tree interpreter based on the given config.
pub fn run_box_tree_interpreter(config: &InterpreterConfig) -> Result<String, RunError> {
    // Read the input file into a string.
    let program_string = fs::read_to_string(&config.src_filepath)?;

    // Run lexer.
    let tokens = run_lexical_analysis(program_string.as_str(), true);

    // Run parser.
    let program = box_tree_recursive_descent_parsing::parse_recursive_descent(&tokens)?;

    // Execute the program.
    let execution_result = box_tree_execution::execute_program(program, false);

    // Return the result.
    return Ok(box_tree_execution::execution_result_to_string(
        &execution_result,
    ));
}

/// Run an interpreter (i.e. the lexer, parser, and code execution) given an
/// interpreter config.
pub fn run_interpreter(config: &InterpreterConfig) -> Result<String, RunError> {
    if config.impl_name == "box_tree" {
        return run_box_tree_interpreter(config);
    }

    return Err(RunError::ConfigError(format!(
        "Unrecognized implementation name {}",
        config.impl_name
    )));
}
