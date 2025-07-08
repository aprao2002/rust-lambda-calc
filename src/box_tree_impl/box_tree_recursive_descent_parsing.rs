//! Recursive descent parser that constructs lambda-calculus programs in the
//! box-tree representation given a vector of tokens.

use std::fmt::Display;

use crate::box_tree_impl::box_tree_ast::{DefStatement, EvalStatement, ExprNode, Program};
use crate::lexical_analysis::{Token, TokenClass};

/// Represents a parsing error.
#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedTokenClass {
        expected_token_class: TokenClass,
        found_token_class: TokenClass,
        line_num: usize,
    },
    UnexpectedTokenString {
        expected_token_string: String,
        found_token_string: String,
        line_num: usize,
    },
    UnexpectedEndOfInput,
}

/// Display trait implementation for ParseError.
impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedTokenClass {
                expected_token_class,
                found_token_class,
                line_num,
            } => {
                return write!(f, "Unexpected token class in box tree recursive descent parsing at line {}. Expected: {:?}, found: {:?}.", line_num, expected_token_class, found_token_class);
            }

            Self::UnexpectedTokenString {
                expected_token_string,
                found_token_string,
                line_num,
            } => {
                return write!(f, "Unexpected token string in box tree recursive descent parsing at line {}. Expected: {:?}, found: {:?}.",line_num,  expected_token_string, found_token_string);
            }

            Self::UnexpectedEndOfInput => {
                return write!(
                    f,
                    "Unexpected end of input in box tree recursive descent parsing."
                );
            }
        }
    }
}

/// Tries to parse a token of the requested class at tokens[start_idx].
fn try_token_class(
    tokens: &Vec<Token>,
    start_idx: usize,
    token_class: TokenClass,
) -> Result<(&Token, usize), ParseError> {
    if start_idx >= tokens.len() {
        return Err(ParseError::UnexpectedEndOfInput);
    }

    match tokens[start_idx].token_class == token_class {
        true => return Ok((&tokens[start_idx], start_idx + 1)),
        false => {
            return Err(ParseError::UnexpectedTokenClass {
                expected_token_class: token_class,
                found_token_class: tokens[start_idx].token_class,
                line_num: tokens[start_idx].line_num,
            })
        }
    };
}

/// Tries to parse a token containing the requested text at tokens[start_idx].
fn try_token_text<'a, 'b>(
    tokens: &'a Vec<Token>,
    start_idx: usize,
    token_text: &'b str,
) -> Result<(&'b str, usize), ParseError> {
    if start_idx >= tokens.len() {
        return Err(ParseError::UnexpectedEndOfInput);
    }

    match tokens[start_idx].token_text == token_text {
        true => return Ok((token_text, start_idx + 1)),
        false => {
            return Err(ParseError::UnexpectedTokenString {
                expected_token_string: String::from(token_text),
                found_token_string: tokens[start_idx].token_text.clone(),
                line_num: tokens[start_idx].line_num,
            });
        }
    };
}

/// Tries to parse an expression that looks like `\[IDENTIFIER].[EXPR]`.
fn try_lambda_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Lambda)?;
    let (formal_param_token, start_idx) =
        try_token_class(tokens, start_idx, TokenClass::Identifier)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Dot)?;
    let (fn_body, start_idx) = try_expr_rule(tokens, start_idx)?;

    return Ok((
        Box::new(ExprNode::FnDef {
            formal_param: formal_param_token.token_text.clone(),
            fn_body: fn_body,
        }),
        start_idx,
    ));
}

/// Tries to parse an expression that looks like `([EXPR])`.
fn try_parenthesis_expr_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    let (_, start_idx) = try_token_text(tokens, start_idx, "(")?;
    let (expr_node, start_idx) = try_expr_rule(tokens, start_idx)?;
    let (_, start_idx) = try_token_text(tokens, start_idx, ")")?;

    return Ok((expr_node, start_idx));
}

/// Tries to parse an expression that looks like `[IDENTIFIER]`.
fn try_var_expr_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    let (var_token, start_idx) = try_token_class(tokens, start_idx, TokenClass::Identifier)?;

    return Ok((
        Box::new(ExprNode::Var {
            var_name: var_token.token_text.clone(),
        }),
        start_idx,
    ));
}

/// Tries to parse according to the production `atom -> (e) | v`.
fn try_atom_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    return try_parenthesis_expr_rule(tokens, start_idx)
        .or_else(|_| try_var_expr_rule(tokens, start_idx));
}

/// Tries to parse chains of function applications. uses the right-associative
/// rule app -> atom app | atom | lambda, but parses the sequence of terms using
/// a loop that 'fixes' the output to be left-associative.
fn try_application_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    // Try to parse at least one atom.
    let (mut out_expr, mut start_idx) = try_atom_rule(tokens, start_idx)?;

    // Keep trying to parse atoms while maintaining left associativity.
    loop {
        let next_term =
            try_atom_rule(tokens, start_idx).or_else(|_| try_lambda_rule(tokens, start_idx));

        match next_term {
            // We were able to parse another term, so add to the output while
            // ensuring left associativity.
            Ok((next_atom, new_start_idx)) => {
                out_expr = Box::new(ExprNode::FnApp {
                    fn_body: out_expr,
                    actual_arg: next_atom,
                });
                start_idx = new_start_idx;
            }

            // We were not able to parse another term, so break the loop.
            Err(_) => {
                break;
            }
        }
    }

    return Ok((out_expr, start_idx));
}

/// Tries to parse according to the production `e -> lambda | non_lam`.
fn try_expr_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    return try_lambda_rule(tokens, start_idx).or_else(|_| try_application_rule(tokens, start_idx));
}

/// Tries to parse a `def` statement.
fn try_def_statement_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(DefStatement, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Def)?;
    let (def_name_token, start_idx) = try_token_class(tokens, start_idx, TokenClass::Identifier)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Equals)?;
    let (def_body, start_idx) = try_expr_rule(tokens, start_idx)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Semicolon)?;

    return Ok((
        DefStatement {
            def_name: def_name_token.token_text.clone(),
            def_body: def_body,
        },
        start_idx,
    ));
}

/// Tries to parse an `eval` statement.
fn try_eval_statement_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(EvalStatement, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Eval)?;
    let (eval_body_box, start_idx) = try_expr_rule(tokens, start_idx)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Semicolon)?;

    return Ok((
        EvalStatement {
            eval_body: eval_body_box,
        },
        start_idx,
    ));
}

/// Uses recursive descent to parse the given vector of tokens into a `Program`
/// object (see the `box_tree_ast` module).
///
/// Assumes that the input token vector has discarded whitespace and comments
/// (i.e. it was produced via run_lexical_analysis with
/// `discard_uninteresting = true`).
pub fn parse_recursive_descent(tokens: &Vec<Token>) -> Result<Program, ParseError> {
    let mut def_statements = Vec::new();
    let mut eval_statements = Vec::new();

    let mut start_idx = 0;

    while start_idx < tokens.len() {
        if let Ok((def_statement, new_start_idx)) = try_def_statement_rule(tokens, start_idx) {
            def_statements.push(def_statement);
            start_idx = new_start_idx;
            continue;
        }

        match try_eval_statement_rule(tokens, start_idx) {
            Ok((eval_statement, new_start_idx)) => {
                eval_statements.push(eval_statement);
                start_idx = new_start_idx;
                continue;
            }

            Err(parse_error) => {
                return Err(parse_error);
            }
        }
    }

    return Ok(Program {
        def_statements: def_statements,
        eval_statements: eval_statements,
    });
}

#[cfg(test)]
mod tests {
    use crate::lexical_analysis::run_lexical_analysis;

    use super::*;

    // Test if we can parse a simple def statement.
    #[test]
    fn test_single_simple_def_statement() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"def identity = \x. x;";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_output = Program {
            def_statements: vec![DefStatement {
                def_name: String::from("identity"),
                def_body: Box::new(ExprNode::FnDef {
                    formal_param: String::from("x"),
                    fn_body: Box::new(ExprNode::Var {
                        var_name: String::from("x"),
                    }),
                }),
            }],
            eval_statements: vec![],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_output);
    }

    // Test if we can parse a simple eval statement.
    #[test]
    fn test_single_simple_eval_statement() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"eval (\x. x)(\y. y);";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_output = Program {
            def_statements: vec![],
            eval_statements: vec![EvalStatement {
                eval_body: Box::new(ExprNode::FnApp {
                    fn_body: Box::new(ExprNode::FnDef {
                        formal_param: String::from("x"),
                        fn_body: Box::new(ExprNode::Var {
                            var_name: String::from("x"),
                        }),
                    }),
                    actual_arg: Box::new(ExprNode::FnDef {
                        formal_param: String::from("y"),
                        fn_body: Box::new(ExprNode::Var {
                            var_name: String::from("y"),
                        }),
                    }),
                }),
            }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_output);
    }

    // Test if we parse function application as left associative.
    #[test]
    fn test_function_application_association() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"eval var_1 var_2 var_3;";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_output = Program {
            def_statements: vec![],
            eval_statements: vec![EvalStatement {
                eval_body: Box::new(ExprNode::FnApp {
                    fn_body: Box::new(ExprNode::FnApp {
                        fn_body: Box::new(ExprNode::Var {
                            var_name: String::from("var_1"),
                        }),
                        actual_arg: Box::new(ExprNode::Var {
                            var_name: String::from("var_2"),
                        }),
                    }),
                    actual_arg: Box::new(ExprNode::Var {
                        var_name: String::from("var_3"),
                    }),
                }),
            }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_output);
    }

    // Test if we function application association respects parentheses.
    #[test]
    fn test_function_application_association_with_parentheses() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"eval var_1 (var_2 var_3);";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_output = Program {
            def_statements: vec![],
            eval_statements: vec![EvalStatement {
                eval_body: Box::new(ExprNode::FnApp {
                    fn_body: Box::new(ExprNode::Var {
                        var_name: String::from("var_1"),
                    }),
                    actual_arg: Box::new(ExprNode::FnApp {
                        fn_body: Box::new(ExprNode::Var {
                            var_name: String::from("var_2"),
                        }),
                        actual_arg: Box::new(ExprNode::Var {
                            var_name: String::from("var_3"),
                        }),
                    }),
                }),
            }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_output);
    }

    // Test if we parse lambdas to bind to as much as possible of what follows
    // them.
    #[test]
    fn test_lambda_binding() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"def test = (\a. a \b. b) \c. c;";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_output = Program {
            def_statements: vec![DefStatement {
                def_name: String::from("test"),
                def_body: Box::new(ExprNode::FnApp {
                    fn_body: Box::new(ExprNode::FnDef {
                        formal_param: String::from("a"),
                        fn_body: Box::new(ExprNode::FnApp {
                            fn_body: Box::new(ExprNode::Var {
                                var_name: String::from("a"),
                            }),
                            actual_arg: Box::new(ExprNode::FnDef {
                                formal_param: String::from("b"),
                                fn_body: Box::new(ExprNode::Var {
                                    var_name: String::from("b"),
                                }),
                            }),
                        }),
                    }),
                    actual_arg: Box::new(ExprNode::FnDef {
                        formal_param: String::from("c"),
                        fn_body: Box::new(ExprNode::Var {
                            var_name: String::from("c"),
                        }),
                    }),
                }),
            }],
            eval_statements: vec![],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_output);
    }

    // Test if we can parse a combination of def and eval statements.
    #[test]
    fn test_eval_and_def_statements() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"
            def zero = \f. \x. x;
            def succ = \n. \f. \x. f (n f x);
            eval succ zero;
        ";
        let program_tokens = run_lexical_analysis(program_str, true);

        let expected_def_statements = vec![
            // def zero = \f. \x. x;
            DefStatement {
                def_name: String::from("zero"),
                def_body: Box::new(ExprNode::FnDef {
                    formal_param: String::from("f"),
                    fn_body: Box::new(ExprNode::FnDef {
                        formal_param: String::from("x"),
                        fn_body: Box::new(ExprNode::Var {
                            var_name: String::from("x"),
                        }),
                    }),
                }),
            },
            // def succ = \n. \f. \x. f (n f x);
            DefStatement {
                def_name: String::from("succ"),
                def_body: Box::new(ExprNode::FnDef {
                    formal_param: String::from("n"),
                    fn_body: Box::new(ExprNode::FnDef {
                        formal_param: String::from("f"),
                        fn_body: Box::new(ExprNode::FnDef {
                            formal_param: String::from("x"),
                            fn_body: Box::new(ExprNode::FnApp {
                                fn_body: Box::new(ExprNode::Var {
                                    var_name: String::from("f"),
                                }),
                                actual_arg: Box::new(ExprNode::FnApp {
                                    fn_body: Box::new(ExprNode::FnApp {
                                        fn_body: Box::new(ExprNode::Var {
                                            var_name: String::from("n"),
                                        }),
                                        actual_arg: Box::new(ExprNode::Var {
                                            var_name: String::from("f"),
                                        }),
                                    }),
                                    actual_arg: Box::new(ExprNode::Var {
                                        var_name: String::from("x"),
                                    }),
                                }),
                            }),
                        }),
                    }),
                }),
            },
        ];

        let expected_eval_statements = vec![
            // eval succ zero;
            EvalStatement {
                eval_body: Box::new(ExprNode::FnApp {
                    fn_body: Box::new(ExprNode::Var {
                        var_name: String::from("succ"),
                    }),
                    actual_arg: Box::new(ExprNode::Var {
                        var_name: String::from("zero"),
                    }),
                }),
            },
        ];

        let expected_output = Program {
            def_statements: expected_def_statements,
            eval_statements: expected_eval_statements,
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_output);
    }
}
