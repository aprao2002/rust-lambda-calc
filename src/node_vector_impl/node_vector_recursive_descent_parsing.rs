use crate::lexical_analysis::{Token, TokenClass};
use crate::node_vector_impl::node_vector_ast::{ExprNode, ExprNodeArena, Program, Statement};

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

// Tries to parse a token of the requested class at tokens[start_idx].
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

// Tries to parse a token containing the requested text at tokens[start_idx].
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

// Tries to parse an expression that looks like `\[IDENTIFIER].[EXPR]`.
fn try_lambda_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(ExprNode, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Lambda)?;
    let (formal_param_token, start_idx) =
        try_token_class(tokens, start_idx, TokenClass::Identifier)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Dot)?;
    let (fn_body, start_idx) = try_expr_rule(tokens, program, start_idx)?;

    program.expr_nodes.push(fn_body);

    return Ok((
        ExprNode::FnDef {
            formal_param: formal_param_token.token_text.clone(),
            fn_body_idx: program.expr_nodes.len() - 1,
        },
        start_idx,
    ));
}

// Tries to parse an expression that looks like `([EXPR])`.
fn try_parenthesis_expr_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(ExprNode, usize), ParseError> {
    let (_, start_idx) = try_token_text(tokens, start_idx, "(")?;
    let (expr_node, start_idx) = try_expr_rule(tokens, program, start_idx)?;
    let (_, start_idx) = try_token_text(tokens, start_idx, ")")?;

    return Ok((expr_node, start_idx));
}

// Tries to parse an expression that looks like `[IDENTIFIER]`.
fn try_var_expr_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(ExprNode, usize), ParseError> {
    let (var_token, start_idx) = try_token_class(tokens, start_idx, TokenClass::Identifier)?;

    return Ok((
        ExprNode::Var {
            var_name: var_token.token_text.clone(),
        },
        start_idx,
    ));
}

// Tries to parse according to the production `atom -> (e) | v`.
fn try_atom_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(ExprNode, usize), ParseError> {
    let old_arena_next_idx = program.expr_nodes.get_next_idx();

    return try_parenthesis_expr_rule(tokens, program, start_idx).or_else(|_| {
        program.expr_nodes.set_next_idx(old_arena_next_idx);
        return try_var_expr_rule(tokens, start_idx);
    });
}

// Tries to parse chains of function applications. uses the right-associative
// rule app -> atom e | atom, but parses the sequence of terms using a loop that
// 'fixes' the output to be left-associative.
fn try_application_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(ExprNode, usize), ParseError> {
    // Try to parse at least one atom.
    let (mut out_expr, mut start_idx) = try_atom_rule(tokens, program, start_idx)?;

    // Keep trying to parse atoms while maintaining left associativity.
    loop {
        let prev_iter_arena_next_idx = program.expr_nodes.get_next_idx();

        let next_term = try_atom_rule(tokens, program, start_idx).or_else(|_| {
            program.expr_nodes.set_next_idx(prev_iter_arena_next_idx);
            return try_lambda_rule(tokens, program, start_idx);
        });

        match next_term {
            // We were able to parse another term, so add to the output while
            // ensuring left associativity.
            Ok((next_atom, new_start_idx)) => {
                program.expr_nodes.push(out_expr);
                let out_expr_idx = program.expr_nodes.len() - 1;

                program.expr_nodes.push(next_atom);
                let next_atom_idx = program.expr_nodes.len() - 1;

                out_expr = ExprNode::FnApp {
                    fn_body_idx: out_expr_idx,
                    actual_arg_idx: next_atom_idx,
                };
                start_idx = new_start_idx;
            }

            // We were not able to parse another term, so break the loop.
            Err(_) => {
                program.expr_nodes.set_next_idx(prev_iter_arena_next_idx);
                break;
            }
        }
    }

    return Ok((out_expr, start_idx));
}

// Tries to parse according to the production `e -> lambda | non_lam`.
fn try_expr_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(ExprNode, usize), ParseError> {
    let old_arena_next_idx = program.expr_nodes.get_next_idx();

    return try_lambda_rule(tokens, program, start_idx).or_else(|_| {
        program.expr_nodes.set_next_idx(old_arena_next_idx);
        return try_application_rule(tokens, program, start_idx);
    });
}

// Tries to parse a `def` statement.
fn try_def_statement_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(Statement, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Def)?;
    let (def_name_token, start_idx) = try_token_class(tokens, start_idx, TokenClass::Identifier)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Equals)?;
    let (def_body, start_idx) = try_expr_rule(tokens, program, start_idx)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Semicolon)?;

    program.expr_nodes.push(def_body);

    return Ok((
        Statement::Def {
            def_name: def_name_token.token_text.clone(),
            def_body_idx: program.expr_nodes.len() - 1,
        },
        start_idx,
    ));
}

// Tries to parse an `eval` statement.
fn try_eval_statement_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(Statement, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Eval)?;
    let (eval_body, start_idx) = try_expr_rule(tokens, program, start_idx)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Semicolon)?;

    program.expr_nodes.push(eval_body);

    return Ok((
        Statement::Eval {
            eval_body_idx: program.expr_nodes.len() - 1,
        },
        start_idx,
    ));
}

// Tries to parse a `def` or `eval` statement.
fn try_statement_rule(
    tokens: &Vec<Token>,
    program: &mut Program,
    start_idx: usize,
) -> Result<(Statement, usize), ParseError> {
    let old_arena_next_idx = program.expr_nodes.get_next_idx();

    return try_def_statement_rule(tokens, program, start_idx).or_else(|_| {
        program.expr_nodes.set_next_idx(old_arena_next_idx);
        return try_eval_statement_rule(tokens, program, start_idx);
    });
}

/// Uses recursive descent to parse the given vector of tokens into a vector of
/// `def` or `eval` statements.
///
/// Assumes that the input token vector has discarded whitespace and comments
/// (i.e. it was produced via run_lexical_analysis with
/// `discard_uninteresting = true`).
pub fn parse_recursive_descent(tokens: &Vec<Token>) -> Result<Program, ParseError> {
    let mut start_idx = 0;

    let mut program = Program {
        expr_nodes: ExprNodeArena::new(None),
        statements: Vec::new(),
    };

    let original_arena_next_idx = program.expr_nodes.get_next_idx();

    while start_idx < tokens.len() {
        let try_statement_output = try_statement_rule(tokens, &mut program, start_idx);

        match try_statement_output {
            Ok((statement, new_idx)) => {
                program.statements.push(statement);
                start_idx = new_idx;
            }

            Err(parse_error) => {
                program.expr_nodes.set_next_idx(original_arena_next_idx);
                return Err(parse_error);
            }
        };
    }

    return Ok(program);
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
        let expected_expr_nodes = vec![
            ExprNode::FnDef {
                formal_param: String::from("x"),
                fn_body_idx: 1,
            },
            ExprNode::Var {
                var_name: String::from("x"),
            },
        ];

        let expected_program = Program {
            expr_nodes: ExprNodeArena::from_vec(expected_expr_nodes, None),
            statements: vec![Statement::Def {
                def_name: String::from("identity"),
                def_body_idx: 0,
            }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_program);
    }

    // Test if we can parse a simple eval statement.
    #[test]
    fn test_single_simple_eval_statement() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"eval (\x. x)(\y. y);";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_expr_nodes = vec![
            // 0: (\x. x)(\y. y)
            ExprNode::FnApp {
                fn_body_idx: 1,
                actual_arg_idx: 3,
            },
            // 1: \x. x
            ExprNode::FnDef {
                formal_param: String::from("x"),
                fn_body_idx: 2,
            },
            // 2: x
            ExprNode::Var {
                var_name: String::from("x"),
            },
            // 3: \y. y
            ExprNode::FnDef {
                formal_param: String::from("y"),
                fn_body_idx: 4,
            },
            // 4: y
            ExprNode::Var {
                var_name: String::from("y"),
            },
        ];

        let expected_program = Program {
            expr_nodes: ExprNodeArena::from_vec(expected_expr_nodes, None),
            statements: vec![Statement::Eval { eval_body_idx: 0 }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_program);
    }

    // Test if we parse function application as left associative.
    #[test]
    fn test_function_application_association() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"eval var_1 var_2 var_3;";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_expr_nodes = vec![
            // 0: var_1 var_2 var_3
            ExprNode::FnApp {
                fn_body_idx: 1,
                actual_arg_idx: 4,
            },
            // 1: var_1 var_2
            ExprNode::FnApp {
                fn_body_idx: 2,
                actual_arg_idx: 3,
            },
            // 2: var_1
            ExprNode::Var {
                var_name: String::from("var_1"),
            },
            // 3: var_2
            ExprNode::Var {
                var_name: String::from("var_2"),
            },
            // 4: var_3
            ExprNode::Var {
                var_name: String::from("var_3"),
            },
        ];

        let expected_program = Program {
            expr_nodes: ExprNodeArena::from_vec(expected_expr_nodes, None),
            statements: vec![Statement::Eval { eval_body_idx: 0 }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_program);
    }

    // Test if we function application association respects parentheses.
    #[test]
    fn test_function_application_association_with_parentheses() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"eval var_1 (var_2 var_3);";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_expr_nodes = vec![
            // 0: var_1 (var_2 var_3)
            ExprNode::FnApp {
                fn_body_idx: 1,
                actual_arg_idx: 2,
            },
            // 1: var_1
            ExprNode::Var {
                var_name: String::from("var_1"),
            },
            // 2: var_2 var_3
            ExprNode::FnApp {
                fn_body_idx: 3,
                actual_arg_idx: 4,
            },
            // 3: var_2
            ExprNode::Var {
                var_name: String::from("var_2"),
            },
            // 4: var_3
            ExprNode::Var {
                var_name: String::from("var_3"),
            },
        ];

        let expected_program = Program {
            expr_nodes: ExprNodeArena::from_vec(expected_expr_nodes, None),
            statements: vec![Statement::Eval { eval_body_idx: 0 }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_program);
    }

    // Test if we parse lambdas to bind to as much as possible of what follows
    // them.
    #[test]
    fn test_lambda_binding() {
        // Initialize the test program string and run the lexer on it.
        let program_str = r"def test = (\a. a \b. b) \c. c;";
        let program_tokens = run_lexical_analysis(program_str, true);

        // Initialize the expected output.
        let expected_expr_nodes = vec![
            // 0: (\a. a \b. b) \c. c
            ExprNode::FnApp {
                fn_body_idx: 1,
                actual_arg_idx: 6,
            },
            // 1: \a. a \b. b
            ExprNode::FnDef {
                formal_param: String::from("a"),
                fn_body_idx: 2,
            },
            // 2: a \b. b
            ExprNode::FnApp {
                fn_body_idx: 3,
                actual_arg_idx: 4,
            },
            // 3: a
            ExprNode::Var {
                var_name: String::from("a"),
            },
            // 4: \b. b
            ExprNode::FnDef {
                formal_param: String::from("b"),
                fn_body_idx: 5,
            },
            // 5: b
            ExprNode::Var {
                var_name: String::from("b"),
            },
            // 6: \c. c
            ExprNode::FnDef {
                formal_param: String::from("c"),
                fn_body_idx: 7,
            },
            // 7: c
            ExprNode::Var {
                var_name: String::from("c"),
            },
        ];

        let expected_program = Program {
            expr_nodes: ExprNodeArena::from_vec(expected_expr_nodes, None),
            statements: vec![Statement::Def {
                def_name: String::from("test"),
                def_body_idx: 0,
            }],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_program);
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

        // Initialize the expected output.
        let expected_expr_nodes = vec![
            // ---- def zero = \f. \x. x; ----
            // 0: \f. \x. x
            ExprNode::FnDef {
                formal_param: String::from("f"),
                fn_body_idx: 1,
            },
            // 1: \x. x
            ExprNode::FnDef {
                formal_param: String::from("x"),
                fn_body_idx: 2,
            },
            // 2: x
            ExprNode::Var {
                var_name: String::from("x"),
            },
            // ---- def succ = \n. \f. \x. f (n f x); ----
            // 3: \n. \f. \x. f (n f x)
            ExprNode::FnDef {
                formal_param: String::from("n"),
                fn_body_idx: 4,
            },
            // 4: \f. \x. f (n f x)
            ExprNode::FnDef {
                formal_param: String::from("f"),
                fn_body_idx: 5,
            },
            // 5: \x. f (n f x)
            ExprNode::FnDef {
                formal_param: String::from("x"),
                fn_body_idx: 6,
            },
            // 6: f (n f x)
            ExprNode::FnApp {
                fn_body_idx: 7,
                actual_arg_idx: 8,
            },
            // 7: f
            ExprNode::Var {
                var_name: String::from("f"),
            },
            // 8: n f x
            ExprNode::FnApp {
                fn_body_idx: 9,
                actual_arg_idx: 12,
            },
            // 9: n f
            ExprNode::FnApp {
                fn_body_idx: 10,
                actual_arg_idx: 11,
            },
            // 10: n
            ExprNode::Var {
                var_name: String::from("n"),
            },
            // 11: f
            ExprNode::Var {
                var_name: String::from("f"),
            },
            // 12: x
            ExprNode::Var {
                var_name: String::from("x"),
            },
            // ---- eval succ zero; ----
            // 13: succ zero
            ExprNode::FnApp {
                fn_body_idx: 14,
                actual_arg_idx: 15,
            },
            // 14: succ
            ExprNode::Var {
                var_name: String::from("succ"),
            },
            // 15: zero
            ExprNode::Var {
                var_name: String::from("zero"),
            },
        ];

        let expected_program = Program {
            expr_nodes: ExprNodeArena::from_vec(expected_expr_nodes, None),
            statements: vec![
                Statement::Def {
                    def_name: String::from("zero"),
                    def_body_idx: 0,
                },
                Statement::Def {
                    def_name: String::from("succ"),
                    def_body_idx: 3,
                },
                Statement::Eval { eval_body_idx: 13 },
            ],
        };

        // Run the parser.
        let generated_output = parse_recursive_descent(&program_tokens)
            .expect("parse_recursive_descent returned unexpected parse error");

        // Check parser output matches expected output.
        assert_eq!(generated_output, expected_program);
    }
}
