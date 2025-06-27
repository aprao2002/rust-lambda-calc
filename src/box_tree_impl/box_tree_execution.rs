//! Executes lambda-calculus programs given in the box-tree program
//! representation.

use std::collections::{HashMap, HashSet};

use crate::box_tree_impl::box_tree_ast::{
    get_all_free_variables, get_all_variables, make_def_map, rename_variable, ExprNode, Program,
};

/// Represents the result of box-tree program execution.
pub type ExecutionResult = Vec<Box<ExprNode>>;

/// Converts an ExecutionResult to a String.
pub fn execution_result_to_string(execution_result: &ExecutionResult) -> String {
    let mut out = vec![];

    for expr_node_box in execution_result {
        out.push((**expr_node_box).to_string());
    }

    return out.join("\n");
}

/// Given an ExprNode, a formal param to rename, and the free variables of a
/// value being substituted into the ExprNode, rename the formal_param so that
/// we don't accidentally introduce new references to the formal_param.
fn perform_alpha_conversion(
    formal_param: &str,
    fn_body: &mut ExprNode,
    value_free_vars: &HashSet<&str>,
) {
    assert!(
        value_free_vars.contains(formal_param),
        "Alpha conversion attempted when not required."
    );

    let all_fn_body_vars = get_all_variables(fn_body);
    let vars_to_avoid: HashSet<&str> = all_fn_body_vars.union(value_free_vars).copied().collect();

    let mut new_formal_param = String::from(formal_param);

    while vars_to_avoid.contains(new_formal_param.as_str()) {
        new_formal_param = new_formal_param + "'";
    }

    rename_variable(formal_param, new_formal_param.as_str(), fn_body);
}

/// Performs beta reduction on expr_body, substituting instances of var_name
/// with var_value. Performs alpha conversion while doing substitutions if
/// needed.
fn perform_beta_reduction_helper(
    expr_body: &mut ExprNode,
    var_name: &str,
    var_value: &ExprNode,
    value_free_vars: &HashSet<&str>,
) {
    match expr_body {
        // Substitute into variable.
        ExprNode::Var {
            var_name: curr_var_name,
        } => {
            if curr_var_name == var_name {
                *expr_body = var_value.clone();
            }
        }

        // Substitute onto function application.
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            perform_beta_reduction_helper(&mut **fn_body, var_name, var_value, value_free_vars);
            perform_beta_reduction_helper(&mut **actual_arg, var_name, var_value, value_free_vars);
        }

        // Substitute onto function definition.
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            // Only try to substitute if the formal param doesn't shadow
            // var_name.
            if formal_param != var_name {
                // To prevent variable capture, perform alpha conversion if
                // var_value contains formal_param as a free variable.
                if value_free_vars.contains(formal_param.as_str()) {
                    perform_alpha_conversion(
                        formal_param.as_str(),
                        &mut **fn_body,
                        value_free_vars,
                    );
                }

                perform_beta_reduction_helper(&mut **fn_body, var_name, var_value, value_free_vars);
            }
        }
    };
}

/// Performs beta reduction on expr_body, replacing instances of var_name
/// with var_value.
fn perform_beta_reduction(expr_body: &mut ExprNode, var_name: &str, var_value: &ExprNode) {
    let value_free_vars = get_all_free_variables(var_value);
    perform_beta_reduction_helper(expr_body, var_name, var_value, &value_free_vars);
}

fn dummy_value() -> Box<ExprNode> {
    return Box::new(ExprNode::Var {
        var_name: String::from(""),
    });
}

/// Performs lazy evaluation of a given lambda calculus expression until it is
/// in weak-head normal form. Returns a Box holding the evaluated expression,
/// and a boolean saying whether the result is different from the input
/// expression.
fn eval_expr_lazy(
    mut expr_body: Box<ExprNode>,
    def_statement_map: &HashMap<&str, &ExprNode>,
    verbose: bool,
) -> (Box<ExprNode>, bool) {
    let mut change_made = false;

    // Keep trying to apply substitution until we are no longer at a redex.
    loop {
        if verbose {
            println!("In eval_expr_lazy, expr_body is {}", &*expr_body);
        }

        // Inspect the topmost node of the AST.
        match &mut *expr_body {
            // The topmost node is a function application, so see if it is a redex.
            ExprNode::FnApp {
                fn_body,
                actual_arg,
            } => {
                match &mut **fn_body {
                    // The function being applied is a function definition, so
                    // we are at a redex.
                    ExprNode::FnDef {
                        formal_param,
                        fn_body: defined_fn,
                    } => {
                        perform_beta_reduction(
                            &mut *defined_fn,
                            formal_param.as_str(),
                            &*actual_arg,
                        );

                        expr_body = std::mem::replace(defined_fn, dummy_value());

                        change_made = true;
                        continue;
                    }

                    // The function being applied is a variable name. First
                    // expand it if it is actually a def statement macro.
                    ExprNode::Var { var_name } => {
                        // The variable is a def statement macro.
                        if def_statement_map.contains_key(var_name.as_str()) {
                            let new_fn_body = Box::new(
                                (*def_statement_map.get(var_name.as_str()).expect(
                                    "Unable to get expansion of def statement macro {var_name}.",
                                ))
                                .clone(),
                            );

                            *fn_body = new_fn_body;

                            change_made = true;
                            continue;
                        }
                        // The variable is not a def statement macro.
                        else {
                            break;
                        }
                    }

                    // The inner function is a function application, so evaluate
                    // the inner function.
                    fn_body_val => {
                        if verbose {
                            println!("Recursing on {fn_body_val}.")
                        }

                        let (new_fn_body, new_fn_body_is_different) = eval_expr_lazy(
                            std::mem::replace(fn_body, dummy_value()),
                            def_statement_map,
                            verbose,
                        );

                        *fn_body = new_fn_body;

                        if verbose {
                            println!("Recursion complete.")
                        }

                        if new_fn_body_is_different {
                            change_made = true;
                            continue;
                        } else {
                            break;
                        }
                    }
                }
            }

            // The expr_body is not a function application, so it is not a
            // redex. Because of this, we can break.
            _ => {
                break;
            }
        };
    }

    return (expr_body, change_made);
}

/// Execute a lambda calculus program in box-tree representation.
pub fn execute_program(program: Program, verbose: bool) -> ExecutionResult {
    // First build a map from def_name -> def_body.
    let def_map = make_def_map(&program.def_statements);

    // For each statement, if it is an eval, perform the evaluation.
    let mut exec_result: Vec<Box<ExprNode>> = Vec::new();

    for eval_statement in program.eval_statements {
        let (eval_result, _) = eval_expr_lazy(eval_statement.eval_body, &def_map, verbose);
        exec_result.push(eval_result);
    }

    return exec_result;
}

#[cfg(test)]
mod tests {
    use std::iter::zip;

    use crate::{
        box_tree_impl::box_tree_recursive_descent_parsing::parse_recursive_descent,
        lexical_analysis::run_lexical_analysis,
    };

    use super::*;

    // Executes program_str and verifies that the outputs matches
    // expected_str_outputs.
    fn run_execution_test(program_str: &str, expected_str_outputs: &Vec<&str>) {
        let program_tokens = run_lexical_analysis(program_str, true);
        let program =
            parse_recursive_descent(&program_tokens).expect("Unable to parse program string.");

        let exec_result = execute_program(program, true);

        let exec_string_results: Vec<String> = exec_result
            .iter()
            .map(|expr_node| format!("{}", **expr_node))
            .collect();

        zip(expected_str_outputs.iter(), exec_string_results.iter()).for_each(
            |(expected_str_output, received_str_output)| {
                assert_eq!(*expected_str_output, received_str_output.as_str());
            },
        );
    }

    // Test eval_expr_lazy on a few simple programs.
    #[test]
    fn test_eval_expr_lazy_simple() {
        let program_strs_and_expected_outputs = vec![
            (r"eval (\x. x y) (\z. z);", vec![r"y"]),
            (
                r"eval (\a. \b. a b) ( (\x. x) (\y. y) );",
                vec![r"\b. (\x. x) (\y. y) b"],
            ),
            (r"eval a b c;", vec![r"a b c"]),
            (r"eval (\x. x) (\y. y) (\z. z);", vec![r"\z. z"]),
        ];

        for (program_str, expected_output) in program_strs_and_expected_outputs {
            run_execution_test(program_str, &expected_output);
        }
    }

    // Test eval_expr_lazy on addition with numbers in Church encoding.
    #[test]
    fn test_eval_expr_addition() {
        let addition_program_str = r"
            def zero = \f. \x. x;
            def succ = \n. \f. \x. f (n f x);
            
            def one = succ zero;
            def two = succ succ zero;

            def add = \m. \n. m succ n;

            eval (add one two) f x;
        ";

        let addition_expected_output = vec![r"f (zero succ two f x)"];

        run_execution_test(addition_program_str, &addition_expected_output);
    }

    // Test eval_expr_lazy on counting the length of a linked list.
    #[test]
    fn test_eval_expr_linked_list_length() {
        let linked_list_length_program_str = r"
            def cons = \h. \t. \f. \x. f h (t f x);
            def nil = \f. \x. x;

            def test_list = cons e1 (cons e2 nil);
            
            def cons_case_fn = \h. \t. succ t; 

            eval test_list cons_case_fn zero;
        ";

        let linked_list_length_expected_output = vec![r"succ (cons e2 nil cons_case_fn zero)"];

        run_execution_test(
            linked_list_length_program_str,
            &linked_list_length_expected_output,
        );
    }
}
