use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::box_tree_impl::box_tree_ast::{
    get_all_free_variables, get_all_variables, make_def_map, rename_variable, ExprNode, Statement,
};

// Given an ExprNode, a formal param to rename, and the free variables of a
// value being substituted into the ExprNode, rename the formal_param so that
// we don't accidentally introduce new references to the formal_param.
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

// Performs beta reduction on expr_body, substituting instances of var_name
// with var_value. Performs alpha conversion while doing substitutions if
// needed.
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

// Performs beta reduction on expr_body, replacing instances of var_name
// with var_value.
fn perform_beta_reduction(expr_body: &mut ExprNode, var_name: &str, var_value: &ExprNode) {
    let value_free_vars = get_all_free_variables(var_value);
    perform_beta_reduction_helper(expr_body, var_name, var_value, &value_free_vars);
}

// Performs lazy / normal order evaluation of a given lambda calculus
// expression.
fn eval_expr_lazy(
    mut expr_body: Box<ExprNode>,
    def_statement_map: &HashMap<&str, &ExprNode>,
    verbose: bool,
) -> Box<ExprNode> {
    let mut parsed_left = false;

    // Keep trying to apply substitution until we are no longer at a redex.
    loop {
        if verbose {
            println!("In eval_expr_lazy, expr_body is {}", &*expr_body);
        }

        match *expr_body {
            // The expr_body is a function application, so see if it is a redex.
            ExprNode::FnApp {
                fn_body,
                actual_arg,
            } => {
                match *fn_body {
                    // The function being applied is a function definition, so
                    // we are at a redex.
                    ExprNode::FnDef {
                        formal_param,
                        fn_body: mut defined_fn,
                    } => {
                        parsed_left = false;

                        perform_beta_reduction(
                            &mut *defined_fn,
                            formal_param.as_str(),
                            &*actual_arg,
                        );

                        *expr_body = *defined_fn;
                        continue;
                    }

                    // The function being applied is a variable name. First
                    // expand it if it is actually a def statement macro.
                    ExprNode::Var { var_name } => {
                        parsed_left = false;

                        // The variable is a def statement macro.
                        if def_statement_map.contains_key(var_name.as_str()) {
                            let new_fn_body = Box::new(
                                (*def_statement_map.get(var_name.as_str()).expect(
                                    "Unable to get expansion of def statement macro {var_name}.",
                                ))
                                .clone(),
                            );

                            *expr_body = ExprNode::FnApp {
                                fn_body: new_fn_body,
                                actual_arg: actual_arg,
                            };

                            continue;
                        }
                        // The variable is not a def statement macro.
                        else {
                            *expr_body = ExprNode::FnApp {
                                fn_body: Box::new(ExprNode::Var { var_name }),
                                actual_arg: actual_arg,
                            };

                            break;
                        }
                    }

                    // The inner function is a function application, so evaluate
                    // the inner function.
                    fn_body_val => {
                        if !parsed_left {
                            if verbose {
                                println!("Recursing on {fn_body_val}.")
                            }

                            *expr_body = ExprNode::FnApp {
                                fn_body: eval_expr_lazy(
                                    Box::new(fn_body_val),
                                    def_statement_map,
                                    verbose,
                                ),
                                actual_arg: actual_arg,
                            };

                            if verbose {
                                println!("Recursion complete.")
                            }

                            parsed_left = true;
                            continue;
                        } else {
                            *expr_body = ExprNode::FnApp {
                                fn_body: Box::new(fn_body_val),
                                actual_arg: actual_arg,
                            };

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

    return expr_body;
}

/// Execute a lambda calculus program.
pub fn execute_program(program: Vec<Statement>, verbose: bool) -> Vec<Box<ExprNode>> {
    // First build a map from def_name -> def_body.
    let cloned_program = program.clone();
    let def_map = make_def_map(&cloned_program);

    // For each statement, if it is an eval, perform the evaluation.
    let mut exec_result: Vec<Box<ExprNode>> = Vec::new();

    for statement in program {
        if let Statement::Eval { eval_body } = statement {
            exec_result.push(eval_expr_lazy(eval_body, &def_map, verbose));
        }
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
