use std::collections::{HashMap, HashSet};

use crate::program_representation::{
    get_all_free_variables, get_all_variables, make_def_map, rename_variable,
};
use crate::program_representation::{ExprNode, Statement};

fn perform_alpha_conversion(
    formal_param: &str,
    fn_body: &mut ExprNode,
    value_free_vars: &HashSet<&str>,
) {
    let all_fn_body_vars = get_all_variables(fn_body);
    let vars_to_avoid: HashSet<&str> = all_fn_body_vars.union(value_free_vars).copied().collect();

    let mut new_formal_param = String::from(formal_param);

    while vars_to_avoid.contains(new_formal_param.as_str()) {
        new_formal_param = new_formal_param + "'";
    }

    rename_variable(formal_param, new_formal_param.as_str(), fn_body);
}

fn perform_beta_substitution_helper(
    expr_body: &ExprNode,
    var_name: &str,
    var_value: &ExprNode,
    value_free_vars: &HashSet<&str>,
) -> Box<ExprNode> {
    match expr_body {
        // Substitute into variable.
        ExprNode::Var {
            var_name: curr_var_name,
        } => {
            if curr_var_name == var_name {
                return Box::new(var_value.clone());
            }
            return Box::new(ExprNode::Var {
                var_name: curr_var_name.clone(),
            });
        }

        // Substitute onto function application.
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            let subbed_fn_body =
                perform_beta_substitution_helper(&**fn_body, var_name, var_value, value_free_vars);
            let subbed_actual_arg = perform_beta_substitution_helper(
                &*actual_arg,
                var_name,
                var_value,
                value_free_vars,
            );

            return Box::new(ExprNode::FnApp {
                fn_body: subbed_fn_body,
                actual_arg: subbed_actual_arg,
            });
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
                    let mut final_fn_body = Box::new((**fn_body).clone());

                    perform_alpha_conversion(
                        formal_param.as_str(),
                        &mut *final_fn_body,
                        value_free_vars,
                    );

                    return Box::new(ExprNode::FnDef {
                        formal_param: formal_param.clone(),
                        fn_body: perform_beta_substitution_helper(
                            &*final_fn_body,
                            var_name,
                            var_value,
                            value_free_vars,
                        ),
                    });
                }
                // Directly perform beta substitution if var_value does not
                // contain formal_param as a free variable.
                else {
                    // Perform the beta substitution into the function body.
                    return Box::new(ExprNode::FnDef {
                        formal_param: formal_param.clone(),
                        fn_body: perform_beta_substitution_helper(
                            &*fn_body,
                            var_name,
                            var_value,
                            value_free_vars,
                        ),
                    });
                }
            }

            // Return a copy of the pre-existing program if the formal_param
            // shadows the variable's name that we are substituting for.
            return Box::new(ExprNode::FnDef {
                formal_param: formal_param.clone(),
                fn_body: fn_body.clone(),
            });
        }
    };
}

fn perform_beta_substitution(
    expr_body: &ExprNode,
    var_name: &str,
    var_value: &ExprNode,
) -> Box<ExprNode> {
    let value_free_vars = get_all_free_variables(var_value);
    return perform_beta_substitution_helper(expr_body, var_name, var_value, &value_free_vars);
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
                // println!("In FnApp case.");

                match *fn_body {
                    // The function being applied is a function definition, so
                    // we are at a redex.
                    ExprNode::FnDef {
                        formal_param,
                        fn_body: defined_fn,
                    } => {
                        parsed_left = false;
                        // println!("In inner FnDef case.");

                        expr_body = perform_beta_substitution(
                            &*defined_fn,
                            formal_param.as_str(),
                            &*actual_arg,
                        );
                        continue;
                    }

                    // The function being applied is a variable name. First
                    // expand it if it is actually a def statement macro.
                    ExprNode::Var { var_name } => {
                        parsed_left = false;
                        // println!("In inner Var case.");

                        // println!(
                        //     "Var name is {var_name}. In dev map = {}",
                        //     def_statement_map.contains_key(var_name.as_str())
                        // );

                        // The variable is a def statement macro.
                        if def_statement_map.contains_key(var_name.as_str()) {
                            let new_fn_body = Box::new(
                                (*def_statement_map.get(var_name.as_str()).expect(
                                    "Unable to get expansion of def statement macro {var_name}.",
                                ))
                                .clone(),
                            );

                            expr_body = Box::new(ExprNode::FnApp {
                                fn_body: new_fn_body,
                                actual_arg: actual_arg,
                            });

                            continue;
                        }
                        // The variable is not a def statement macro.
                        else {
                            return Box::new(ExprNode::FnApp {
                                fn_body: Box::new(ExprNode::Var { var_name }),
                                actual_arg: actual_arg,
                            });

                            // return Box::new(ExprNode::Var { var_name });
                        }
                    }

                    // The inner function is a function application, so evaluate
                    // the inner function.
                    fn_body_val => {
                        // println!("In inner FnApp case, parsed_left = {parsed_left}.");

                        if !parsed_left {
                            if verbose {
                                println!("Recursing on {fn_body_val}.")
                            }

                            expr_body = Box::new(ExprNode::FnApp {
                                fn_body: eval_expr_lazy(
                                    Box::new(fn_body_val),
                                    def_statement_map,
                                    verbose,
                                ),
                                actual_arg: actual_arg,
                            });

                            if verbose {
                                println!("Recursion complete.")
                            }

                            parsed_left = true;
                            continue;
                        } else {
                            return Box::new(ExprNode::FnApp {
                                fn_body: Box::new(fn_body_val),
                                actual_arg: actual_arg,
                            });
                        }
                    }
                }
            }

            // The expr_body is not a function application, so it is not a
            // redex. Because of this, we can break.
            expr_body => {
                return Box::new(expr_body);
            }
        };
    }
}

/// Execute a lambda calculus program.
pub fn execute_program(program: &Vec<Statement>, verbose: bool) -> Vec<Box<ExprNode>> {
    // First build a map from def_name -> def_body.
    let def_map = make_def_map(&program);

    // For each statement, if it is an eval, perform the evaluation.
    let mut exec_result: Vec<Box<ExprNode>> = Vec::new();

    for statement in program {
        if let Statement::Eval { eval_body } = statement {
            exec_result.push(eval_expr_lazy(eval_body.clone(), &def_map, verbose));
        }
    }

    return exec_result;
}

#[cfg(test)]
mod tests {
    use std::iter::zip;

    use crate::{
        lexical_analysis::run_lexical_analysis, recursive_descent_parsing::parse_recursive_descent,
    };

    use super::*;

    fn run_execution_test(program_str: &str, expected_str_outputs: &Vec<&str>) {
        let program_tokens = run_lexical_analysis(program_str, true);
        let program =
            parse_recursive_descent(&program_tokens).expect("Unable to parse program string.");

        let exec_result = execute_program(&program, true);

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

    // Test eval_expr_lazy on summing up counting the length of a  linked list.
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
