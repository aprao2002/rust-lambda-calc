use std::collections::HashSet;

use crate::recursive_descent_parsing::{ExprNode, Statement};

fn compute_free_variables(expr_body: &ExprNode) -> HashSet<&str> {
    match expr_body {
        ExprNode::Var { var_name } => {
            return HashSet::from([var_name.as_ref()]);
        }
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            let fn_body_free_vars = compute_free_variables(&**fn_body);
            let actual_arg_free_vars = compute_free_variables(&**actual_arg);

            return fn_body_free_vars
                .union(&actual_arg_free_vars)
                .copied()
                .collect();
        }
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            let mut fn_body_free_vars = compute_free_variables(&*fn_body);
            fn_body_free_vars.remove(formal_param.as_str());
            return fn_body_free_vars;
        }
    };
}

fn find_all_variables(expr_body: &ExprNode) -> HashSet<&str> {
    match expr_body {
        ExprNode::Var { var_name } => {
            return HashSet::from([var_name.as_ref()]);
        }
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            let fn_body_free_vars = compute_free_variables(&**fn_body);
            let actual_arg_free_vars = compute_free_variables(&**actual_arg);

            return fn_body_free_vars
                .union(&actual_arg_free_vars)
                .copied()
                .collect();
        }
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            let mut fn_body_free_vars = compute_free_variables(&*fn_body);
            fn_body_free_vars.insert(formal_param.as_str());
            return fn_body_free_vars;
        }
    };
}

fn perform_alpha_conversion(
    formal_param: &str,
    fn_body: &ExprNode,
    value_free_vars: &HashSet<&str>,
) {
    // let all_fn_body_vars = find_all_variables(&*fn_body);
    // let vars_to_avoid: HashSet<&str> = all_fn_body_vars.union(value_free_vars).copied().collect();

    // let mut new_formal_parameter = String::from(formal_param);

    // while vars_to_avoid.contains(new_formal_parameter.as_str()) {
    //     new_formal_parameter = new_formal_parameter + "'";
    // }

    // rename_variable(formal_param, new_formal_parameter.as_str(), fn_body);
}

fn perform_beta_substitution_helper(
    expr_body: Box<ExprNode>,
    var_name: &str,
    var_value: &ExprNode,
    value_free_vars: &HashSet<&str>,
) -> Box<ExprNode> {
    match *expr_body {
        // Substitute into variable.
        ExprNode::Var {
            var_name: curr_var_name,
        } => {
            if curr_var_name == var_name {
                return Box::new(var_value.clone());
            }
            return Box::new(ExprNode::Var {
                var_name: curr_var_name,
            });
        }

        // Substitute onto function application.
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            let subbed_fn_body =
                perform_beta_substitution_helper(fn_body, var_name, var_value, value_free_vars);
            let subbed_actual_arg =
                perform_beta_substitution_helper(actual_arg, var_name, var_value, value_free_vars);

            return Box::new(ExprNode::FnApp {
                fn_body: subbed_fn_body,
                actual_arg: subbed_actual_arg,
            });
        }

        // Substitute onto function definition.
        ExprNode::FnDef {
            formal_param,
            mut fn_body,
        } => {
            // Only try to substitute if the formal param doesn't shadow
            // var_name.
            if formal_param != var_name {
                // To prevent variable capture, perform alpha conversion if
                // var_value contains formal_param as a free variable.
                if value_free_vars.contains(formal_param.as_str()) {
                    perform_alpha_conversion(formal_param.as_str(), &*fn_body, value_free_vars);
                }

                // Perform the beta substitution into the function body.
                fn_body =
                    perform_beta_substitution_helper(fn_body, var_name, var_value, value_free_vars);
            }

            return Box::new(ExprNode::FnDef {
                formal_param: formal_param,
                fn_body: fn_body,
            });
        }
    };
}

fn perform_beta_substitution(
    expr_body: Box<ExprNode>,
    var_name: &str,
    var_value: Box<ExprNode>,
) -> Box<ExprNode> {
    let value_free_vars = compute_free_variables(&*var_value);
    return perform_beta_substitution_helper(expr_body, var_name, &*var_value, &value_free_vars);
}

fn eval_expr_lazy(expr_body: Box<ExprNode>) -> Box<ExprNode> {
    loop {
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
                        fn_body: defined_fn,
                    } => {
                        return perform_beta_substitution(
                            defined_fn,
                            formal_param.as_str(),
                            actual_arg,
                        );
                    }

                    // The function being applied is not a function definition,
                    // so we are not at a redex.
                    fn_body => {
                        return Box::new(ExprNode::FnApp {
                            fn_body: Box::new(fn_body),
                            actual_arg: actual_arg,
                        });
                    }
                }
            }

            // The expr_body is not a function application, so it is not a
            // redex.
            expr_body => {
                return Box::new(expr_body);
            }
        };
    }
}

fn execute_program(statements: Vec<Statement>) {
    // First build a map from def_name -> def_body.

    // Validate that there are no recursive defs.

    // For each statement, if it is an eval, perform the evaluation.
}
