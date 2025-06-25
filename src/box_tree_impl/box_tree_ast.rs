/// Data structures to represent lambda calculus expressions, and some utility
/// functions to display and manipulate them.
use std::collections::{HashMap, HashSet};

/// Represents a 'def' or 'eval' statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Statement {
    Def {
        def_name: String,
        def_body: Box<ExprNode>,
    },
    Eval {
        eval_body: Box<ExprNode>,
    },
}

/// Represents a lambda-calculus expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprNode {
    FnDef {
        formal_param: String,
        fn_body: Box<ExprNode>,
    },
    FnApp {
        fn_body: Box<ExprNode>,
        actual_arg: Box<ExprNode>,
    },
    Var {
        var_name: String,
    },
}

// Helper function to produce a string representation of an ExprNode.
fn expr_node_to_string_helper(expr_node: &ExprNode, string_so_far: &mut String) {
    match expr_node {
        ExprNode::Var { var_name } => {
            string_so_far.push_str(var_name.as_str());
        }
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            // If fn_body is a function def, we will surround it with
            // parentheses for readability.
            let mut first_needs_parens = false;

            match &**fn_body {
                ExprNode::FnDef { .. } => {
                    first_needs_parens = true;
                }
                _ => {}
            }

            // If actual_arg is a function def or function app, we will surround
            // it with parentheses for readability.
            let mut second_needs_parens = false;

            match &**actual_arg {
                ExprNode::FnDef { .. } => {
                    second_needs_parens = true;
                }
                ExprNode::FnApp { .. } => {
                    second_needs_parens = true;
                }
                _ => {}
            }

            // string_so_far.push('(');

            if first_needs_parens {
                string_so_far.push('(');
                expr_node_to_string_helper(fn_body, string_so_far);
                string_so_far.push(')');
            } else {
                expr_node_to_string_helper(fn_body, string_so_far);
            }

            string_so_far.push(' ');

            if second_needs_parens {
                string_so_far.push('(');
                expr_node_to_string_helper(actual_arg, string_so_far);
                string_so_far.push(')');
            } else {
                expr_node_to_string_helper(actual_arg, string_so_far);
            }

            // string_so_far.push(')');
        }
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            string_so_far.push_str(format!("\\{}. ", formal_param.as_str()).as_str());
            expr_node_to_string_helper(fn_body, string_so_far);
        }
    };
}

// Converts an expr node to a string.
pub fn expr_node_to_string(expr_node: &ExprNode) -> String {
    let mut out_string = String::new();
    expr_node_to_string_helper(expr_node, &mut out_string);
    return out_string;
}

// Display trait implementation for ExprNode using expr_node_to_string function.
impl std::fmt::Display for ExprNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(f, "{}", expr_node_to_string(self).as_str());
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Def { def_name, def_body } => {
                return write!(f, "def {} = {};", def_name, def_body);
            }
            Statement::Eval { eval_body } => {
                return write!(f, "eval {};", eval_body);
            }
        }
    }
}

/// Creates a map where keys are the names defined by 'def' statements and
/// values are the corresponding ExprNodes they expand to.
pub fn make_def_map(program: &Vec<Statement>) -> HashMap<&str, &ExprNode> {
    let mut out: HashMap<&str, &ExprNode> = HashMap::new();

    for statement in program {
        if let Statement::Def { def_name, def_body } = statement {
            out.insert(def_name.as_str(), &**def_body);
        }
    }

    return out;
}

/// Gets the names of all macros defined in a lambda calculus program with def
/// statements.
pub fn get_all_def_names(program: &Vec<Statement>) -> HashSet<&str> {
    let mut all_def_names: HashSet<&str> = HashSet::new();

    for statement in program {
        if let Statement::Def { def_name, .. } = statement {
            all_def_names.insert(def_name.as_str());
        }
    }

    return all_def_names;
}

/// Computes the free variables in the given lambda calculus expression.
pub fn get_all_free_variables(expr_body: &ExprNode) -> HashSet<&str> {
    match expr_body {
        ExprNode::Var { var_name } => {
            return HashSet::from([var_name.as_ref()]);
        }
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            let fn_body_free_vars = get_all_free_variables(&**fn_body);
            let actual_arg_free_vars = get_all_free_variables(&**actual_arg);

            return fn_body_free_vars
                .union(&actual_arg_free_vars)
                .copied()
                .collect();
        }
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            let mut fn_body_free_vars = get_all_free_variables(&*fn_body);
            fn_body_free_vars.remove(formal_param.as_str());
            return fn_body_free_vars;
        }
    };
}

/// Finds all variables used in the given lambda calculus expression.
pub fn get_all_variables(expr_body: &ExprNode) -> HashSet<&str> {
    match expr_body {
        ExprNode::Var { var_name } => {
            return HashSet::from([var_name.as_ref()]);
        }
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            let fn_body_vars = get_all_variables(&**fn_body);
            let actual_arg_vars = get_all_variables(&**actual_arg);

            return fn_body_vars.union(&actual_arg_vars).copied().collect();
        }
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            let mut fn_body_vars = get_all_variables(&*fn_body);
            fn_body_vars.insert(formal_param.as_str());
            return fn_body_vars;
        }
    };
}

/// Renames a variable in the given lambda calculus expression
/// (used in program_exection.rs for alpha renaming).
pub fn rename_variable(old_var_name: &str, new_var_name: &str, expr_to_rename: &mut ExprNode) {
    match expr_to_rename {
        ExprNode::Var { var_name } => {
            if var_name.as_str() == old_var_name {
                *var_name = String::from(new_var_name);
            }
        }
        ExprNode::FnApp {
            fn_body,
            actual_arg,
        } => {
            rename_variable(old_var_name, new_var_name, fn_body);
            rename_variable(old_var_name, new_var_name, actual_arg);
        }
        ExprNode::FnDef {
            formal_param,
            fn_body,
        } => {
            if formal_param.as_str() != old_var_name {
                rename_variable(old_var_name, new_var_name, fn_body);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_node_to_string_1() {
        let expected_output = r"\n. \f. \x. f (n f x)";

        let test_input = ExprNode::FnDef {
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
        };

        assert_eq!(expected_output, format!("{}", test_input).as_str());
    }
}
