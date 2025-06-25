/// Data structures to represent lambda calculus expressions, and some utility
/// functions to display and manipulate them.
use std::collections::{HashMap, HashSet};

/// Represents a lambda-calculus expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprNode {
    FnDef {
        formal_param: String,
        fn_body_idx: usize,
    },
    FnApp {
        fn_body_idx: usize,
        actual_arg_idx: usize,
    },
    Var {
        var_name: String,
    },
}

/// Represents a 'def' or 'eval' statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Statement {
    Def {
        def_name: String,
        def_body_idx: usize,
    },
    Eval {
        eval_body_idx: usize,
    },
}

/// Represents a lambda calculus program.
pub struct Program {
    expr_nodes: Vec<ExprNode>,
    statements: Vec<Statement>,
}

// Helper function to produce a string representation of an ExprNode.
fn expr_node_to_string_helper(expr_node_idx: usize, program: &Program, string_so_far: &mut String) {
    let expr_node = &program.expr_nodes[expr_node_idx];

    match expr_node {
        ExprNode::Var { var_name } => {
            string_so_far.push_str(var_name.as_str());
        }
        ExprNode::FnApp {
            fn_body_idx,
            actual_arg_idx,
        } => {
            // Get references to the actual program nodes.
            let fn_body = &program.expr_nodes[*fn_body_idx];
            let actual_arg = &program.expr_nodes[*actual_arg_idx];

            // If fn_body is a function def, we will surround it with
            // parentheses for readability.
            let mut first_needs_parens = false;

            match fn_body {
                ExprNode::FnDef { .. } => {
                    first_needs_parens = true;
                }
                _ => {}
            }

            // If actual_arg is a function def or function app, we will surround
            // it with parentheses for readability.
            let mut second_needs_parens = false;

            match actual_arg {
                ExprNode::FnDef { .. } => {
                    second_needs_parens = true;
                }
                ExprNode::FnApp { .. } => {
                    second_needs_parens = true;
                }
                _ => {}
            }

            if first_needs_parens {
                string_so_far.push('(');
                expr_node_to_string_helper(*fn_body_idx, program, string_so_far);
                string_so_far.push(')');
            } else {
                expr_node_to_string_helper(*fn_body_idx, program, string_so_far);
            }

            string_so_far.push(' ');

            if second_needs_parens {
                string_so_far.push('(');
                expr_node_to_string_helper(*actual_arg_idx, program, string_so_far);
                string_so_far.push(')');
            } else {
                expr_node_to_string_helper(*actual_arg_idx, program, string_so_far);
            }
        }
        ExprNode::FnDef {
            formal_param,
            fn_body_idx,
        } => {
            string_so_far.push_str(format!("\\{}. ", formal_param.as_str()).as_str());
            expr_node_to_string_helper(*fn_body_idx, program, string_so_far);
        }
    };
}

// Converts an expr node to a string.
pub fn expr_node_to_string(expr_node_idx: usize, program: &Program) -> String {
    let mut out_string = String::new();
    expr_node_to_string_helper(expr_node_idx, program, &mut out_string);
    return out_string;
}

// Converts a statement to a string.
pub fn statement_to_string(statement: &Statement, program: &Program) -> String {
    match statement {
        Statement::Def {
            def_name,
            def_body_idx,
        } => {
            return format!(
                "def {} = {};",
                def_name,
                expr_node_to_string(*def_body_idx, program)
            );
        }

        Statement::Eval { eval_body_idx } => {
            return format!("eval {};", expr_node_to_string(*eval_body_idx, program));
        }
    }
}

/// Creates a map where keys are the names defined by 'def' statements and
/// values are the corresponding ExprNodes they expand to.
pub fn make_def_map(program: &Program) -> HashMap<&str, &ExprNode> {
    let mut out: HashMap<&str, &ExprNode> = HashMap::new();

    for statement in &program.statements {
        if let Statement::Def {
            def_name,
            def_body_idx,
        } = statement
        {
            out.insert(def_name.as_str(), &program.expr_nodes[*def_body_idx]);
        }
    }

    return out;
}

/// Gets the names of all macros defined in a lambda calculus program with def
/// statements.
pub fn get_all_def_names(program: &Program) -> HashSet<&str> {
    let mut all_def_names: HashSet<&str> = HashSet::new();

    for statement in &program.statements {
        if let Statement::Def { def_name, .. } = statement {
            all_def_names.insert(def_name.as_str());
        }
    }

    return all_def_names;
}

/// Computes the free variables in the given lambda calculus expression.
pub fn get_all_free_variables<'a>(expr_body_idx: usize, program: &'a Program) -> HashSet<&'a str> {
    let expr_body = &program.expr_nodes[expr_body_idx];

    match expr_body {
        ExprNode::Var { var_name } => {
            return HashSet::from([var_name.as_ref()]);
        }
        ExprNode::FnApp {
            fn_body_idx,
            actual_arg_idx,
        } => {
            let fn_body_free_vars = get_all_free_variables(*fn_body_idx, program);
            let actual_arg_free_vars = get_all_free_variables(*actual_arg_idx, program);

            return fn_body_free_vars
                .union(&actual_arg_free_vars)
                .copied()
                .collect();
        }
        ExprNode::FnDef {
            formal_param,
            fn_body_idx,
        } => {
            let mut fn_body_free_vars = get_all_free_variables(*fn_body_idx, program);
            fn_body_free_vars.remove(formal_param.as_str());
            return fn_body_free_vars;
        }
    };
}

/// Finds all variables used in the given lambda calculus expression.
pub fn get_all_variables<'a>(expr_body_idx: usize, program: &'a Program) -> HashSet<&'a str> {
    let expr_body = &program.expr_nodes[expr_body_idx];

    match expr_body {
        ExprNode::Var { var_name } => {
            return HashSet::from([var_name.as_ref()]);
        }
        ExprNode::FnApp {
            fn_body_idx,
            actual_arg_idx,
        } => {
            let fn_body_vars = get_all_variables(*fn_body_idx, program);
            let actual_arg_vars = get_all_variables(*actual_arg_idx, program);

            return fn_body_vars.union(&actual_arg_vars).copied().collect();
        }
        ExprNode::FnDef {
            formal_param,
            fn_body_idx,
        } => {
            let mut fn_body_free_vars = get_all_variables(*fn_body_idx, program);
            fn_body_free_vars.insert(formal_param.as_str());
            return fn_body_free_vars;
        }
    };
}

/// Renames a variable in the given lambda calculus expression
/// (used in program_exection.rs for alpha renaming).
pub fn rename_variable(
    old_var_name: &str,
    new_var_name: &str,
    expr_idx: usize,
    program: &mut Program,
) {
    // We don't recurse directly in the match statement because we can't
    let mut idxs_to_recurse = vec![];

    match &mut program.expr_nodes[expr_idx] {
        ExprNode::Var { var_name } => {
            if var_name.as_str() == old_var_name {
                *var_name = String::from(new_var_name);
            }
        }
        ExprNode::FnApp {
            fn_body_idx,
            actual_arg_idx,
        } => {
            idxs_to_recurse.push(*fn_body_idx);
            idxs_to_recurse.push(*actual_arg_idx);
        }
        ExprNode::FnDef {
            formal_param,
            fn_body_idx,
        } => {
            if formal_param.as_str() != old_var_name {
                idxs_to_recurse.push(*fn_body_idx);
            }
        }
    }

    idxs_to_recurse
        .iter()
        .for_each(|idx| rename_variable(old_var_name, new_var_name, *idx, program));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_node_to_string_1() {
        let expected_output = r"\n. \f. \x. f (n f x)";

        let test_expr_nodes = vec![
            // 0: \n. ..
            ExprNode::FnDef {
                formal_param: String::from("n"),
                fn_body_idx: 1,
            },
            // 1: \f. ..
            ExprNode::FnDef {
                formal_param: String::from("f"),
                fn_body_idx: 2,
            },
            // 2: \x. ..
            ExprNode::FnDef {
                formal_param: String::from("x"),
                fn_body_idx: 3,
            },
            // 3: f (n f x)
            ExprNode::FnApp {
                fn_body_idx: 4,
                actual_arg_idx: 5,
            },
            // 4: f
            ExprNode::Var {
                var_name: String::from("f"),
            },
            // 5: (n f) x
            ExprNode::FnApp {
                fn_body_idx: 6,
                actual_arg_idx: 9,
            },
            // 6: n f
            ExprNode::FnApp {
                fn_body_idx: 7,
                actual_arg_idx: 8,
            },
            // 7: n
            ExprNode::Var {
                var_name: String::from("n"),
            },
            // 8: f
            ExprNode::Var {
                var_name: String::from("f"),
            },
            // 9: x
            ExprNode::Var {
                var_name: String::from("x"),
            },
        ];

        let test_program = Program {
            expr_nodes: test_expr_nodes,
            statements: vec![],
        };

        assert_eq!(
            expected_output,
            format!("{}", expr_node_to_string(0, &test_program)).as_str()
        );
    }
}
