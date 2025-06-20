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

fn expr_node_to_string(expr_node: &ExprNode) -> String {
    let mut out_string = String::new();
    expr_node_to_string_helper(expr_node, &mut out_string);
    return out_string;
}

impl std::fmt::Display for ExprNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(f, "{}", expr_node_to_string(self).as_str());
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
