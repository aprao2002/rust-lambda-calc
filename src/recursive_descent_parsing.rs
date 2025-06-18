use crate::lexical_analysis::{Token, TokenClass};

enum ExprNode {
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

pub enum Statement {
    Def {
        def_name: String,
        def_body: Box<ExprNode>,
    },
    Eval {
        eval_body: Box<ExprNode>,
    },
}

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

fn try_parenthesis_expr_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    let (_, start_idx) = try_token_text(tokens, start_idx, "(")?;
    let (expr_node, start_idx) = try_expr_rule(tokens, start_idx)?;
    let (_, start_idx) = try_token_text(tokens, start_idx, ")")?;

    return Ok((expr_node, start_idx));
}

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

fn try_atom_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    return try_parenthesis_expr_rule(tokens, start_idx)
        .or_else(|_| try_var_expr_rule(tokens, start_idx));
}

fn try_non_app_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    return try_lambda_rule(tokens, start_idx).or_else(|_| try_atom_rule(tokens, start_idx));
}

fn try_apply_atom_to_non_app_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    let (atom_expr_node, start_idx) = try_atom_rule(tokens, start_idx)?;
    let (non_app_expr_node, start_idx) = try_non_app_rule(tokens, start_idx)?;

    return Ok((
        Box::new(ExprNode::FnApp {
            fn_body: atom_expr_node,
            actual_arg: non_app_expr_node,
        }),
        start_idx,
    ));
}

fn try_non_lambda_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    return try_apply_atom_to_non_app_rule(tokens, start_idx)
        .or_else(|_| try_atom_rule(tokens, start_idx));
}

fn try_expr_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Box<ExprNode>, usize), ParseError> {
    return try_lambda_rule(tokens, start_idx).or_else(|_| try_non_lambda_rule(tokens, start_idx));
}

fn try_def_statement_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Statement, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Def)?;
    let (def_name_token, start_idx) = try_token_class(tokens, start_idx, TokenClass::Identifier)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Equals)?;
    let (def_body, start_idx) = try_expr_rule(tokens, start_idx)?;

    return Ok((
        Statement::Def {
            def_name: def_name_token.token_text.clone(),
            def_body: def_body,
        },
        start_idx,
    ));
}

fn try_eval_statement_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Statement, usize), ParseError> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Eval)?;
    let (eval_body_box, start_idx) = try_expr_rule(tokens, start_idx)?;

    return Ok((
        Statement::Eval {
            eval_body: eval_body_box,
        },
        start_idx,
    ));
}

fn try_statement_rule(
    tokens: &Vec<Token>,
    start_idx: usize,
) -> Result<(Statement, usize), ParseError> {
    return try_def_statement_rule(tokens, start_idx)
        .or_else(|_| try_eval_statement_rule(tokens, start_idx));
}

pub fn parse_recursive_descent(tokens: &Vec<Token>) -> Result<Vec<Statement>, ParseError> {
    let mut statements = Vec::new();
    let mut start_idx = 0;

    while start_idx < tokens.len() {
        let (statement, new_idx) = try_statement_rule(tokens, start_idx)?;
        statements.push(statement);
        start_idx = new_idx;
    }

    return Ok(statements);
}
