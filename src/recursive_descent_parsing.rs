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

enum Statement {
    Def {
        def_name: String,
        def_body: Box<ExprNode>,
    },
    Eval {
        eval_body: Box<ExprNode>,
    },
}

fn try_token_class(
    tokens: &Vec<Token>,
    start_idx: usize,
    token_class: TokenClass,
) -> Option<(&Token, usize)> {
    assert!(start_idx < tokens.len());

    match tokens[start_idx].token_class == token_class {
        true => return Some((&tokens[start_idx], start_idx + 1)),
        false => return None,
    };
}

fn try_expr_rule(tokens: &Vec<Token>, start_idx: usize) -> Option<(Box<ExprNode>, usize)> {
    return None;
}

fn try_def_statement_rule(tokens: &Vec<Token>, start_idx: usize) -> Option<(Statement, usize)> {
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Def)?;
    let (def_name_token, start_idx) = try_token_class(tokens, start_idx, TokenClass::Identifier)?;
    let (_, start_idx) = try_token_class(tokens, start_idx, TokenClass::Equals)?;
    let (def_body_box, start_idx) = try_expr_rule(tokens, start_idx)?;

    return Some((
        Statement::Def {
            def_name: def_name_token.token_text.clone(),
            def_body: def_body_box,
        },
        start_idx,
    ));
}

pub fn parse_recursive_descent(tokens: Vec<Token>) {}
