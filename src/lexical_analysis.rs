use lazy_static::lazy_static;
use regex::Regex;

// The different classes of tokens that compose the language.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum TokenClass {
    Def,
    Eval,
    Identifier,
    Equals,
    Semicolon,
    Lambda,
    Dot,
    Parentheses,
    Comment,
    Whitespace,
    Error,
}

// Represents a single token of the language.
#[derive(PartialEq, Eq, Debug)]
struct Token {
    token_class: TokenClass,
    token_text: String,
    // line_num: u32,
}

// Represents how to recognize a token class.
#[derive(Debug)]
struct TokenRule {
    token_class: TokenClass,
    regex: Regex,
}

// Vector of regex patterns that correspond to each token class.
lazy_static! {
    static ref token_rules: Vec<TokenRule> = vec![
        TokenRule {
            token_class: TokenClass::Def,
            regex: Regex::new(r"(?m)^def($|\s)").expect("Unable to compile Def rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Eval,
            regex: Regex::new(r"(?m)^eval($|\s)").expect("Unable to compile Eval rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Identifier,
            regex: Regex::new(r"(?m)^([a-zA-Z]+[a-zA-Z0-9_]*)($|\s)")
                .expect("Unable to compile Identifier rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Semicolon,
            regex: Regex::new(r"(?m);$").expect("Unable to compile Semicolon rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Lambda,
            regex: Regex::new(r"(?m)\\").expect("Unable to compile Lambda rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Dot,
            regex: Regex::new(r"(?m).").expect("Unable to compile Dot rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Parentheses,
            regex: Regex::new(r"(?m)\(|\)").expect("Unable to compile Parentheses rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Comment,
            regex: Regex::new(r"(?m)//.*$").expect("Unable to compile Comment rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Whitespace,
            regex: Regex::new(r"(?m)\s+").expect("Unable to compile Whitespace rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Error,
            regex: Regex::new(r"(?m).+?").expect("Unable to compile Error rule regex."),
        },
    ];
}

// Gets the rule for a specific token class.
fn get_rule_for_token_class(token_class: TokenClass) -> Option<&'static TokenRule> {
    token_rules
        .iter()
        .find(|token_rule| token_rule.token_class == token_class)
}

// Finds the rule that matches the most characters from the start of the input
// string.
fn get_longest_matching_rule(input_str: &str) -> (&'static TokenRule, usize) {
    let mut longest_match_len: usize = 0;
    let mut longest_token_rule = get_rule_for_token_class(TokenClass::Error)
        .expect("Unable to find token rule for Error token class.");

    for token_rule in token_rules.iter() {
        match token_rule
            .regex
            .find(input_str)
            .take_if(|match_obj| match_obj.start() == 0)
        {
            None => continue,
            Some(match_obj) => {
                if match_obj.len() > longest_match_len {
                    longest_match_len = match_obj.len();
                    longest_token_rule = token_rule;
                }
            }
        };
    }

    (longest_token_rule, longest_match_len)
}

// Given a string, returns a vector of tokens that comprise that string. 
// Discards 'uninteresting' tokens like comments and whitespace.
fn make_token_stream(program_str: &str) -> Vec<Token> {
    let mut curr_idx: usize = 0;
    let mut out = Vec::new();

    while curr_idx < program_str.len() {
        let (token_rule, match_len) = get_longest_matching_rule(&program_str[curr_idx..]);

        out.push(Token {
            token_class: token_rule.token_class,
            token_text: String::from(&program_str[curr_idx..curr_idx + match_len]),
            // line_num: ,
        });
        curr_idx += match_len;
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test if get_rule_for_token_class returns the right rule.
    #[test]
    fn test_get_rule_for_token_class() {
        token_rules.iter().for_each(|token_rule| {
            println!("Testing token_class: {:?}", token_rule.token_class);

            let retrieved_rule = get_rule_for_token_class(token_rule.token_class)
                .expect("Unable to get rule for token class {token_rule.token_class}");

            assert!(std::ptr::eq(retrieved_rule, token_rule));
        });
    }

    // Test if find_longest_matching_rule returns the right rules.
    #[test]
    fn test_longest_matching_rule() {
        // Test cases formatted as (input_str, expected_token_rule, expected_match_len).
        let string_and_rule_vec = vec![
            (
                r"// This is a comment.",
                get_rule_for_token_class(TokenClass::Comment)
                    .expect("Unable to get rule for token class {TokenClass::Comment}"),
                r"// This is a comment.".len(),
            ),
            (
                r"eval \v. v;",
                get_rule_for_token_class(TokenClass::Eval)
                    .expect("Unable to get rule for token class {TokenClass::Eval}"),
                r"eval ".len(),
            ),
        ];

        string_and_rule_vec
            .iter()
            .for_each(|&(input_str, expected_rule, expected_len)| {
                let (retrieved_rule, match_len) = get_longest_matching_rule(input_str);
                assert!(std::ptr::eq(retrieved_rule, expected_rule));
                assert_eq!(match_len, expected_len);
            });
    }

    // Test if make_token_stream returns the desired token stream.
    #[test]
    fn test_make_token_stream_simple() {
        let program_str = r"// This is a comment.
def identity_fn = (\x. x);";

        let expected_token_stream_prefix = vec![
            Token {
                token_class: TokenClass::Comment,
                token_text: String::from(r"// This is a comment."),
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from("\n"),
            },
            Token {
                token_class: TokenClass::Def,
                token_text: String::from(r"def "),
            },
        ];

        let produced_token_stream = make_token_stream(program_str);

        assert!(expected_token_stream_prefix.len() <= produced_token_stream.len());

        expected_token_stream_prefix
            .iter()
            .enumerate()
            .for_each(|(idx, token)| assert_eq!(token, &produced_token_stream[idx]));
    }
}
