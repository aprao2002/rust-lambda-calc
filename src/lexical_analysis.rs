use core::error;
use std::{cmp::min, usize};

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
    line_num: usize,
}

// Represents how to recognize a token class.
#[derive(Debug)]
struct TokenRule {
    token_class: TokenClass,
    regex: Regex,
}

// Vector of regex patterns that correspond to each token class. The 'token_text'
// capture group in each regex will be used to populate the token_text field of
// Token objects.
lazy_static! {
    static ref token_rules: Vec<TokenRule> = vec![
        TokenRule {
            token_class: TokenClass::Def,
            regex: Regex::new(r"\A(?<token_text>def)($|\s)")
                .expect("Unable to compile Def rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Eval,
            regex: Regex::new(r"\A(?<token_text>eval)($|\s)")
                .expect("Unable to compile Eval rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Identifier,
            regex: Regex::new(r"\A(?<token_text>([a-zA-Z]+[a-zA-Z0-9_]*))")
                .expect("Unable to compile Identifier rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Equals,
            regex: Regex::new(r"\A(?<token_text>=)($|\s)")
                .expect("Unable to compile Identifier rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Semicolon,
            regex: Regex::new(r"\A(?<token_text>;)")
                .expect("Unable to compile Semicolon rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Lambda,
            regex: Regex::new(r"\A(?<token_text>\\)")
                .expect("Unable to compile Lambda rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Dot,
            regex: Regex::new(r"\A(?<token_text>\.)").expect("Unable to compile Dot rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Parentheses,
            regex: Regex::new(r"\A(?<token_text>\(|\))")
                .expect("Unable to compile Parentheses rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Comment,
            regex: Regex::new(r"\A(?<token_text>//[^\n]*)($|\s)")
                .expect("Unable to compile Comment rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Whitespace,
            regex: Regex::new(r"\A(?<token_text>\s+)")
                .expect("Unable to compile Whitespace rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Error,
            regex: Regex::new(r"(?m)\A(?<token_text>.+?)")
                .expect("Unable to compile Error rule regex."),
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
#[derive(Debug)]
struct RuleApplicationResult<'a> {
    token_rule: &'static TokenRule,
    token_text: &'a str,
    full_match_len: usize,
}

impl<'a> PartialEq for RuleApplicationResult<'a> {
    fn eq(&self, other: &Self) -> bool {
        return std::ptr::eq(self.token_rule, other.token_rule)
            && self.token_text == other.token_text
            && self.full_match_len == other.full_match_len;
    }
}

fn count_occurrences(in_str: &str, target_char: char) -> usize {
    return in_str.chars().fold(0, |accum, curr_char| {
        accum + ((curr_char == target_char) as usize)
    });
}

fn apply_longest_matching_rule<'a>(input_str: &'a str) -> RuleApplicationResult<'a> {
    let mut out_token_rule = get_rule_for_token_class(TokenClass::Error)
        .expect("Unable to find token rule for Error token class.");
    let mut out_token_text = "";
    let mut out_match_len: usize = 0;

    for token_rule in token_rules.iter() {
        match token_rule.regex.captures(input_str) {
            None => continue,
            Some(captures_obj) => {
                let full_match = captures_obj.get(0).expect("captures_obj.get(0) was None.");
                let token_text_match = captures_obj
                    .name("token_text")
                    .expect("captures_obj did not have a token_text capture group.");

                if full_match.len() > out_match_len {
                    out_token_rule = token_rule;
                    out_token_text = &input_str[token_text_match.range()];
                    out_match_len = full_match.len();
                }
            }
        };
    }
    return RuleApplicationResult {
        token_rule: out_token_rule,
        token_text: out_token_text,
        full_match_len: out_match_len,
    };
}

// Merges a sequence of error tokens into a single error token. Assumes that the
// input vector contains at least one error token.
fn merge_error_tokens(error_tokens: &Vec<Token>) -> Token {
    assert!(
        error_tokens.len() > 0,
        "merge_error_tokens received 0 error tokens to merge."
    );

    let (all_token_texts, all_line_nums): (Vec<&str>, Vec<usize>) = error_tokens
        .iter()
        .map(|token| (token.token_text.as_str(), token.line_num))
        .unzip();

    return Token {
        token_class: TokenClass::Error,
        token_text: all_token_texts.join(""),
        line_num: *all_line_nums
            .iter()
            .min()
            .expect("Unable to compute line number in merge_error_tokens."),
    };
}

// Given a string, returns a vector of tokens that comprise that string.
// Discards 'uninteresting' tokens like comments and whitespace.
fn make_token_stream(program_str: &str) -> Vec<Token> {
    // Track the current index into program_str we are inspecting, the current
    // line number, and the current vector of output tokens we will return.
    let mut curr_idx: usize = 0;
    let mut curr_line_num: usize = 0;
    let mut out_tokens = Vec::new();

    // Used to merge consecutive error tokens into a single error token.
    let mut trailing_error_tokens = Vec::new();

    // Loop until we consume the entire input program string.
    while curr_idx < program_str.len() {
        // Apply the longest matching rule.
        let rule_application_result = apply_longest_matching_rule(&program_str[curr_idx..]);

        // Construct the new token to add.
        let new_token = Token {
            token_class: rule_application_result.token_rule.token_class,
            token_text: String::from(rule_application_result.token_text),
            line_num: curr_line_num,
        };

        // Defer the addition of error tokens so that we can merge consecutive 
        // ones into a single big error token.
        if new_token.token_class == TokenClass::Error {
            trailing_error_tokens.push(new_token);
        
        // We did not just find an error token, so add any deferred error tokens
        // and the new (non-error) token.
        } else {
            if trailing_error_tokens.len() > 0 {
                out_tokens.push(merge_error_tokens(&trailing_error_tokens));
                trailing_error_tokens.clear();
            }

            out_tokens.push(new_token);
        }

        // Update scanning state.
        curr_idx += rule_application_result.token_text.len();
        curr_line_num += count_occurrences(rule_application_result.token_text, '\n');
    }

    // Handle edge case of trailing error tokens.
    if trailing_error_tokens.len() > 0 {
        out_tokens.push(merge_error_tokens(&trailing_error_tokens));
    }

    return out_tokens;
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
    fn test_apply_longest_matching_rule() {
        // Test cases formatted as (input_str, expected_token_rule, expected_match_len).
        let string_and_rule_vec = vec![
            (
                r"// This is a comment.",
                RuleApplicationResult {
                    token_rule: get_rule_for_token_class(TokenClass::Comment)
                        .expect("Unable to get rule for token class {TokenClass::Comment}"),
                    token_text: r"// This is a comment.",
                    full_match_len: r"// This is a comment.".len(),
                },
            ),
            (
                r"eval \v. v;",
                RuleApplicationResult {
                    token_rule: get_rule_for_token_class(TokenClass::Eval)
                        .expect("Unable to get rule for token class {TokenClass::Eval}"),
                    token_text: r"eval",
                    full_match_len: r"eval ".len(),
                },
            ),
        ];

        string_and_rule_vec
            .iter()
            .for_each(|(input_str, expected_result)| {
                let rule_application_result = apply_longest_matching_rule(*input_str);
                assert_eq!(&rule_application_result, expected_result);
            });
    }

    fn assert_token_stream_has_prefix(tokens_vec: &Vec<Token>, tokens_prefix: &Vec<Token>) {
        assert!(tokens_prefix.len() <= tokens_vec.len());

        tokens_prefix
            .iter()
            .enumerate()
            .for_each(|(idx, token)| assert_eq!(token, &tokens_vec[idx]));
    }

    // Test if make_token_stream returns the desired token stream for a
    // well-formed program.
    #[test]
    fn test_make_token_stream_simple() {
        let program_str = r"// This is a comment.
def identity_fn = (\x.x);";

        let expected_token_stream_prefix = vec![
            Token {
                token_class: TokenClass::Comment,
                token_text: String::from(r"// This is a comment."),
                line_num: 0,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from("\n"),
                line_num: 0,
            },
            Token {
                token_class: TokenClass::Def,
                token_text: String::from(r"def"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from(r" "),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Identifier,
                token_text: String::from(r"identity_fn"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from(r" "),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Equals,
                token_text: String::from(r"="),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from(r" "),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Parentheses,
                token_text: String::from(r"("),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Lambda,
                token_text: String::from(r"\"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Identifier,
                token_text: String::from(r"x"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Dot,
                token_text: String::from(r"."),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Identifier,
                token_text: String::from(r"x"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Parentheses,
                token_text: String::from(r")"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Semicolon,
                token_text: String::from(r";"),
                line_num: 1,
            },
        ];

        let produced_token_stream = make_token_stream(program_str);

        assert_token_stream_has_prefix(&produced_token_stream, &expected_token_stream_prefix);
    }

    // Test if make_token_stream returns the desired token stream for a
    // program with errors.
    #[test]
    fn test_make_token_stream_error() {
        let program_str = r"// This is a comment.
!!!
def identity_fn = (\x.x);";

        let expected_token_stream_prefix = vec![
            Token {
                token_class: TokenClass::Comment,
                token_text: String::from(r"// This is a comment."),
                line_num: 0,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from("\n"),
                line_num: 0,
            },
            Token {
                token_class: TokenClass::Error,
                token_text: String::from(r"!!!"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from("\n"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Def,
                token_text: String::from(r"def"),
                line_num: 2,
            },
        ];

        let produced_token_stream = make_token_stream(program_str);

        assert_token_stream_has_prefix(&produced_token_stream, &expected_token_stream_prefix);
    }
}
