//! A simple lexer that converts a program given as a string into a vector of
//! tokens.

use std::usize;

use lazy_static::lazy_static;
use regex::Regex;

/// The different classes of tokens that compose the language.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum TokenClass {
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

/// Represents a single token of the language.
#[derive(PartialEq, Eq, Debug)]
pub struct Token {
    pub token_class: TokenClass,
    pub token_text: String,
    pub line_num: usize,
}

/// Represents how to recognize a token class.
#[derive(Debug)]
struct TokenRule {
    token_class: TokenClass,
    regex: Regex,
}

lazy_static! {
    /// Vector of regex patterns that correspond to each token class. The 'token_text'
    /// capture group in each regex will be used to populate the token_text field of
    /// Token objects.
    static ref token_rules: Vec<TokenRule> = vec![
        TokenRule {
            token_class: TokenClass::Def,
            regex: Regex::new(r"\A(def)\b").expect("Unable to compile Def rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Eval,
            regex: Regex::new(r"\A(eval)\b").expect("Unable to compile Eval rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Identifier,
            regex: Regex::new(r"\A([a-zA-Z_]+[a-zA-Z0-9_]*)")
                .expect("Unable to compile Identifier rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Equals,
            regex: Regex::new(r"\A(=)").expect("Unable to compile Identifier rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Semicolon,
            regex: Regex::new(r"\A(;)").expect("Unable to compile Semicolon rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Lambda,
            regex: Regex::new(r"\A(\\)").expect("Unable to compile Lambda rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Dot,
            regex: Regex::new(r"\A(\.)").expect("Unable to compile Dot rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Parentheses,
            regex: Regex::new(r"\A(\(|\))").expect("Unable to compile Parentheses rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Comment,
            regex: Regex::new(r"\A(//[^\n]*)").expect("Unable to compile Comment rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Whitespace,
            regex: Regex::new(r"\A(\s+)").expect("Unable to compile Whitespace rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Error,
            regex: Regex::new(r"\A(.)").expect("Unable to compile Error rule regex."),
        },
    ];
}

/// Gets the rule for a specific token class.
fn get_rule_for_token_class(token_class: TokenClass) -> Option<&'static TokenRule> {
    token_rules
        .iter()
        .find(|token_rule| token_rule.token_class == token_class)
}

/// Finds the rule that matches the most characters from the start of the input
/// string.
#[derive(Debug)]
struct RuleApplicationResult<'a> {
    token_rule: &'static TokenRule,
    token_text: &'a str,
}

/// Allows equality comparisons between RuleApplicationResult objects. Compares
/// the objects by (1) making sure they point to the same token_rule, and (2)
/// contain the same token_text.
impl<'a> PartialEq for RuleApplicationResult<'a> {
    fn eq(&self, other: &Self) -> bool {
        return std::ptr::eq(self.token_rule, other.token_rule)
            && self.token_text == other.token_text;
    }
}

/// Counts the number of occurrences of target_char in in_str.
fn count_occurrences(in_str: &str, target_char: char) -> usize {
    return in_str
        .chars()
        .filter(|&curr_char| curr_char == target_char)
        .count();
}

/// Finds the lexer rule that matches the longest substring starting from the
/// start of input_str, and returns a RuleApplicationResult object describing the
/// match.
fn apply_longest_matching_rule<'a>(input_str: &'a str) -> RuleApplicationResult<'a> {
    let mut out_token_rule = get_rule_for_token_class(TokenClass::Error)
        .expect("Unable to find token rule for Error token class.");
    let mut out_token_text = "";

    for token_rule in token_rules.iter() {
        match token_rule.regex.find(input_str) {
            None => continue,
            Some(match_obj) => {
                if match_obj.len() > out_token_text.len() {
                    out_token_rule = token_rule;
                    out_token_text = &input_str[match_obj.range()];
                }
            }
        }
    }
    return RuleApplicationResult {
        token_rule: out_token_rule,
        token_text: out_token_text,
    };
}

/// Merges a sequence of error tokens into a single error token. Assumes that the
/// input vector contains at least one error token.
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

/// Given a string, returns a vector of tokens that comprise that string.
/// Discards comments and whitespace if discard_uninteresting is true.
pub fn run_lexical_analysis(program_str: &str, discard_uninteresting: bool) -> Vec<Token> {
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

        // Skip uninteresting tokens if requested to do so.
        if discard_uninteresting
            && (rule_application_result.token_rule.token_class == TokenClass::Comment
                || rule_application_result.token_rule.token_class == TokenClass::Whitespace)
        {
            curr_idx += rule_application_result.token_text.len();
            curr_line_num += count_occurrences(rule_application_result.token_text, '\n');
            continue;
        }

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
            if !trailing_error_tokens.is_empty() {
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
    if !trailing_error_tokens.is_empty() {
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
                },
            ),
            (
                r"eval \v. v;",
                RuleApplicationResult {
                    token_rule: get_rule_for_token_class(TokenClass::Eval)
                        .expect("Unable to get rule for token class {TokenClass::Eval}"),
                    token_text: r"eval",
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

    // Test if run_lexical_analysis returns the desired token stream for a
    // well-formed program when discard_uninteresting is false.
    #[test]
    fn test_lexical_analysis_no_discarding() {
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

        let produced_token_stream = run_lexical_analysis(program_str, false);

        assert_token_stream_has_prefix(&produced_token_stream, &expected_token_stream_prefix);
    }

    // Test if run_lexical_analysis returns the desired token stream for a
    // well-formed program when discard_uninteresting is true.
    #[test]
    fn test_lexical_analysis_with_discarding() {
        let program_str = r"// This is a comment.
def identity_fn = (\x.x);";

        let expected_token_stream_prefix = vec![
            Token {
                token_class: TokenClass::Def,
                token_text: String::from(r"def"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Identifier,
                token_text: String::from(r"identity_fn"),
                line_num: 1,
            },
            Token {
                token_class: TokenClass::Equals,
                token_text: String::from(r"="),
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

        let produced_token_stream = run_lexical_analysis(program_str, true);

        assert_token_stream_has_prefix(&produced_token_stream, &expected_token_stream_prefix);
    }

    // Test if run_lexical_analysis returns the desired token stream for a
    // program with errors.
    #[test]
    fn test_lexical_analysis_error() {
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

        let produced_token_stream = run_lexical_analysis(program_str, false);

        assert_token_stream_has_prefix(&produced_token_stream, &expected_token_stream_prefix);
    }
}
