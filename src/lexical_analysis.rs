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
            regex: Regex::new(r"(?m)\A(?<token_text>def)($|\s)")
                .expect("Unable to compile Def rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Eval,
            regex: Regex::new(r"(?m)\A(?<token_text>eval)($|\s)")
                .expect("Unable to compile Eval rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Identifier,
            regex: Regex::new(r"(?m)\A(?<token_text>([a-zA-Z]+[a-zA-Z0-9_]*))($|\s)")
                .expect("Unable to compile Identifier rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Semicolon,
            regex: Regex::new(r"(?m)\A(?<token_text>;)$")
                .expect("Unable to compile Semicolon rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Lambda,
            regex: Regex::new(r"(?m)\A(?<token_text>\\)")
                .expect("Unable to compile Lambda rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Dot,
            regex: Regex::new(r"(?m)\A(?<token_text>\.)")
                .expect("Unable to compile Dot rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Parentheses,
            regex: Regex::new(r"(?m)\A(?<token_text>\(|\))")
                .expect("Unable to compile Parentheses rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Comment,
            regex: Regex::new(r"(?m)\A(?<token_text>//.*)$")
                .expect("Unable to compile Comment rule regex."),
        },
        TokenRule {
            token_class: TokenClass::Whitespace,
            regex: Regex::new(r"(?m)\A(?<token_text>\s+)")
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
    match_len: usize,
    num_newlines: usize,
}

impl<'a> PartialEq for RuleApplicationResult<'a> {
    fn eq(&self, other: &Self) -> bool {
        return std::ptr::eq(self.token_rule, other.token_rule)
            && self.token_text == other.token_text
            && self.match_len == other.match_len
            && self.num_newlines == other.num_newlines;
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
    let mut out_num_newlines: usize = 0;
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
                    out_num_newlines = count_occurrences(&full_match.as_str(), '\n');
                    out_match_len = full_match.len();
                }
            }
        };
    }
    return RuleApplicationResult {
        token_rule: out_token_rule,
        token_text: out_token_text,
        match_len: out_match_len,
        num_newlines: out_num_newlines,
    };
}

// Given a string, returns a vector of tokens that comprise that string.
// Discards 'uninteresting' tokens like comments and whitespace.
fn make_token_stream(program_str: &str) -> Vec<Token> {
    let mut curr_idx: usize = 0;
    let mut curr_line_num: usize = 0;
    let mut out_tokens = Vec::new();

    while curr_idx < program_str.len() {
        let rule_application_result = apply_longest_matching_rule(&program_str[curr_idx..]);

        out_tokens.push(Token {
            token_class: rule_application_result.token_rule.token_class,
            token_text: String::from(
                &program_str[curr_idx..curr_idx + rule_application_result.match_len],
            ),
            line_num: curr_line_num,
        });

        curr_idx += rule_application_result.match_len;
        curr_line_num += rule_application_result.num_newlines;
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
                    match_len: r"// This is a comment.".len(),
                    num_newlines: 0,
                },
            ),
            (
                r"eval \v. v;",
                RuleApplicationResult {
                    token_rule: get_rule_for_token_class(TokenClass::Eval)
                        .expect("Unable to get rule for token class {TokenClass::Eval}"),
                    token_text: r"eval",
                    match_len: r"eval ".len(),
                    num_newlines: 0,
                },
            ),
        ];

        string_and_rule_vec
            .iter()
            .for_each(|(input_str, expected_result)| {
                let rule_application_result = apply_longest_matching_rule(*input_str);
                assert_eq!(&rule_application_result, expected_result);

                // // Check that the correct rule was retrieved.
                // assert!(std::ptr::eq(
                //     rule_application_result.token_rule,
                //     expected_rule
                // ));

                // // Check that the correct match len was computed.
                // assert_eq!(rule_application_result.match_len, expected_len);
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
                line_num: 0,
            },
            Token {
                token_class: TokenClass::Whitespace,
                token_text: String::from("\n"),
                line_num: 0,
            },
            Token {
                token_class: TokenClass::Def,
                token_text: String::from(r"def "),
                line_num: 1,
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
