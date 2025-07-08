# Rust Lambda Calculus Interpreter

This is an interpreter for lambda calculus programs written in Rust. For more details, see [this blog post](https://aprao2002.github.io/personal-website/blog/rust_lambda_calc_1/).

## Usage

```
git clone https://github.com/aprao2002/rust-lambda-calc.git
cd rust-lambda-calc

cargo run -- -s {path_to_src_file}
```

Some example source code to run the interpreter on can be found in the `test_programs` directory.

## Language Syntax

Users can add comments with '//'. The program consists of a sequence of def statements and eval statements. Eval statements are the lambda expressions that the interpreter will actually execute. Def statements essentially function as macros. As the interpreter executes an eval statement, if it ever needs to evaluate a variable that looks like a free variable, it will first check if there is a def statement that maps that free variable name to some sub-expression, and if so, the interpreter will substitute that sub-expression into the eval statement and continue execution. See the programs in the `test_programs` directory for examples.