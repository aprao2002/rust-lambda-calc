//! Parser and program execution code that represents programs as a tree where
//! each node references other nodes via `Box` smart pointers.

pub mod box_tree_ast;
pub mod box_tree_execution;
pub mod box_tree_recursive_descent_parsing;
