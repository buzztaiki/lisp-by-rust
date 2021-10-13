use std::env::args;
use std::fs::File;
use std::io::stdin;

mod env;
mod eval;
mod lisp;
mod reader;
mod repl;

fn main() -> lisp::Result<()> {
    if let Some(fname) = args().nth(1) {
        let f = File::open(fname).map_err(|e| lisp::Error(e.to_string()))?;
        repl::repl(eval::global_env(), f)
    } else {
        repl::repl(eval::global_env(), stdin())
    }
}
