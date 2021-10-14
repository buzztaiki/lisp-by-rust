use std::env::args;
use std::fs::File;
use std::io::stdin;

use lib::{builtin, lisp, repl};

fn main() -> lisp::Result<()> {
    if let Some(fname) = args().nth(1) {
        let f = File::open(fname).map_err(|e| lisp::Error(e.to_string()))?;
        repl::repl(builtin::global_env(), f)
    } else {
        repl::repl(builtin::global_env(), stdin())
    }
}
