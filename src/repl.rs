use std::io;

use crate::env::Env;
use crate::eval;
use crate::lisp::*;
use crate::reader::Reader;

pub fn repl(mut env: Env, input: impl io::Read) -> Result<()> {
    let reader = Reader::new(input.bytes().flatten());
    for expr in reader {
        match expr {
            Ok(expr) => match eval::eval(&mut env, &expr) {
                Ok(expr) => println!("{}", expr),
                Err(e) => eprintln!("error: eval: {}", e),
            },
            Err(e) => eprintln!("error: read: {}", e),
        }
    }
    Ok(())
}
