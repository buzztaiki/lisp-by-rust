use std::io;

use crate::env::Env;
use crate::eval;
use crate::lisp::*;
use crate::reader::Reader;

pub fn repl(mut env: Env, input: impl io::Read) -> Result<()> {
    let mut reader = Reader::new(input.bytes().flatten());

    loop {
        match reader.read() {
            Ok(expr) => match expr {
                Some(expr) => match eval::eval(&mut env, expr) {
                    Ok(expr) => println!("{}", expr),
                    Err(e) => eprintln!("error: eval: {}", e),
                },
                None => return Ok(()),
            },
            Err(e) => eprintln!("error: read: {}", e),
        }
    }
}
