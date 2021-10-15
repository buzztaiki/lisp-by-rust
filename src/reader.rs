use crate::lisp::*;
use std::iter::Peekable;
use std::rc::Rc;

pub struct Reader<Iter: Iterator> {
    input: Peekable<Iter>,
}

impl<Iter: Iterator<Item = u8>> Reader<Iter> {
    pub fn new(input: Iter) -> Self {
        Self {
            input: input.peekable(),
        }
    }

    pub fn read(&mut self) -> Result<Option<Rc<Expr>>> {
        self.skip_whitespace();
        if let Some(c) = self.input.next() {
            match c {
                b'\'' => Ok(Some(list(&[symbol("quote"), Self::noeof(self.read())?]))),
                b'(' => self.read_list(),
                b')' => Err(Error("unbalanced parentheses".to_string())),
                _ => self.read_atom(c),
            }
        } else {
            Ok(None)
        }
    }

    fn read_list(&mut self) -> Result<Option<Rc<Expr>>> {
        let mut exprs = Vec::new();
        let mut cdr = nil();
        loop {
            self.skip_whitespace();
            if self.input.next_if_eq(&b')').is_some() {
                break Ok(Some(cons_list(&exprs, cdr)));
            }
            if self.input.next_if_eq(&b'.').is_some() {
                cdr = Self::noeof(self.read())?;
                continue;
            }

            if !cdr.is_nil() {
                break Err(Error("too many exprs after dot".to_string()));
            }
            exprs.push(Self::noeof(self.read())?);
        }
    }

    fn read_atom(&mut self, c: u8) -> Result<Option<Rc<Expr>>> {
        let mut xs = vec![c];
        let cont = |x: &u8| !x.is_ascii_whitespace() && ![b'\'', b'(', b')'].contains(x);
        while let Some(x) = self.input.next_if(cont) {
            xs.push(x);
        }
        let s = String::from_utf8(xs).map_err(|e| Error(e.to_string()))?;
        Ok(Some(s.parse::<i64>().map_or_else(|_| symbol(&s), number)))
    }

    fn skip_whitespace(&mut self) {
        while self.input.next_if(|x| x.is_ascii_whitespace()).is_some() {}
    }

    fn noeof(x: Result<Option<Rc<Expr>>>) -> Result<Rc<Expr>> {
        x?.ok_or_else(|| Error("unexpected eof".to_string()))
    }
}

impl<Iter: Iterator<Item = u8>> Iterator for Reader<Iter> {
    type Item = Result<Rc<Expr>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.read().transpose()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_read(sexpr: &str, expr: Rc<Expr>) {
        assert_eq!(Reader::new(sexpr.bytes()).read().unwrap(), Some(expr));
    }

    #[test]
    fn test_read_number() {
        assert_read("10", number(10));
    }

    #[test]
    fn test_read_symbol() {
        assert_read("moo", symbol("moo"));
    }

    #[test]
    fn test_read_quote() {
        assert_read("'moo", list(&[symbol("quote"), symbol("moo")]));
    }

    #[test]
    fn test_read_list() {
        assert_read(
            "(cons 10 (cons 20 30))",
            list(&[
                symbol("cons"),
                number(10),
                list(&[symbol("cons"), number(20), number(30)]),
            ]),
        );
    }

    #[test]
    fn test_read_doted_pair() {
        assert_read("(10 . 20)", cons(number(10), number(20)));
        assert_read(
            "(10 20 . 30)",
            cons(number(10), cons(number(20), number(30))),
        );

        assert!(Reader::new("(10 . 20 30)".bytes()).read().is_err());
    }

    #[test]
    fn test_as_iterator() {
        assert_eq!(Reader::new("1 2 3".bytes()).flatten().collect::<Vec<_>>(), vec![number(1), number(2), number(3)]);
    }
}
