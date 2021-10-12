use core::fmt;
use std::collections::HashMap;
use std::io;
use std::iter::Peekable;
use std::rc::Rc;

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct Error(String);

pub type Result<T> = std::result::Result<T, Error>;

pub type Env = HashMap<Rc<Expr>, Rc<Expr>>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Cons(Rc<Expr>, Rc<Expr>),
    Symbol(String),
    Number(i64),
    Function(Function),
}

#[derive(Debug, Eq)]
pub struct Function {
    env: Env,
    argnames: Rc<Expr>,
    body: Rc<Expr>,
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Cons(head, rest) => {
                write!(f, "({}", head)?;
                let mut rest = rest.clone();
                while consp(rest.clone()) {
                    write!(f, " {}", car(rest.clone()).map_err(|_| fmt::Error)?)?;
                    rest = cdr(rest).map_err(|_| fmt::Error)?;
                }
                if rest != nil() {
                    write!(f, " . {}", rest)?;
                }

                write!(f, ")")?;
                Ok(())
            }
            Expr::Symbol(x) => write!(f, "{}", x),
            Expr::Number(x) => write!(f, "{}", x),
            Expr::Function(_) => write!(f, "<function>"),
        }
    }
}

impl Function {
    pub fn new(env: &Env, argnames: Rc<Expr>, body: Rc<Expr>) -> Self {
        Self {
            env: env.clone(),
            argnames,
            body,
        }
    }

    pub fn apply(&self, env: &Env, args: Rc<Expr>) -> Result<Rc<Expr>> {
        let mut new_env = self.env.clone();
        for (k, v) in pairs(self.argnames.clone(), evlis(env, args)?)? {
            new_env.insert(k, v);
        }
        eval(&new_env, car(self.body.clone())?)
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl std::hash::Hash for Function {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(self as *const Self, state);
    }
}

pub fn cons(car: Rc<Expr>, cdr: Rc<Expr>) -> Rc<Expr> {
    Rc::new(Expr::Cons(car, cdr))
}

pub fn symbol(x: &str) -> Rc<Expr> {
    Rc::new(Expr::Symbol(x.to_string()))
}

pub fn number(x: i64) -> Rc<Expr> {
    Rc::new(Expr::Number(x))
}

pub fn function(x: Function) -> Rc<Expr> {
    Rc::new(Expr::Function(x))
}

pub fn nil() -> Rc<Expr> {
    symbol("nil")
}

pub fn t() -> Rc<Expr> {
    symbol("t")
}

pub fn cons_list(xs: &[Rc<Expr>], tail: Rc<Expr>) -> Rc<Expr> {
    if let [head, rest @ ..] = xs {
        cons(head.clone(), cons_list(rest, tail.clone()))
    } else {
        tail
    }
}

pub fn list(xs: &[Rc<Expr>]) -> Rc<Expr> {
    cons_list(xs, nil())
}

pub fn car(x: Rc<Expr>) -> Result<Rc<Expr>> {
    match x.as_ref() {
        Expr::Cons(car, _) => Ok(car.clone()),
        Expr::Symbol(_) if x == nil() => Ok(x),
        _ => Err(Error(format!("expect list: {}", x))),
    }
}

pub fn cdr(x: Rc<Expr>) -> Result<Rc<Expr>> {
    match x.as_ref() {
        Expr::Cons(_, cdr) => Ok(cdr.clone()),
        Expr::Symbol(_) if x == nil() => Ok(x),
        _ => Err(Error(format!("expect list: {}", x))),
    }
}

pub fn atom(x: Rc<Expr>) -> bool {
    match x.as_ref() {
        Expr::Symbol(_) | Expr::Number(_) => true,
        _ => false,
    }
}

pub fn consp(x: Rc<Expr>) -> bool {
    match x.as_ref() {
        Expr::Cons(_, _) => true,
        _ => false,
    }
}

pub fn eq(x: Rc<Expr>, y: Rc<Expr>) -> bool {
    match (x.as_ref(), y.as_ref()) {
        (Expr::Symbol(x1), Expr::Symbol(y1)) => x1 == y1,
        (Expr::Number(x1), Expr::Number(y1)) => x1 == y1,
        _ => false,
    }
}

pub fn bool_to_expr(x: bool) -> Rc<Expr> {
    if x {
        t()
    } else {
        nil()
    }
}

pub fn eval(env: &Env, x: Rc<Expr>) -> Result<Rc<Expr>> {
    match x.as_ref() {
        Expr::Cons(car, cdr) => apply(env, car.clone(), cdr.clone()),
        Expr::Symbol(_) if x == nil() || x == t() => Ok(x),
        Expr::Symbol(_) => env
            .get(&x)
            .cloned()
            .ok_or_else(|| Error(format!("symbol not found: {}", x))),
        Expr::Number(_) => Ok(x),
        Expr::Function(_) => Ok(x),
    }
}

pub fn evlis(env: &Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    if xs == nil() {
        Ok(xs)
    } else {
        Ok(cons(eval(env, car(xs.clone())?)?, evlis(env, cdr(xs)?)?))
    }
}

pub fn pairs(mut xs: Rc<Expr>, mut ys: Rc<Expr>) -> Result<Vec<(Rc<Expr>, Rc<Expr>)>> {
    let mut res = Vec::new();
    loop {
        if xs == nil() {
            return Ok(res);
        }

        res.push((car(xs.clone())?, car(ys.clone())?));
        xs = cdr(xs)?;
        ys = cdr(ys)?;
    }
}

pub fn evcon(env: &Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    // (cond ((eq x y) 'ok) (t 'ng))
    if xs == nil() {
        Ok(xs)
    } else {
        let x = car(xs.clone())?;
        if eval(env, car(x.clone())?)? != nil() {
            eval(env, car(cdr(x)?)?)
        } else {
            evcon(env, cdr(xs)?)
        }
    }
}

pub fn evlet(env: &Env, xs: Rc<Expr>) -> Result<Rc<Expr>> {
    // (let ((x 1) (y 2)) (cons x y))
    let mut new_env = env.clone();
    let mut vars = car(xs.clone())?;
    while vars != nil() {
        new_env.insert(
            car(car(vars.clone())?)?,
            eval(env, car(cdr(car(vars.clone())?)?)?)?,
        );
        vars = cdr(vars)?;
    }
    eval(&new_env, car(cdr(xs)?)?)
}

pub fn number_op(f: impl FnOnce(i64, i64) -> i64, args: Rc<Expr>) -> Result<Rc<Expr>> {
    match (car(args.clone())?.as_ref(), car(cdr(args)?)?.as_ref()) {
        (Expr::Number(x), Expr::Number(y)) => Ok(number(f(*x, *y))),
        (x, y) => Err(Error(format!("invalid number: {}, {}", x, y))),
    }
}

pub fn number_cmp(f: impl FnOnce(i64, i64) -> bool, args: Rc<Expr>) -> Result<Rc<Expr>> {
    match (car(args.clone())?.as_ref(), car(cdr(args)?)?.as_ref()) {
        (Expr::Number(x), Expr::Number(y)) => Ok(bool_to_expr(f(*x, *y))),
        (x, y) => Err(Error(format!("invalid number: {}, {}", x, y))),
    }
}

pub fn apply(env: &Env, func: Rc<Expr>, args: Rc<Expr>) -> Result<Rc<Expr>> {
    match func.as_ref() {
        Expr::Symbol(fname) => {
            let res = match fname.as_str() {
                "cons" => cons(eval(env, car(args.clone())?)?, eval(env, car(cdr(args)?)?)?),
                "car" => car(eval(env, car(args)?)?)?,
                "cdr" => cdr(eval(env, car(args)?)?)?,
                "quote" => car(args)?,
                "atom" => bool_to_expr(atom(car(args)?)),
                "eq" => bool_to_expr(eq(
                    eval(env, car(args.clone())?)?,
                    eval(env, car(cdr(args)?)?)?,
                )),
                "cond" => evcon(env, args)?,
                "let" => evlet(env, args)?,
                "lambda" => function(Function::new(env, car(args.clone())?, cdr(args.clone())?)),
                "+" => number_op(|x, y| x + y, evlis(env, args)?)?,
                "-" => number_op(|x, y| x - y, evlis(env, args)?)?,
                "*" => number_op(|x, y| x * y, evlis(env, args)?)?,
                "/" => number_op(|x, y| x / y, evlis(env, args)?)?,
                "<" => number_cmp(|x, y| x < y, evlis(env, args)?)?,
                "<=" => number_cmp(|x, y| x <= y, evlis(env, args)?)?,
                ">" => number_cmp(|x, y| x > y, evlis(env, args)?)?,
                ">=" => number_cmp(|x, y| x >= y, evlis(env, args)?)?,
                _ => apply(env, eval(env, func)?, evlis(env, args)?)?,
            };
            Ok(res)
        }
        Expr::Cons(_, _) => apply(env, eval(env, func)?, args),
        Expr::Function(function) => function.apply(env, args),
        _ => Err(Error(format!("invalid function: {}", func))),
    }
}

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

            if cdr != nil() {
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
        while let Some(_) = self.input.next_if(|x| x.is_ascii_whitespace()) {}
    }

    fn noeof(x: Result<Option<Rc<Expr>>>) -> Result<Rc<Expr>> {
        x?.ok_or_else(|| Error("unexpected eof".to_string()))
    }
}

pub fn repl(env: Env, input: impl io::Read) -> Result<()> {
    let mut reader = Reader::new(input.bytes().flat_map(|x| x));

    loop {
        match reader.read() {
            Ok(expr) => match expr {
                Some(expr) => match eval(&env, expr) {
                    Ok(expr) => println!("{}", expr),
                    Err(e) => eprintln!("error: eval: {}", e),
                },
                None => return Ok(()),
            },
            Err(e) => eprintln!("error: read: {}", e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_read(sexpr: &str, expr: Rc<Expr>) {
        assert_eq!(Reader::new(sexpr.bytes()).read().unwrap(), Some(expr));
    }

    fn assert_eval(env: &Env, sexpr: &str, expr: Rc<Expr>) {
        let input = Reader::new(sexpr.bytes()).read().unwrap().unwrap();
        dbg!(input.clone());
        assert_eq!(eval(env, input).unwrap(), expr);
    }

    #[test]
    fn test_list() {
        assert_eq!(
            list(&[number(1), number(2)]),
            cons(number(1), cons(number(2), nil()))
        );
    }

    #[test]
    fn test_car() {
        assert_eq!(car(cons(number(1), number(2))).unwrap(), number(1));
        assert_eq!(car(nil()).unwrap(), nil());
        assert!(car(number(1)).is_err());
        assert!(car(symbol("moo")).is_err());
    }

    #[test]
    fn test_cdr() {
        assert_eq!(cdr(cons(number(1), number(2))).unwrap(), number(2));
        assert_eq!(
            cdr(list(&[number(1), number(2)])).unwrap(),
            list(&[number(2)])
        );
        assert_eq!(cdr(nil()).unwrap(), nil());
        assert!(cdr(number(1)).is_err());
        assert!(cdr(symbol("moo")).is_err());
    }

    #[test]
    fn test_eval_number() {
        assert_eval(&Env::new(), "10", number(10));
    }

    #[test]
    fn test_eval_nil() {
        assert_eval(&Env::new(), "nil", nil());
    }

    #[test]
    fn test_eval_t() {
        assert_eval(&Env::new(), "t", t());
    }

    #[test]
    fn test_eval_cons() {
        assert_eval(&Env::new(), "(cons 1 2)", cons(number(1), number(2)));
    }

    #[test]
    fn test_eval_eq() {
        assert_eval(&Env::new(), "(eq 10 10)", t());

        let mut env = Env::new();
        env.insert(symbol("x"), number(10));
        assert_eval(&env, "(eq x 10)", t());
    }

    #[test]
    fn test_eval_lambda() {
        assert_eval(
            &Env::new(),
            "((lambda (a b) (cons a b)) 1 2)",
            cons(number(1), number(2)),
        );
        assert_eval(
            &Env::new(),
            "((lambda (a) ((lambda (b) b) a)) 'x)",
            symbol("x"),
        );
    }

    #[test]
    fn test_eval_let() {
        assert_eval(
            &Env::new(),
            "(let ((a 1) (b 2)) (cons 1 2))",
            cons(number(1), number(2)),
        );
    }

    #[test]
    fn test_eval_cond() {
        assert_eval(
            &Env::new(),
            "(let ((x 10)) (cond ((eq x 1) 'ng) ((eq x 10) 'ok) (t nil)))",
            symbol("ok"),
        );
    }

    #[test]
    fn test_eval_closure() {
        assert_eval(
            &Env::new(),
            "(let ((f (let ((x 1)) (lambda (y) (+ x y))))) (f 10))",
            number(11),
        );
        assert_eval(
            &Env::new(),
            "((let ((x 1)) (lambda (y) (+ x y))) 10)",
            number(11),
        );
    }

    #[test]
    fn test_eval_fib() {
        assert_eval(
            &Env::new(),
            r"
(let ((fib (lambda (fib n)
             (cond ((< n 2) n)
                   (t (+ (fib fib (- n 1)) (fib fib (- n 2))))))))
  (fib fib 10))
",
            number(55),
        );
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
    fn test_to_string() {
        assert_eq!(cons(number(10), symbol("x")).to_string(), "(10 . x)");
        assert_eq!(
            cons(number(10), cons(number(20), symbol("nil"))).to_string(),
            "(10 20)"
        );
        assert_eq!(
            cons(number(10), cons(number(20), number(30))).to_string(),
            "(10 20 . 30)"
        );
        assert_eq!(
            list(&[number(10), list(&[number(20), number(30)]), number(40)]).to_string(),
            "(10 (20 30) 40)"
        );
    }
}
