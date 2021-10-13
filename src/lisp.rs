use core::fmt;
use std::rc::Rc;

use crate::env::Env;
use crate::eval;

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct Error(pub String);

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Cons(Rc<Expr>, Rc<Expr>),
    Symbol(String),
    Number(i64),
    Function(Function),
}

#[derive(Debug)]
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
    pub fn new(env: Env, argnames: Rc<Expr>, body: Rc<Expr>) -> Self {
        Self {
            env,
            argnames,
            body,
        }
    }

    pub fn apply(&self, env: &mut Env, args: Rc<Expr>) -> Result<Rc<Expr>> {
        let mut new_env = self.env.new_scope();
        for (k, v) in iter(self.argnames.clone()).zip(iter(eval::evlis(env, args)?)) {
            new_env.insert(k?, v?);
        }
        eval::eval(&mut new_env, car(self.body.clone())?)
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for Function {}

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
    matches!(x.as_ref(), Expr::Symbol(_) | Expr::Number(_))
}

pub fn consp(x: Rc<Expr>) -> bool {
    matches!(x.as_ref(), Expr::Cons(_, _))
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

pub fn iter(xs: Rc<Expr>) -> Iter {
    Iter { xs }
}

pub struct Iter {
    xs: Rc<Expr>,
}

impl Iter {
    fn next_item(&mut self) -> Result<Rc<Expr>> {
        let x = car(self.xs.clone())?;
        self.xs = cdr(self.xs.clone())?;
        Ok(x)
    }
}

impl Iterator for Iter {
    type Item = Result<Rc<Expr>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.xs == nil() {
            None
        } else {
            let x = self.next_item();
            if x.is_err() {
                self.xs = nil();
            }
            Some(x)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn test_iter() {
        let xs = list((0..5).map(number).collect::<Vec<_>>().as_ref());
        assert_eq!(iter(xs).flatten().collect::<Vec<_>>(), (0..5).map(number).collect::<Vec<_>>());

        let xs = cons(number(1), number(2));
        assert_eq!(iter(xs).flatten().collect::<Vec<_>>(), vec![number(1)]);
    }
}
