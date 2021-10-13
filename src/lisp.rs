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

pub const NIL: &str = "nil";
pub const T: &str = "t";

impl Expr {
    pub fn car(&self) -> Result<Rc<Expr>> {
        match self {
            Expr::Cons(car, _) => Ok(car.clone()),
            Expr::Symbol(v) if v == NIL => Ok(nil()),
            _ => Err(Error(format!("expect list: {}", self))),
        }
    }

    pub fn cdr(&self) -> Result<Rc<Expr>> {
        match self {
            Expr::Cons(_, cdr) => Ok(cdr.clone()),
            Expr::Symbol(v) if v == NIL => Ok(nil()),
            _ => Err(Error(format!("expect list: {}", self))),
        }
    }

    pub fn is_nil(&self) -> bool {
        match self {
            Expr::Symbol(v) if v == NIL => true,
            _ => false,
        }
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, Expr::Symbol(_) | Expr::Number(_))
    }

    pub fn is_cons(&self) -> bool {
        matches!(self, Expr::Cons(_, _))
    }

    pub fn lisp_eq(&self, other: &Expr) -> bool {
        match (self, other) {
            (Expr::Symbol(x1), Expr::Symbol(y1)) => x1 == y1,
            (Expr::Number(x1), Expr::Number(y1)) => x1 == y1,
            _ => false,
        }
    }
}

pub trait RcExprExt {
    fn iter(&self) -> Iter;
}

impl RcExprExt for Rc<Expr> {
    fn iter(&self) -> Iter {
        Iter { xs: self.clone() }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Cons(head, rest) => {
                write!(f, "({}", head)?;
                let mut rest = rest.clone();
                while rest.clone().is_cons() {
                    write!(f, " {}", rest.car().map_err(|_| fmt::Error)?)?;
                    rest = rest.cdr().map_err(|_| fmt::Error)?;
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
        for (k, v) in self.argnames.clone().iter().zip(eval::evlis(env, args)?.iter()) {
            new_env.insert(k?, v?);
        }
        eval::eval(&mut new_env, self.body.car()?)
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
    symbol(NIL)
}

pub fn t() -> Rc<Expr> {
    symbol(T)
}

pub fn cons_list(xs: &[Rc<Expr>], tail: Rc<Expr>) -> Rc<Expr> {
    if let [head, rest @ ..] = xs {
        cons(head.clone(), cons_list(rest, tail))
    } else {
        tail
    }
}

pub fn list(xs: &[Rc<Expr>]) -> Rc<Expr> {
    cons_list(xs, nil())
}

pub fn bool_to_expr(x: bool) -> Rc<Expr> {
    if x {
        t()
    } else {
        nil()
    }
}

pub struct Iter {
    xs: Rc<Expr>,
}

impl Iter {
    fn next_item(&mut self) -> Result<Rc<Expr>> {
        let x = self.xs.car()?;
        self.xs = self.xs.cdr()?;
        Ok(x)
    }
}

impl Iterator for Iter {
    type Item = Result<Rc<Expr>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.xs.is_nil() {
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
        assert_eq!(cons(number(1), number(2)).car().unwrap(), number(1));
        assert_eq!(nil().car().unwrap(), nil());
        assert!(number(1).car().is_err());
        assert!(symbol("moo").car().is_err());
    }

    #[test]
    fn test_cdr() {
        assert_eq!(cons(number(1), number(2)).cdr().unwrap(), number(2));
        assert_eq!(
            list(&[number(1), number(2)]).cdr().unwrap(),
            list(&[number(2)])
        );
        assert_eq!(nil().cdr().unwrap(), nil());
        assert!(number(1).cdr().is_err());
        assert!(symbol("moo").cdr().is_err());
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
        assert_eq!(
            xs.iter().flatten().collect::<Vec<_>>(),
            (0..5).map(number).collect::<Vec<_>>()
        );

        let xs = cons(number(1), number(2));
        assert_eq!(xs.iter().flatten().collect::<Vec<_>>(), vec![number(1)]);
    }
}
