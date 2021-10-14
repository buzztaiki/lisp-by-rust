use std::fmt;
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
    Function(Rc<FunctionExpr>),
}

#[derive(Debug)]
pub enum FunctionExpr {
    Builtin(Builtin),
    Function(Function),
}

#[derive(Debug)]
pub struct Function {
    env: Env,
    name: String,
    argnames: Rc<Expr>,
    body: Rc<Expr>,
}

pub struct Builtin {
    name: String,
    func: BuiltinFn,
}

pub type BuiltinFn = fn(&mut Env, &Expr) -> Result<Rc<Expr>>;

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

    pub fn pair(&self) -> Result<(Rc<Expr>, Rc<Expr>)> {
        self.car().and_then(|a| self.cdr().map(|b| (a, b)))
    }

    pub fn cadr(&self) -> Result<Rc<Expr>> {
        self.cdr()?.car()
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Expr::Symbol(v) if v == NIL)
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

    pub fn iter(&self) -> Iter {
        Iter::new(self)
    }

    pub fn from_bool(x: bool) -> Rc<Expr> {
        if x {
            t()
        } else {
            nil()
        }
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
                if !rest.is_nil() {
                    write!(f, " . {}", rest)?;
                }

                write!(f, ")")?;
                Ok(())
            }
            Expr::Symbol(x) => write!(f, "{}", x),
            Expr::Number(x) => write!(f, "{}", x),
            Expr::Function(x) => write!(f, "<function {}>", x.name()),
        }
    }
}

impl FunctionExpr {
    pub fn builtin(name: &str, func: BuiltinFn) -> Rc<Self> {
        Rc::new(Self::Builtin(Builtin {
            name: name.to_string(),
            func,
        }))
    }

    pub fn function(env: Env, name: &str, argnames: Rc<Expr>, body: Rc<Expr>) -> Rc<Self> {
        Rc::new(Self::Function(Function {
            env,
            name: name.to_string(),
            argnames,
            body,
        }))
    }

    pub fn name(&self) -> &str {
        match self {
            FunctionExpr::Builtin(x) => x.name.as_str(),
            FunctionExpr::Function(x) => x.name.as_str(),
        }
    }

    pub fn apply(&self, env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
        match self {
            FunctionExpr::Builtin(x) => x.apply(env, args),
            FunctionExpr::Function(x) => x.apply(env, args),
        }
    }
}

impl PartialEq for FunctionExpr {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for FunctionExpr {}

impl std::hash::Hash for FunctionExpr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(self as *const Self, state);
    }
}

impl Builtin {
    fn apply(&self, env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
        (self.func)(env, args)
    }
}

impl fmt::Debug for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Builtin").field("name", &self.name).finish()
    }
}

impl Function {
    fn apply(&self, env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
        let mut new_env = self.env.new_scope();
        for (k, v) in self.argnames.iter().zip(eval::evlis(env, args)?.iter()) {
            new_env.insert(k?, v?);
        }
        eval::eval(&mut new_env, &*self.body.car()?)
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

pub fn function(x: Rc<FunctionExpr>) -> Rc<Expr> {
    Rc::new(Expr::Function(x))
}

pub const NIL: &str = "nil";
pub const T: &str = "t";

thread_local!(static NIL_SYM: Rc<Expr> = symbol(NIL));
thread_local!(static T_SYM: Rc<Expr> = symbol(T));

pub fn nil() -> Rc<Expr> {
    NIL_SYM.with(|f| f.clone())
}

pub fn t() -> Rc<Expr> {
    T_SYM.with(|f| f.clone())
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

enum IterState {
    Init,
    Cont,
    Stop,
}

pub struct Iter<'a> {
    init: &'a Expr,
    xs: Rc<Expr>,
    state: IterState,
}

impl<'a> Iter<'a> {
    fn new(init: &'a Expr) -> Self {
        Self { init, xs: nil(), state: IterState::Init }
    }

    fn current(&self) -> Option<&Expr> {
        match self.state {
            IterState::Init => Some(self.init),
            IterState::Cont => Some(&self.xs),
            IterState::Stop => None,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = Result<Rc<Expr>>;

    fn next(&mut self) -> Option<Self::Item> {
        let xs = self.current()?;
        if xs.is_nil() {
            return None;
        }
        match xs.pair() {
            Ok((head, rest)) => {
                self.xs = rest;
                self.state = IterState::Cont;
                Some(Ok(head))
            },
            Err(e) => {
                self.state = IterState::Stop;
                Some(Err(e))
            },
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
        let xs = list(&(0..5).map(number).collect::<Vec<_>>());
        assert_eq!(
            xs.iter().flatten().collect::<Vec<_>>(),
            (0..5).map(number).collect::<Vec<_>>()
        );

        let xs = cons(number(1), number(2));
        assert_eq!(xs.iter().flatten().collect::<Vec<_>>(), vec![number(1)]);
    }
}
