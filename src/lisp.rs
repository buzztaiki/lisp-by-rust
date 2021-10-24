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
    SpecialForm(Function),
    Function(Function),
    Macro(Function),
}

pub struct Function {
    name: String,
    func: Box<dyn FunctionFn>,
}

pub trait FunctionFn: Fn(&mut Env, &Expr) -> Result<Rc<Expr>> {}
impl<F: Fn(&mut Env, &Expr) -> Result<Rc<Expr>>> FunctionFn for F {}

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
            Expr::Function(x) => write!(f, "{}", x),
        }
    }
}

impl FunctionExpr {
    pub fn special_form(f: Function) -> Rc<Self> {
        Rc::new(Self::SpecialForm(f))
    }

    pub fn function(f: Function) -> Rc<Self> {
        Rc::new(Self::Function(f))
    }

    pub fn macro_form(f: Function) -> Rc<Self> {
        Rc::new(Self::Macro(f))
    }

    pub fn name(&self) -> &str {
        match self {
            FunctionExpr::SpecialForm(x) => x.name.as_str(),
            FunctionExpr::Function(x) => x.name.as_str(),
            FunctionExpr::Macro(x) => x.name.as_str(),
        }
    }

    pub fn kind(&self) -> &str {
        match self {
            FunctionExpr::SpecialForm(_) => "special-form",
            FunctionExpr::Function(_) => "function",
            FunctionExpr::Macro(_) => "macro",
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

impl fmt::Display for FunctionExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{} {}>", self.kind(), self.name())
    }
}

impl Function {
    pub fn new(name: &str, func: impl FunctionFn + 'static) -> Self {
        Self {
            name: name.to_string(),
            func: Box::new(func),
        }
    }

    pub fn compound(env: &Env, name: &str, argnames: Rc<Expr>, body: Rc<Expr>) -> Self {
        let vars = env.capture(); 
        let f = move |env: &mut Env, args: &Expr| {
            let scope = &mut env.enter_scope();
            scope.extend(vars.iter().cloned());
            eval::bind_args(scope, &argnames, args)?;
            eval::eval_body(scope, &body)
        };
        Self::new(name, f)
    }

    pub fn apply(&self, env: &mut Env, args: &Expr) -> Result<Rc<Expr>> {
        (self.func)(env, args)
    }
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Function").field("name", &self.name).finish()
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
        Self {
            init,
            xs: nil(),
            state: IterState::Init,
        }
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
            }
            Err(e) => {
                self.state = IterState::Stop;
                Some(Err(e))
            }
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

        fn f(_: &mut Env, _: &Expr) -> Result<Rc<Expr>> {
            Ok(nil())
        }
        assert_eq!(
            function(FunctionExpr::special_form(Function::new("moo", f))).to_string(),
            "<special-form moo>"
        );
        assert_eq!(
            function(FunctionExpr::function(Function::new("woo", f))).to_string(),
            "<function woo>"
        );
        assert_eq!(
            function(FunctionExpr::macro_form(Function::new("goo", f))).to_string(),
            "<macro goo>"
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
