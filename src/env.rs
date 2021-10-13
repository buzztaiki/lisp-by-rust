use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::lisp::Expr;

#[derive(Debug)]
pub struct Env {
    env: EnvBoxPtr,
}

#[derive(Debug)]
struct EnvBox {
    env: HashMap<Rc<Expr>, Rc<Expr>>,
    parent: Option<EnvBoxPtr>,
}

type EnvBoxPtr = Rc<RefCell<EnvBox>>;

impl EnvBox {
    fn new(env: HashMap<Rc<Expr>, Rc<Expr>>, parent: Option<EnvBoxPtr>) -> EnvBoxPtr {
        Rc::new(Self { env, parent }.into())
    }

    fn insert(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        self.env.insert(k, v);
    }

    fn get(&self, k: &Expr) -> Option<Rc<Expr>> {
        if let Some(v) = self.env.get(k) {
            return Some(v.clone());
        }
        self.parent.as_ref()?.borrow().get(k)
    }
}

impl Env {
    pub fn new() -> Self {
        Self {
            env: EnvBox::new(HashMap::new(), None),
        }
    }

    pub fn insert(&mut self, k: Rc<Expr>, v: Rc<Expr>) {
        self.env.borrow_mut().insert(k, v);
    }

    pub fn get(&self, k: &Expr) -> Option<Rc<Expr>> {
        self.env.borrow().get(k)
    }

    pub fn new_scope(&self) -> Self {
        Self {
            env: EnvBox::new(HashMap::new(), Some(self.env.clone())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lisp::number;

    #[test]
    fn test() {
        let mut env = Env::new();
        env.insert(number(10), number(20));
        assert_eq!(env.get(&number(10)), Some(number(20)));

        let mut env2 = env.new_scope();
        assert_eq!(env2.get(&number(10)), Some(number(20)));

        env2.insert(number(10), number(30));
        assert_eq!(env2.get(&number(10)), Some(number(30)));
        assert_eq!(env.get(&number(10)), Some(number(20)));
    }
}
