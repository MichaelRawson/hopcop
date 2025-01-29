use crate::{
    syntax::{Application, Term},
    util::Perfect,
};
use fnv::FnvHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Tagged<T> {
    offset: usize,
    item: T,
}

impl<T> From<T> for Tagged<T> {
    fn from(item: T) -> Self {
        Self { offset: 0, item }
    }
}

impl<T> Tagged<T> {
    pub(crate) fn new(offset: usize, item: T) -> Self {
        Self { offset, item }
    }

    fn transfer<S>(&self, item: S) -> Tagged<S> {
        Tagged {
            offset: self.offset,
            item,
        }
    }

    fn map<S, F: FnOnce(T) -> S>(self, f: F) -> Tagged<S> {
        Tagged {
            offset: self.offset,
            item: f(self.item),
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct Substitution {
    map: FnvHashMap<Tagged<usize>, Tagged<Term>>,
}

impl Substitution {
    pub(crate) fn clear(&mut self) {
        self.map.clear()
    }

    pub(crate) fn unify(&mut self, left: Tagged<Term>, right: Tagged<Term>) -> bool {
        let mut todo = vec![];
        let mut next = Some((left, right));
        while let Some((left, right)) = next {
            let left = self.lookup(left);
            let right = self.lookup(right);
            if left == right {
                next = todo.pop();
                continue;
            }
            match (left.item, right.item) {
                (Term::Var(x), t @ Term::Var(_)) => {
                    self.map.insert(left.transfer(x), right.transfer(t));
                }
                (Term::Var(x), Term::App(app)) => {
                    if !self.bind(left.transfer(x), right.transfer(app)) {
                        return false;
                    }
                }
                (Term::App(t), Term::Var(x)) => {
                    if !self.bind(right.transfer(x), left.transfer(t)) {
                        return false;
                    }
                }
                (Term::App(lapp), Term::App(rapp)) => {
                    if lapp.symbol != rapp.symbol {
                        return false;
                    }
                    todo.extend(Iterator::zip(
                        lapp.args.iter().map(|arg| left.transfer(*arg)),
                        rapp.args.iter().map(|arg| right.transfer(*arg)),
                    ));
                }
            }
            next = todo.pop();
        }
        true
    }

    fn bind(&mut self, x: Tagged<usize>, t: Tagged<Perfect<Application>>) -> bool {
        let mut todo: Vec<_> = t.item.args.iter().map(|arg| t.transfer(*arg)).collect();
        while let Some(next) = todo.pop() {
            let next = self.lookup(next);
            match next.item {
                Term::Var(y) => {
                    if x == next.transfer(y) {
                        return false;
                    }
                }
                Term::App(app) => {
                    todo.extend(app.args.iter().map(|arg| next.transfer(*arg)));
                }
            }
        }
        self.map.insert(x, t.map(Term::App));
        true
    }

    fn lookup(&self, mut term: Tagged<Term>) -> Tagged<Term> {
        while let Term::Var(x) = term.item {
            if let Some(bound) = self.map.get(&term.transfer(x)) {
                term = *bound;
            } else {
                break;
            }
        }
        term
    }
}
