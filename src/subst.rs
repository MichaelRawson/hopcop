use std::fmt;

use crate::syntax::{Application, Term};
use crate::util::Perfect;
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

impl<T: fmt::Display> fmt::Display for Tagged<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.item, self.offset)
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
    trail: Vec<Tagged<usize>>,
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for x in &self.trail {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{} -> {}", x, self.map[x])?;
            first = false;
        }
        write!(f, "}}")
    }
}

impl Substitution {
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn len(&self) -> usize {
        self.trail.len()
    }

    pub(crate) fn clear(&mut self) {
        self.map.clear();
        self.trail.clear();
    }

    pub(crate) fn truncate(&mut self, to: usize) {
        assert!(to <= self.len());
        while to < self.len() {
            let next = self.trail.pop().unwrap();
            assert!(self.map.remove(&next).is_some());
        }
    }

    pub(crate) fn unify(&mut self, left: Tagged<Term>, right: Tagged<Term>) -> bool {
        let start = self.trail.len();
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
                (Term::Var(x), Term::Var(_)) => {
                    let left = left.transfer(x);
                    self.map.insert(left, right);
                    self.trail.push(left);
                }
                (Term::Var(x), Term::App(app)) => {
                    if !self.bind(left.transfer(x), right.transfer(app)) {
                        self.truncate(start);
                        return false;
                    }
                }
                (Term::App(t), Term::Var(x)) => {
                    if !self.bind(right.transfer(x), left.transfer(t)) {
                        self.truncate(start);
                        return false;
                    }
                }
                (Term::App(lapp), Term::App(rapp)) => {
                    if lapp.symbol != rapp.symbol {
                        self.truncate(start);
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

    pub(crate) fn unify_application(
        &mut self,
        left: Tagged<Perfect<Application>>,
        right: Tagged<Perfect<Application>>,
    ) -> bool {
        self.unify(left.map(Term::App), right.map(Term::App))
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
        self.trail.push(x);
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
