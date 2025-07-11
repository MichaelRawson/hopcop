use fnv::FnvBuildHasher;
use indexmap::IndexMap;
use std::fmt;

use crate::syntax::{Application, IsGround, Literal, Term};
use crate::util::Perfect;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Location(usize);

impl Location {
    pub(crate) fn new(index: usize) -> Self {
        Self(index)
    }
}

pub(crate) const ROOT: Location = Location(0);

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Branch {
    pub(crate) location: Location,
    pub(crate) index: usize,
}

impl fmt::Display for Branch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}_{}", self.location, self.index)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Located<T> {
    location: Location,
    item: T,
}

impl Location {
    pub(crate) fn locate<T: IsGround>(self, item: T) -> Located<T> {
        let location = if item.is_ground() { ROOT } else { self };
        Located { location, item }
    }
}

impl<T: fmt::Display> fmt::Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.item, self.location)
    }
}

impl<T> Located<T> {
    fn transfer<S: IsGround>(&self, item: S) -> Located<S> {
        self.location.locate(item)
    }

    pub(crate) fn map<S, F: FnOnce(T) -> S>(self, f: F) -> Located<S> {
        Located {
            location: self.location,
            item: f(self.item),
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct Substitution {
    map: IndexMap<Located<usize>, Located<Term>, FnvBuildHasher>,
    unify: Vec<(Located<Term>, Located<Term>)>,
    occurs: Vec<Located<Term>>,
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (x, t) in &self.map {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{x} -> {t}")?;
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
        self.map.len()
    }

    pub(crate) fn clear(&mut self) {
        self.map.clear();
    }

    pub(crate) fn truncate(&mut self, to: usize) {
        self.map.truncate(to);
    }

    pub(crate) fn unify(&mut self, left: Located<Term>, right: Located<Term>) -> bool {
        let start = self.map.len();
        self.unify.clear();
        let mut next = Some((left, right));
        while let Some((left, right)) = next {
            let left = self.lookup(left);
            let right = self.lookup(right);
            if left == right {
                next = self.unify.pop();
                continue;
            }
            match (left.item, right.item) {
                (Term::Var(x), Term::Var(_)) => {
                    let left = left.transfer(x);
                    self.map.insert(left, right);
                }
                (Term::Var(x), Term::App(app)) => {
                    if !self.bind_unchecked(left.transfer(x), right.transfer(app)) {
                        self.truncate(start);
                        return false;
                    }
                }
                (Term::App(t), Term::Var(x)) => {
                    if !self.bind_unchecked(right.transfer(x), left.transfer(t)) {
                        self.truncate(start);
                        return false;
                    }
                }
                (Term::App(lapp), Term::App(rapp)) => {
                    if lapp.symbol != rapp.symbol {
                        self.truncate(start);
                        return false;
                    }
                    self.unify.extend(Iterator::zip(
                        lapp.args.iter().map(|arg| left.transfer(*arg)),
                        rapp.args.iter().map(|arg| right.transfer(*arg)),
                    ));
                }
            }
            next = self.unify.pop();
        }
        true
    }

    pub(crate) fn connect(&mut self, l: Located<Literal>, k: Located<Literal>) -> bool {
        self.unify(l.map(|l| Term::App(l.atom)), k.map(|r| Term::App(r.atom)))
    }

    pub(crate) fn equal(&mut self, left: Located<Term>, right: Located<Term>) -> bool {
        self.unify.clear();
        let mut next = Some((left, right));
        while let Some((left, right)) = next {
            let left = self.lookup(left);
            let right = self.lookup(right);
            if left == right {
                next = self.unify.pop();
                continue;
            }
            if let (Term::App(lapp), Term::App(rapp)) = (left.item, right.item) {
                if lapp.symbol != rapp.symbol {
                    return false;
                }
                self.unify.extend(Iterator::zip(
                    lapp.args.iter().map(|arg| left.transfer(*arg)),
                    rapp.args.iter().map(|arg| right.transfer(*arg)),
                ));
            } else {
                return false;
            }
            next = self.unify.pop();
        }
        true
    }

    fn bind_unchecked(&mut self, x: Located<usize>, t: Located<Perfect<Application>>) -> bool {
        self.occurs.clear();
        self.occurs
            .extend(t.item.args.iter().map(|arg| t.transfer(*arg)));
        while let Some(next) = self.occurs.pop() {
            let next = self.lookup(next);
            match next.item {
                Term::Var(y) => {
                    if x == next.transfer(y) {
                        return false;
                    }
                }
                Term::App(app) => {
                    self.occurs
                        .extend(app.args.iter().map(|arg| next.transfer(*arg)));
                }
            }
        }
        self.map.insert(x, t.map(Term::App));
        true
    }

    fn lookup(&self, mut term: Located<Term>) -> Located<Term> {
        while let Term::Var(x) = term.item {
            if let Some(bound) = self.map.get(&term.transfer(x)) {
                term = *bound;
            } else {
                break;
            }
        }
        term
    }

    pub(crate) fn bindings(&self) -> impl Iterator<Item = (&Located<usize>, &Located<Term>)> {
        self.bindings_since(0)
    }

    pub(crate) fn bindings_since(
        &self,
        since: usize,
    ) -> impl Iterator<Item = (&Located<usize>, &Located<Term>)> {
        self.map[since..].iter()
    }
}

pub(crate) struct Substituted<'a, T> {
    pub(crate) substitution: &'a Substitution,
    pub(crate) item: T,
}

impl<'a> fmt::Display for Substituted<'a, Located<Perfect<Application>>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let located = &self.item;
        let app = located.item;
        write!(f, "{}", app.symbol.name)?;
        if !app.args.is_empty() {
            write!(f, "(")?;
            let mut first = true;
            for arg in &app.args {
                if !first {
                    write!(f, ",")?;
                }
                first = false;
                Substituted {
                    substitution: self.substitution,
                    item: located.transfer(*arg),
                }
                .fmt(f)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'a> fmt::Display for Substituted<'a, Located<Term>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lookup = self.substitution.lookup(self.item);
        match lookup.item {
            Term::Var(x) => write!(f, "X{}_{}", x, lookup.location.0),
            Term::App(app) => Substituted {
                substitution: self.substitution,
                item: lookup.transfer(app),
            }
            .fmt(f),
        }
    }
}

impl<'a> fmt::Display for Substituted<'a, Located<Literal>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let located = &self.item;
        let literal = located.item;
        if literal.atom.symbol.is_equality() {
            Substituted {
                substitution: self.substitution,
                item: located.transfer(literal.atom.args[0]),
            }
            .fmt(f)?;
            write!(f, "{}", if literal.polarity { " = " } else { " != " })?;
            Substituted {
                substitution: self.substitution,
                item: located.transfer(literal.atom.args[1]),
            }
            .fmt(f)?;
        } else {
            if !literal.polarity {
                write!(f, "~")?;
            }
            Substituted {
                substitution: self.substitution,
                item: located.transfer(literal.atom),
            }
            .fmt(f)?;
        }
        Ok(())
    }
}
