use fnv::{FnvBuildHasher, FnvHashSet};
use indexmap::IndexSet;
use std::collections::VecDeque;
use std::fmt;

use crate::subst::{Substitution, Tagged};
use crate::syntax::{Clause, Extension, Literal, Matrix};
use crate::tableau::{Location, ROOT, Tableau};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Propagate {
    Place(Location, Literal),
    Connect(Location, Location),
}

impl fmt::Display for Propagate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Propagate::Place(location, literal) => write!(f, "({})@{}", literal, location),
            Propagate::Connect(l, k) => write!(f, "{}~{}", l, k),
        }
    }
}

#[derive(Default)]
struct DB {
    clauses: Vec<Box<[Propagate]>>,
}

impl DB {
    fn insert(&mut self, clause: Box<[Propagate]>) {
        self.clauses.push(clause);
    }

    fn set(
        &mut self,
        set: Propagate,
        already: &IndexSet<Propagate, FnvBuildHasher>,
    ) -> Option<&[Propagate]> {
        // TODO watched-literal shenanigans
        'clauses: for clause in &self.clauses {
            for rule in clause {
                if *rule != set && !already.contains(rule) {
                    continue 'clauses;
                }
            }
            return Some(clause);
        }
        None
    }
}

fn could_unify(l: Literal, k: Literal) -> bool {
    l.polarity != k.polarity
        && Substitution::default().unify_application(Tagged::new(0, l.atom), Tagged::new(1, k.atom))
}

enum Rule<'a> {
    Start(&'a Clause),
    Reduce(Location, Location),
    Extend(Location, &'a Extension),
}

impl<'a> fmt::Display for Rule<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rule::Start(clause) => write!(f, "s{}", clause.info.number),
            Rule::Reduce(l, k) => write!(f, "r{}-{}", l.as_usize(), k.as_usize()),
            Rule::Extend(l, e) => {
                write!(f, "e{}-{}-{}", l.as_usize(), e.clause.info.number, e.index)
            }
        }
    }
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    tableau: Tableau,
    substitution: Substitution,
    open: VecDeque<Location>,
    proof: Vec<Rule<'matrix>>,
    propagated: IndexSet<Propagate, FnvBuildHasher>,
    learn: FnvHashSet<Propagate>,
    db: DB,
    depth: usize,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            tableau: Tableau::default(),
            substitution: Substitution::default(),
            open: VecDeque::default(),
            proof: vec![],
            propagated: IndexSet::default(),
            learn: FnvHashSet::default(),
            db: DB::default(),
            depth: 3,
        }
    }

    pub(crate) fn is_closed(&self) -> bool {
        !self.proof.is_empty() && self.open.is_empty()
    }

    pub(crate) fn graphviz(&self) {
        self.tableau.graphviz()
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        if self.is_closed() {
            // println!("% SZS status Theorem");
            self.graphviz();
            std::process::exit(0);
        }

        eprint!("proof:");
        for rule in &self.proof {
            eprint!(" {}", rule);
        }
        eprintln!();
        /*
        eprint!("propagated:");
        for prop in &self.propagated {
            eprint!(" {}", prop);
        }
        eprintln!();
        */

        self.learn.clear();
        if let Some(open) = self.open.pop_front() {
            let node = self.tableau[open];
            self.learn.insert(Propagate::Place(open, node.literal));
            let mut parent = node.parent;
            while parent != ROOT {
                let member = self.tableau[parent];
                let grandparent = member.parent;
                if self.reduce(parent, open) {
                    return;
                }
                self.learn.insert(Propagate::Place(parent, member.literal));
                parent = grandparent;
            }

            let Literal { polarity, atom } = node.literal;
            if node.depth == self.depth {
                // TODO more complex logic here to make more general lemmas?
            } else if let Some(extensions) = self.matrix.index.get(&(!polarity, atom.symbol)) {
                for extension in extensions {
                    if self.extend(open, extension) {
                        return;
                    }
                }
            }
            self.open.push_front(open);
        } else {
            assert!(self.tableau.is_empty());
            assert!(self.substitution.is_empty());
            assert!(self.propagated.is_empty());
            for start in &self.matrix.start {
                if self.start(start) {
                    return;
                }
            }
        }
        assert!(!self.learn.is_empty());
        /*
        if self.learn.is_empty() {
            self.db = DB::default();
            self.depth += 1;
            dbg!(self.depth);
            return;
        }
        */
        eprint!("learn:");
        for reason in &self.learn {
            eprint!(" {}", reason);
        }
        eprintln!();
        self.db.insert(self.learn.drain().collect());

        let proof = std::mem::take(&mut self.proof);
        self.begin_replay();
        for rule in proof {
            self.replay_rule(rule);
        }
    }

    fn begin_replay(&mut self) {
        self.tableau.clear();
        self.substitution.clear();
        self.open.clear();
        self.propagated.clear();
    }

    fn replay_rule(&mut self, rule: Rule<'matrix>) {
        let ok = match rule {
            Rule::Start(clause) => self.start(clause),
            Rule::Reduce(l, k) => self.tableau.contains(k) && self.reduce(l, k),
            Rule::Extend(at, extend) => self.tableau.contains(at) && self.extend(at, extend),
        };
        if !ok {
            return;
        }
        match rule {
            Rule::Start(_) => {}
            Rule::Reduce(_, at) | Rule::Extend(at, _) => {
                // TODO avoid this linear-time scan
                self.open.retain(|x| *x != at);
            }
        }
    }

    fn start(&mut self, start: &'matrix Clause) -> bool {
        for (index, literal) in start.literals.iter().copied().enumerate() {
            let location = self.tableau.locate(ROOT, index);
            if !self.propagate(Propagate::Place(location, literal)) {
                self.tableau.clear();
                self.propagated.clear();
                self.open.clear();
                return false;
            }
            self.open.push_back(location);
            self.tableau.set(literal, location, ROOT, 1);
        }
        self.proof.push(Rule::Start(start));
        true
    }

    fn reduce(&mut self, parent: Location, open: Location) -> bool {
        let parent_node = self.tableau[parent];
        let open_node = self.tableau[open];
        if !could_unify(parent_node.literal, open_node.literal) {
            return false;
        }
        if !self.substitution.unify_application(
            Tagged::new(parent_node.parent.as_usize(), parent_node.literal.atom),
            Tagged::new(open_node.parent.as_usize(), open_node.literal.atom),
        ) {
            // TODO explain failure
            return false;
        }

        if !self.propagate(Propagate::Connect(parent, open)) {
            return false;
        }
        self.proof.push(Rule::Reduce(parent, open));
        true
    }

    fn extend(&mut self, open: Location, extension: &'matrix Extension) -> bool {
        let open_node = self.tableau[open];
        let el = extension.clause.literals[extension.index];
        if !could_unify(open_node.literal, el) {
            return false;
        }
        if !self.substitution.unify_application(
            Tagged::new(open_node.parent.as_usize(), open_node.literal.atom),
            Tagged::new(open.as_usize(), el.atom),
        ) {
            // TODO explain failure
            return false;
        }

        let restore_tab = self.tableau.len();
        let restore_prop = self.propagated.len();
        let restore_open = self.open.len();
        let mut failed = false;
        for (index, literal) in extension.clause.literals.iter().copied().enumerate() {
            let location = self.tableau.locate(open, index);
            if !self.propagate(Propagate::Place(location, literal)) {
                failed = true;
                break;
            }
            if index == extension.index {
                if !self.propagate(Propagate::Connect(open, location)) {
                    failed = true;
                    break;
                }
            } else {
                self.open.push_back(location);
            }
            self.tableau
                .set(literal, location, open, self.tableau[open].depth + 1);
        }
        if failed {
            self.tableau.truncate(restore_tab);
            self.undo_propagations(restore_prop);
            while self.open.len() > restore_open {
                self.open.pop_back();
            }
            return false;
        }

        self.proof.push(Rule::Extend(open, extension));
        true
    }

    fn propagate(&mut self, propagate: Propagate) -> bool {
        if let Some(conflict) = self.db.set(propagate, &self.propagated) {
            self.learn
                .extend(conflict.iter().filter(|x| **x != propagate));
            return false;
        }
        self.propagated.insert(propagate);
        true
    }

    fn undo_propagations(&mut self, to: usize) {
        self.propagated.truncate(to);
    }
}
