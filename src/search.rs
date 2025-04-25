use fnv::{FnvBuildHasher, FnvHashSet};
use indexmap::IndexSet;
use std::collections::VecDeque;
use std::fmt;

use crate::subst::{Substitution, Tagged};
use crate::syntax::{Application, Clause, Extension, Literal, Matrix};
use crate::tableau::{Location, ROOT, Tableau};
use crate::util::Perfect;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Atom {
    Place(Location, Literal),
    Connect(Location, Location),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Place(location, literal) => write!(f, "{}@{}", literal, location),
            Atom::Connect(l, k) => write!(f, "{}~{}", l, k),
        }
    }
}

#[derive(Default)]
struct DB {
    clauses: Vec<Box<[Atom]>>,
}

impl DB {
    fn insert(&mut self, clause: Box<[Atom]>) {
        self.clauses.push(clause);
    }

    fn set(&mut self, set: Atom, already: &IndexSet<Atom, FnvBuildHasher>) -> Option<&[Atom]> {
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

enum Rule {
    Start(&'static Clause),
    Reduce(Location, Location),
    Extend(Location, Extension),
}

impl fmt::Display for Rule {
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
    proof: Vec<Rule>,
    atoms: IndexSet<Atom, FnvBuildHasher>,
    learn: FnvHashSet<Atom>,
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
            atoms: IndexSet::default(),
            learn: FnvHashSet::default(),
            db: DB::default(),
            depth: 4,
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
        eprint!("atoms:");
        for atom in &self.atoms {
            eprint!(" {}", atom);
        }
        eprintln!();
        eprintln!("substitution: {}", self.substitution);
        */

        self.learn.clear();
        if let Some(open) = self.open.pop_front() {
            let node = self.tableau[open];
            self.learn.insert(Atom::Place(open, node.literal));
            let mut parent = node.parent;
            while parent != ROOT {
                let member = self.tableau[parent];
                let grandparent = member.parent;
                if self.reduce(parent, open) {
                    return;
                }
                self.learn.insert(Atom::Place(parent, member.literal));
                parent = grandparent;
            }

            let Literal { polarity, atom } = node.literal;
            if node.depth == self.depth {
                // TODO more complex logic here to make more general lemmas?
            } else if let Some(extensions) = self.matrix.index.get(&(!polarity, atom.symbol)) {
                for extension in extensions {
                    if self.extend(open, *extension) {
                        return;
                    }
                }
            }
            self.open.push_front(open);
        } else {
            assert!(self.tableau.is_empty());
            assert!(self.substitution.is_empty());
            assert!(self.atoms.is_empty());
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
        eprint!("learn:");
        for reason in &self.learn {
            eprint!(" {}", reason);
        }
        eprintln!();
        */
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
        self.atoms.clear();
    }

    fn replay_rule(&mut self, rule: Rule) {
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

    fn start(&mut self, start: &'static Clause) -> bool {
        for (index, literal) in start.literals.iter().copied().enumerate() {
            let location = self.tableau.locate(ROOT, index);
            self.atoms.insert(Atom::Place(location, literal));
            self.open.push_back(location);
            self.tableau.set(literal, location, ROOT, 1);
        }
        if !self.check_atoms_since(0) {
            self.tableau.clear();
            self.atoms.clear();
            self.open.clear();
            return false;
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

        let restore_subst = self.substitution.len();
        let left = Tagged::new(parent_node.parent.as_usize(), parent_node.literal.atom);
        let right = Tagged::new(open_node.parent.as_usize(), open_node.literal.atom);
        if !self.substitution.unify_application(left, right) {
            self.explain_unification_failure(left, right);
            return false;
        }

        self.atoms.insert(Atom::Connect(parent, open));
        if !self.check_atoms_since(self.atoms.len() - 1) {
            self.substitution.truncate(restore_subst);
            self.atoms.pop();
            return false;
        }
        self.proof.push(Rule::Reduce(parent, open));
        true
    }

    fn extend(&mut self, open: Location, extension: Extension) -> bool {
        let open_node = self.tableau[open];
        let el = extension.clause.literals[extension.index];
        if !could_unify(open_node.literal, el) {
            return false;
        }

        let restore_subst = self.substitution.len();
        let left = Tagged::new(open_node.parent.as_usize(), open_node.literal.atom);
        let right = Tagged::new(open.as_usize(), el.atom);
        if !self.substitution.unify_application(left, right) {
            self.explain_unification_failure(left, right);
            return false;
        }

        let restore_tab = self.tableau.len();
        let restore_atom = self.atoms.len();
        let restore_open = self.open.len();
        for (index, literal) in extension.clause.literals.iter().copied().enumerate() {
            let location = self.tableau.locate(open, index);
            self.atoms.insert(Atom::Place(location, literal));
            if index == extension.index {
                self.atoms.insert(Atom::Connect(open, location));
            } else {
                self.open.push_back(location);
            }
            self.tableau
                .set(literal, location, open, self.tableau[open].depth + 1);
        }
        if !self.check_atoms_since(restore_atom) {
            self.substitution.truncate(restore_subst);
            self.tableau.truncate(restore_tab);
            self.atoms.truncate(restore_atom);
            while self.open.len() > restore_open {
                self.open.pop_back();
            }
            return false;
        }

        self.proof.push(Rule::Extend(open, extension));
        true
    }

    fn check_atoms_since(&mut self, after: usize) -> bool {
        let atoms = &self.atoms[after..];
        for atom in atoms {
            if let Some(conflict) = self.db.set(*atom, &self.atoms) {
                self.learn
                    .extend(conflict.iter().filter(|x| !atoms.iter().any(|a| a == *x)));
                return false;
            }
        }
        true
    }

    fn explain_unification_failure(
        &mut self,
        left: Tagged<Perfect<Application>>,
        right: Tagged<Perfect<Application>>,
    ) {
        let mut substitution = Substitution::default();
        assert!(substitution.unify_application(left, right));
        let mut reset = substitution.len();
        'find_conflict: loop {
            for atom in &self.atoms {
                let (from, to) = if let Atom::Connect(from, to) = *atom {
                    (from, to)
                } else {
                    continue;
                };
                let from_node = self.tableau[from];
                let to_node = self.tableau[to];
                let l = Tagged::new(from_node.parent.as_usize(), from_node.literal.atom);
                let k = Tagged::new(to_node.parent.as_usize(), to_node.literal.atom);
                if !substitution.unify_application(l, k) {
                    substitution.truncate(reset);
                    self.learn.insert(*atom);
                    self.learn.insert(Atom::Place(from, from_node.literal));
                    self.learn.insert(Atom::Place(to, to_node.literal));
                    if substitution.unify_application(l, k) {
                        reset = substitution.len();
                        continue 'find_conflict;
                    } else {
                        break 'find_conflict;
                    }
                }
            }
            unreachable!()
        }
    }
}
