use fnv::{FnvBuildHasher, FnvHashSet};
use indexmap::IndexSet;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::db::{Atom, DB};
use crate::subst::{Substitution, Tagged};
use crate::syntax::{Application, Clause, Extension, Literal, Matrix};
use crate::tableau::{Location, ROOT, Tableau};
use crate::util::Perfect;

fn could_unify(l: Literal, k: Literal) -> bool {
    l.polarity != k.polarity
        && Substitution::default().unify_application(Tagged::new(0, l.atom), Tagged::new(1, k.atom))
}

#[derive(Debug, Default, Clone, Copy)]
struct Restore {
    tableau: usize,
    substitution: usize,
    atoms: usize,
    closed: usize,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    rng: SmallRng,
    tableau: Tableau,
    substitution: Substitution,
    atoms: IndexSet<Atom, FnvBuildHasher>,
    closed: Vec<Location>,
    restore: Vec<Restore>,
    open: Vec<Location>,
    learn: FnvHashSet<Atom>,
    explain_substitution: Substitution,
    db: DB,
    depth: usize,
}

impl<'matrix> Search<'matrix> {
    fn restore(&mut self, restore: Restore) {
        self.tableau.truncate(restore.tableau);
        self.substitution.truncate(restore.substitution);
        self.atoms.truncate(restore.atoms);
        self.open.extend(self.closed.drain(restore.closed..));
        self.open.retain(|open| self.tableau.contains(*open));
    }

    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            rng: SmallRng::seed_from_u64(0),
            tableau: Tableau::default(),
            substitution: Substitution::default(),
            atoms: IndexSet::default(),
            closed: vec![],
            restore: vec![],
            open: vec![],
            learn: FnvHashSet::default(),
            explain_substitution: Substitution::default(),
            db: DB::default(),
            depth: 1,
        }
    }

    pub(crate) fn is_closed(&self) -> bool {
        !self.restore.is_empty() && self.open.is_empty()
    }

    pub(crate) fn graphviz(&self) {
        self.tableau.graphviz()
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        assert!(!self.is_closed());
        /*
        eprint!("atoms:");
        for atom in &self.atoms {
            eprint!(" {}", atom);
        }
        eprintln!();
        eprintln!("substitution: {}", self.substitution);
        */

        self.learn.clear();
        self.restore.push(Restore {
            tableau: self.tableau.len(),
            substitution: self.substitution.len(),
            atoms: self.atoms.len(),
            closed: self.closed.len(),
        });

        if self.open.is_empty() {
            assert!(self.tableau.is_empty());
            assert!(self.substitution.is_empty());
            assert!(self.atoms.is_empty());
            assert!(self.closed.is_empty());

            for start in &self.matrix.start {
                if self.start(start) {
                    return;
                }
            }
        } else {
            let index = self.rng.random_range(..self.open.len());
            let open = self.open.swap_remove(index);
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
            self.open.push(open);
        }
        self.restore.pop();

        if self.learn.is_empty() {
            self.db = DB::default();
            self.depth += 1;
            dbg!(self.depth);
            return;
        }
        /*
        eprint!("learn:");
        for reason in &self.learn {
            eprint!(" {}", reason);
        }
        eprintln!();
        */

        let conflict_position = self
            .atoms
            .iter()
            .rposition(|atom| self.learn.contains(atom))
            .expect("live atoms do not contain learned clause");
        let restore_position = self
            .restore
            .iter()
            .rposition(|restore| restore.atoms <= conflict_position)
            .unwrap_or_default();

        let restore = self.restore[restore_position];
        self.restore.truncate(restore_position);
        self.restore(restore);
        self.db.insert(self.learn.drain().collect(), &self.atoms);
    }

    fn start(&mut self, start: &'static Clause) -> bool {
        for (index, literal) in start.literals.iter().copied().enumerate() {
            let location = self.tableau.locate(ROOT, index);
            self.atoms.insert(Atom::Place(location, literal));
            self.open.push(location);
            self.tableau.set(literal, location, ROOT, 1);
        }
        if !self.check_atoms_since(0) {
            self.tableau.clear();
            self.atoms.clear();
            self.open.clear();
            return false;
        }
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

        self.closed.push(open);
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
                self.open.push(location);
            }
            self.tableau
                .set(literal, location, open, self.tableau[open].depth + 1);
        }
        if !self.check_atoms_since(restore_atom) {
            self.substitution.truncate(restore_subst);
            self.tableau.truncate(restore_tab);
            self.atoms.truncate(restore_atom);
            self.open.truncate(restore_open);
            return false;
        }

        self.closed.push(open);
        true
    }

    fn check_atoms_since(&mut self, after: usize) -> bool {
        let atoms = &self.atoms[after..];
        for atom in atoms {
            if let Some(conflict) = self.db.find_conflict(*atom, &self.atoms) {
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
        self.explain_substitution.clear();
        assert!(self.explain_substitution.unify_application(left, right));
        for atom in &self.learn {
            let (from, to) = if let Atom::Connect(from, to) = *atom {
                (from, to)
            } else {
                continue;
            };
            let from_node = self.tableau[from];
            let to_node = self.tableau[to];
            let l = Tagged::new(from_node.parent.as_usize(), from_node.literal.atom);
            let k = Tagged::new(to_node.parent.as_usize(), to_node.literal.atom);
            if !self.explain_substitution.unify_application(l, k) {
                return;
            }
        }

        'outer: loop {
            let reset = self.explain_substitution.len();
            for atom in &self.atoms {
                if self.learn.contains(atom) {
                    continue;
                }
                let (from, to) = if let Atom::Connect(from, to) = *atom {
                    (from, to)
                } else {
                    continue;
                };
                let from_node = self.tableau[from];
                let to_node = self.tableau[to];
                let l = Tagged::new(from_node.parent.as_usize(), from_node.literal.atom);
                let k = Tagged::new(to_node.parent.as_usize(), to_node.literal.atom);
                if !self.explain_substitution.unify_application(l, k) {
                    self.explain_substitution.truncate(reset);
                    self.learn.insert(*atom);
                    self.learn.insert(Atom::Place(from, from_node.literal));
                    self.learn.insert(Atom::Place(to, to_node.literal));
                    if self.explain_substitution.unify_application(l, k) {
                        continue 'outer;
                    } else {
                        return;
                    }
                }
            }
            unreachable!()
        }
    }
}
