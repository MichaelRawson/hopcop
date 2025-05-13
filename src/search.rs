use fnv::FnvBuildHasher;
use indexmap::IndexSet;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::db::{Atom, DB};
use crate::subst::{Located, Location, ROOT, Substitution};
use crate::syntax::{Clause, Extension, Literal, Matrix, Term};
use crate::tableau::Tableau;

// a point to restore `Search` to:
// several indices to truncate its internal data
#[derive(Debug, Default, Clone, Copy)]
struct Restore {
    tableau: usize,
    substitution: usize,
    trail: usize,
    closed: usize,
}

// collected data for doing proof search
pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    // random number generator for randomly selecting open branches
    rng: SmallRng,
    // tree of literals
    tableau: Tableau,
    // the global substitution
    substitution: Substitution,
    // variable trail: an ordered hashset
    trail: IndexSet<Atom, FnvBuildHasher>,
    // branches that have been closed: useful for bactracking `open`
    closed: Vec<Location>,
    // restore points after each step
    restore: Vec<Restore>,
    // set of open branches in no particular order
    open: Vec<Location>,
    // the clause we are currently learning
    // could just be a hashset but would like consistent iteration order
    learn: IndexSet<Atom, FnvBuildHasher>,
    // during any attempted inference, the previous length of the trail
    // used to determine which atoms should be learned
    learn_from: usize,
    // set of learned clauses
    db: DB,
    // current iterative deepening limit
    depth: usize,
    // scratch substitution for checking whether things unify
    scratch: Substitution,
}

impl<'matrix> Search<'matrix> {
    // jump back to a particular restore point
    fn restore(&mut self, restore: Restore) {
        self.tableau.truncate(restore.tableau);
        self.substitution.truncate(restore.substitution);
        self.trail.truncate(restore.trail);
        self.open.extend(self.closed.drain(restore.closed..));
        self.open.retain(|open| self.tableau.contains(*open));
    }

    // the beginning of proof search
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            rng: SmallRng::seed_from_u64(0),
            tableau: Tableau::default(),
            substitution: Substitution::default(),
            trail: IndexSet::default(),
            closed: vec![],
            restore: vec![],
            open: vec![],
            learn: IndexSet::default(),
            learn_from: 0,
            db: DB::default(),
            depth: 1,
            scratch: Substitution::default(),
        }
    }

    // are we done?
    pub(crate) fn is_closed(&self) -> bool {
        // open set is empty at first, so we also have to check that we chose some start clause
        !self.restore.is_empty() && self.open.is_empty()
    }

    // graphviz dump for checking proofs
    pub(crate) fn graphviz(&self) {
        self.tableau.graphviz()
    }

    // called iteratively externally:
    // either (1) make an inference step: start, reduce, extend
    // or (2) realise we are stuck and backjump somewhere
    pub(crate) fn step_or_backtrack(&mut self) {
        assert!(!self.is_closed());
        /*
        eprint!("trail:");
        for atom in &self.trail {
            eprint!(" {}", atom);
        }
        eprintln!();
        //eprintln!("substitution: {}", self.substitution);
         */

        // learned clause empty initially, filled out by failing to apply rules below
        self.learn.clear();
        // log where we were before we start mutating things
        self.learn_from = self.trail.len();
        self.restore.push(Restore {
            tableau: self.tableau.len(),
            substitution: self.substitution.len(),
            trail: self.learn_from,
            closed: self.closed.len(),
        });

        if self.open.is_empty() {
            if self.try_start() {
                // start rule succeeded, we're done here
                return;
            }
        } else {
            // randomly select open branch and remove it from `open`
            let index = self.rng.random_range(..self.open.len());
            let open = self.open.swap_remove(index);
            if self.try_close(open) {
                // closing the branch succeeded, we're done here
                self.closed.push(open);
                return;
            }
            // failed to close, put it back
            self.open.push(open);

            // add literal itself to learned clause
            self.learn
                .insert(Atom::Place(open, self.tableau[open].literal));
        }

        // all rules failed here
        self.restore.pop();

        /*
        eprint!("learn:");
        for reason in &self.learn {
            eprint!(" {}", reason);
        }
        eprintln!();
        */

        // all learned atoms should be in the trail
        assert!(self.learn.iter().all(|a| self.trail.contains(a)));

        // if the learned clause is empty, we need to increase depth limit
        if self.learn.is_empty() {
            // DB contains clauses that are only true with the current depth limit, clear it
            // does not pay off to try retaining them: exponentially more clauses at depth limit++
            self.db.clear();
            self.depth += 1;
            dbg!(self.depth);
            return;
        }

        // do the backjump
        // first, determine where in the trail the learned clause is falsified
        let conflict_position = self
            .trail
            .iter()
            .rposition(|atom| self.learn.contains(atom))
            .expect("live atoms do not contain learned clause");
        // work out which inference step that corresponds to
        let restore_position = self
            .restore
            .iter()
            .rposition(|restore| restore.trail <= conflict_position)
            .unwrap_or_default();

        // jump back to there
        let restore = self.restore[restore_position];
        self.restore.truncate(restore_position);
        self.restore(restore);

        // insert the learned clause to the database
        self.db.insert(self.learn.drain(..).collect(), &self.trail);
    }

    // try to apply a start rule
    // could fail if e.g. a learned clause prevents it
    fn try_start(&mut self) -> bool {
        for start in &self.matrix.start {
            if self.start(start) {
                return true;
            }
        }
        false
    }

    // try to start with a particular `start` clause
    fn start(&mut self, start: &'static Clause) -> bool {
        assert!(self.tableau.is_empty());
        assert!(self.substitution.is_empty());
        assert!(self.trail.is_empty());
        assert!(self.closed.is_empty());
        assert!(self.open.is_empty());

        // add all the literals to the tableau and `open`
        for (index, literal) in start.literals.iter().copied().enumerate() {
            let location = self.add_child(ROOT, literal, index, false);
            self.open.push(location);
        }
        // add the disequations from the new clause
        self.trail.extend(
            start
                .disequations
                .iter()
                .map(|d| Atom::Disequation(ROOT.locate(d.left), ROOT.locate(d.right))),
        );
        // check that we didn't violate anything
        if !self.check_trail_consistency(0) {
            self.tableau.clear();
            self.trail.clear();
            self.open.clear();
            return false;
        }
        true
    }

    // try to close an open branch with a reduction or extension rule
    fn try_close(&mut self, open: Location) -> bool {
        let node = self.tableau[open];

        // reduction rules: iterate upwards through ancestors
        let mut ancestor = node.parent;
        while ancestor != ROOT {
            if self.reduce(ancestor, open) {
                return true;
            }
            ancestor = self.tableau[ancestor].parent;
        }

        // at the iterative deepening limit, no extensions can be made
        if node.depth == self.depth {
            return false;
        }

        // enforce regularity condition
        let restore_trail = self.trail.len();
        let mut ancestor = node.parent;
        let k = node.parent.locate(node.literal);
        while ancestor != ROOT {
            let member = self.tableau[ancestor];
            let l = member.parent.locate(member.literal);
            if self.could_unify(l, k) {
                self.trail.insert(Atom::Disequation(
                    l.map(|l| Term::App(l.atom)),
                    k.map(|k| Term::App(k.atom)),
                ));
            }
            ancestor = member.parent;
        }

        // check we don't already violate regularity by extending rather than reducing
        if !self.check_trail_consistency(restore_trail) {
            self.trail.truncate(restore_trail);
            return false;
        }

        // try extension rules
        let Literal { polarity, atom } = node.literal;
        for extension in self
            .matrix
            .index
            .get(&(!polarity, atom.symbol))
            .into_iter()
            .flatten()
        {
            if self.extend(open, *extension) {
                return true;
            }
        }

        self.trail.truncate(restore_trail);
        false
    }

    // try to reduce `open` with `parent`
    fn reduce(&mut self, parent: Location, open: Location) -> bool {
        let parent_node = self.tableau[parent];
        let open_node = self.tableau[open];
        let l = parent_node.parent.locate(parent_node.literal);
        let k = open_node.parent.locate(open_node.literal);

        // if `l` could never reduce `k`, we give a short explanation
        if parent_node.literal.polarity == open_node.literal.polarity || !self.could_unify(l, k) {
            self.learn.insert(Atom::CannotReduce(parent, open));
            return false;
        }

        // to undo the substitution if we fail later
        let restore_subst = self.substitution.len();
        // try connecting `l` and `k`: may fail if the rest of the substitution prevents it
        if !self.substitution.connect(l, k) {
            // learn from:
            // placement of `l` (already inserted)
            // placement of `k` (below)
            self.learn.insert(Atom::Place(parent, parent_node.literal));
            // ... and a series of variable bindings that prevented them unifying
            self.explain_connection_failure(l, k);
            return false;
        }

        let restore_trail = self.trail.len();
        // re-use the scratch bindings as a kind of propagation:
        // if we want to connect l and k, we have to bind some variables
        // NB *not* equivalent to using the new bindings in self.substitution:
        // may be implied by other previous bindings
        self.trail
            .extend(self.scratch.bindings().map(|(x, t)| Atom::Bind(*x, *t)));

        // check that we didn't violate any previously-learned clause
        if !self.check_trail_consistency(restore_trail) {
            self.substitution.truncate(restore_subst);
            self.trail.truncate(restore_trail);
            return false;
        }
        true
    }

    // try to extend at `open` with a particular `extension` step
    fn extend(&mut self, open: Location, extension: Extension) -> bool {
        let node = self.tableau[open];
        let l = node.parent.locate(node.literal);
        let k = open.locate(extension.clause.literals[extension.index]);
        // if l and k could never unify, we don't need to consider this step further
        if !self.could_unify(l, k) {
            return false;
        }

        let restore_subst = self.substitution.len();
        // ...if however they could, but don't because of some bindings,
        if !self.substitution.connect(l, k) {
            // ...we should explain why
            self.explain_connection_failure(l, k);
            return false;
        }

        let restore_tableau = self.tableau.len();
        let restore_trail = self.trail.len();
        let restore_open = self.open.len();
        // add those bindings to the trail if successful
        self.trail
            .extend(self.scratch.bindings().map(|(x, t)| Atom::Bind(*x, *t)));
        // add the clause to the tableau...
        for (index, literal) in extension.clause.literals.iter().copied().enumerate() {
            let location = self.add_child(open, literal, index, index != extension.index);
            if index != extension.index {
                self.open.push(location);
            }
        }
        // ...and its disequations to the trail
        self.trail.extend(
            extension
                .clause
                .disequations
                .iter()
                .map(|d| Atom::Disequation(open.locate(d.left), open.locate(d.right))),
        );

        // something bad, give up on this one
        if !self.check_trail_consistency(restore_trail) {
            self.substitution.truncate(restore_subst);
            self.tableau.truncate(restore_tableau);
            self.trail.truncate(restore_trail);
            self.open.truncate(restore_open);
            return false;
        }

        true
    }

    // check that the trail is consistent with the database (and reality)
    // only the entries beyond `after` are checked
    fn check_trail_consistency(&mut self, after: usize) -> bool {
        // check that new atoms do not cause a conflict
        for atom in &self.trail[after..] {
            if let Some(conflicts) = self.db.find_conflicts(*atom, &self.trail) {
                // if we find a conflict, add it to `learn`
                // if more than one, choose the conflict that adds least to `learn`
                let chosen = conflicts
                    .iter()
                    .min_by_key(|conflict| {
                        conflict
                            .iter()
                            .filter(|a| {
                                self.trail.get_index_of(*a).unwrap() < self.learn_from
                                    && !self.learn.contains(*a)
                            })
                            .count()
                    })
                    .unwrap();
                // "resolve away" atoms occuring after `learn_from` in the trail
                self.learn.extend(
                    chosen
                        .iter()
                        .filter(|a| self.trail.get_index_of(*a).unwrap() < self.learn_from),
                );
                return false;
            }
        }

        // check that disequations are OK so far
        for (index, atom) in self.trail.iter().copied().enumerate() {
            let (left, right) = if let Atom::Disequation(left, right) = atom {
                (left, right)
            } else {
                continue;
            };
            if self.substitution.equal(left, right) {
                self.explain_equal(left, right);
                if index < self.learn_from {
                    self.learn.insert(atom);
                }
                return false;
            }
        }
        true
    }

    // could `l` and `k` _ever_ be unified?
    // if yes, `self.scratch` contains their mgu: NB this is sometimes used!
    fn could_unify(&mut self, l: Located<Literal>, k: Located<Literal>) -> bool {
        self.scratch.clear();
        self.scratch.connect(l, k)
    }

    // add a literal to the tableau and add suitable atoms to the trail
    fn add_child(
        &mut self,
        open: Location,
        literal: Literal,
        index: usize,
        try_reduce: bool,
    ) -> Location {
        let location = self.tableau.add_child(open, literal, index);
        self.trail.insert(Atom::Place(location, literal));
        if !try_reduce {
            return location;
        }

        // iterate through its ancestors and check whether a reduction is possible
        let mut ancestor = open;
        while ancestor != ROOT {
            let node = self.tableau[ancestor];
            if node.literal.polarity == literal.polarity
                || !self.could_unify(node.parent.locate(node.literal), open.locate(literal))
            {
                // if not, add a "cannot reduce" atom
                self.trail.insert(Atom::CannotReduce(ancestor, location));
            }
            ancestor = node.parent;
        }
        location
    }

    // explain why `l` cannot be unified with `k` in terms of bindings from `trail[..learn_from]`
    // insert the result into `learn`
    fn explain_connection_failure(&mut self, l: Located<Literal>, k: Located<Literal>) {
        self.scratch.clear();
        assert!(self.scratch.connect(l, k));

        // bind everything from `learn` as we won't get anything new from these
        for atom in &self.learn {
            if let Atom::Bind(x, t) = *atom {
                if !self.scratch.unify(x.map(Term::Var), t) {
                    return;
                }
            }
        }

        // we assume here that connecting l and k
        // was the only source of bindings in trail[learn_from..]
        'outer: loop {
            let reset = self.scratch.len();
            // try binding everything we didn't bind yet
            for atom in &self.trail[..self.learn_from] {
                let (x, t) = if let Atom::Bind(x, t) = *atom {
                    (x, t)
                } else {
                    continue;
                };
                if self.learn.contains(atom) {
                    continue;
                }
                if self.scratch.unify(x.map(Term::Var), t) {
                    continue;
                }
                // when we can't, the last atom we tried is part of the reason
                self.scratch.truncate(reset);
                self.learn.insert(*atom);
                // either we can now bind it, in which case carry on...
                if self.scratch.unify(x.map(Term::Var), t) {
                    continue 'outer;
                } else {
                    // ...or we can't and we're done
                    return;
                }
            }
            unreachable!()
        }
    }

    // explain why `left` is equal to `right` in terms of bindings from `trail[..learn_from]`
    // insert the result into `learn`
    fn explain_equal(&mut self, left: Located<Term>, right: Located<Term>) {
        self.scratch.clear();

        // assume all bindings are consistent
        // bind upfront:
        // 1. those after `learn_from` on the basis that they cannot be learned
        // 2. bindings from `learn` as we won't get anything new from these
        for atom in self.trail[self.learn_from..]
            .iter()
            .chain(self.learn.iter())
        {
            if let Atom::Bind(x, t) = *atom {
                assert!(self.scratch.unify(x.map(Term::Var), t));
            }
        }
        // already equal, done here
        if self.scratch.equal(left, right) {
            return;
        }

        'outer: loop {
            let reset = self.scratch.len();
            // try binding everything we didn't bind yet
            for atom in &self.trail[..self.learn_from] {
                let (x, t) = if let Atom::Bind(x, t) = *atom {
                    (x, t)
                } else {
                    continue;
                };
                if self.learn.contains(atom) {
                    continue;
                }
                assert!(self.scratch.unify(x.map(Term::Var), t));
                if !self.scratch.equal(left, right) {
                    continue;
                }
                // when we can't without equating left and right,
                // the last atom we tried is part of the reason
                self.scratch.truncate(reset);
                self.learn.insert(*atom);
                assert!(self.scratch.unify(x.map(Term::Var), t));
                // either we can now bind it, in which case carry on...
                if self.scratch.equal(left, right) {
                    return;
                } else {
                    // ...or we can't and we're done
                    continue 'outer;
                }
            }
            unreachable!()
        }
    }
}
