use fnv::{FnvHashMap, FnvHashSet};
use std::collections::VecDeque;
use std::fmt;

use crate::subst::{Substitution, Tagged};
use crate::syntax::{Clause, Literal, Matrix, Position};
use crate::util::Perfect;

#[derive(Debug, Clone, Copy)]
struct Member {
    parent: usize,
    depth: usize,
    literal: Literal,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Rule {
    Start(Perfect<Clause>),
    Reduce(usize, usize),
    Extend(usize, Position),
}

#[derive(Default)]
struct DB {
    clauses: Vec<Box<[Rule]>>,
    set: FnvHashSet<Rule>,
}

impl DB {
    fn insert(&mut self, clause: Box<[Rule]>) {
        self.clauses.push(clause);
    }

    fn set(&mut self, new: Rule) -> Option<&[Rule]> {
        // TODO watched-literal shenanigans
        'clauses: for clause in &self.clauses {
            for rule in clause {
                if *rule != new && !self.set.contains(rule) {
                    continue 'clauses;
                }
            }
            return Some(clause);
        }
        self.set.insert(new);
        None
    }

    fn clear(&mut self) {
        self.set.clear();
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rule::Start(start) => write!(f, "s{}", start.info.number),
            Rule::Reduce(at, ancestor) => write!(f, "r{}-{}", at, ancestor),
            Rule::Extend(at, position) => write!(
                f,
                "e{}-{}-{}",
                at,
                position.clause.info.number,
                position
                    .clause
                    .literals
                    .iter()
                    .position(|x| x == &position.literal)
                    .unwrap()
            ),
        }
    }
}

#[derive(Default)]
pub(crate) struct Tableau {
    map: FnvHashMap<(usize, usize), usize>,
    members: Vec<Option<Member>>,
    open: VecDeque<usize>,
    substitution: Substitution,
}

impl Tableau {
    fn is_closed(&self) -> bool {
        self.open.is_empty()
    }

    fn members(&self) -> impl Iterator<Item = (usize, Member)> {
        self.members
            .iter()
            .enumerate()
            .filter_map(|(i, slot)| slot.map(|m| (i, m)))
    }

    fn first_open_branch(&self) -> Option<usize> {
        self.open.front().copied()
    }

    fn graphviz(&self) {
        println!("digraph tableau {{");
        println!("\tnode [shape=none];");
        println!("\tl0 [label=\"\"];");
        for (location, member) in self.members() {
            println!(
                "\tl{} [label=\"{}. {}\"];",
                location, location, member.literal
            );
            println!("\tl{} -> l{};", member.parent, location);
        }
        println!("}}");
    }
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    tableau: Tableau,
    trail: Vec<Rule>,
    learn: FnvHashSet<Rule>,
    db: DB,
    depth: usize,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            tableau: Tableau::default(),
            trail: vec![],
            learn: FnvHashSet::default(),
            db: DB::default(),
            depth: 1,
        }
    }

    pub(crate) fn is_closed(&self) -> bool {
        self.tableau.is_closed() && !self.trail.is_empty()
    }

    pub(crate) fn graphviz(&self) {
        self.tableau.graphviz()
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        if self.is_closed() {
            println!("% SZS status Theorem");
            std::process::exit(0);
        }
        /*
        for rule in &self.trail {
            eprint!(" {}", rule);
        }
        eprintln!();
        */
        self.learn.clear();

        if let Some(at) = self.tableau.first_open_branch() {
            let restore = self.tableau.substitution.len();
            let member = self.tableau.members[at].unwrap();
            let mut parent = member.parent;
            while parent != 0 {
                let member = self.tableau.members[parent].unwrap();
                let grandparent = member.parent;
                if self.apply_rule(Rule::Reduce(at, parent)) {
                    return;
                }
                self.tableau.substitution.undo_to(restore);
                parent = grandparent;
            }

            let Literal { polarity, atom } = member.literal;
            if member.depth == self.depth {
                // TODO more complex logic here to make more general lemmas?
            } else if let Some(positions) = self.matrix.index.get(&(!polarity, atom.symbol)) {
                for position in positions {
                    if self.apply_rule(Rule::Extend(at, *position)) {
                        return;
                    }
                    self.tableau.substitution.undo_to(restore);
                }
            }

            parent = member.parent;
            for rule in self.trail.iter().rev() {
                match rule {
                    Rule::Start(_) => {
                        self.learn.insert(*rule);
                    }
                    Rule::Extend(here, _) if *here == parent => {
                        parent = self.tableau.members[parent].unwrap().parent;
                        self.learn.insert(*rule);
                    }
                    _ => {}
                }
            }
        } else if self.trail.is_empty() {
            for start in &self.matrix.start {
                if self.apply_rule(Rule::Start(*start)) {
                    return;
                }
            }
        }

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
        self.db.insert(self.learn.iter().copied().collect());

        // TODO do backjumping less stupidly
        for member in &mut self.tableau.members {
            *member = None;
        }
        self.tableau.open.clear();
        self.tableau.substitution.clear();
        self.db.clear();
        let trail = std::mem::take(&mut self.trail);
        for rule in trail {
            if !self.apply_rule(rule) {
                break;
            }
        }
    }

    fn apply_rule(&mut self, rule: Rule) -> bool {
        if let Some(conflict) = self.db.set(rule) {
            for reason in conflict {
                if *reason != rule {
                    self.learn.insert(*reason);
                }
            }
            return false;
        }

        // check for violated learned clauses
        let applicable = match rule {
            Rule::Start(start) => self.start(&start),
            Rule::Reduce(at, ancestor) => self.reduce(at, ancestor),
            Rule::Extend(at, position) => self.extend(at, position),
        };
        if !applicable {
            return false;
        }
        // check for violated constraints
        self.trail.push(rule);
        true
    }

    fn start(&mut self, clause: &Clause) -> bool {
        assert!(self.tableau.open.is_empty());
        for (index, literal) in clause.literals.iter().enumerate() {
            let location = self.location(0, index);
            let member = Member {
                parent: 0,
                depth: 0,
                literal: *literal,
            };
            self.tableau.members[location] = Some(member);
            self.tableau.open.push_back(location);
        }
        true
    }

    fn reduce(&mut self, at: usize, ancestor: usize) -> bool {
        let l = self.tableau.members[at].unwrap();
        let l = Tagged::new(l.parent, l.literal);
        let k = self.tableau.members[ancestor].unwrap();
        let k = Tagged::new(k.parent, k.literal);
        if !self.tableau.substitution.connect(l, k) {
            self.explain_unification_failure(l, k);
            return false;
        }
        self.tableau.open.pop_front();
        true
    }

    fn extend(&mut self, at: usize, position: Position) -> bool {
        let member = self.tableau.members[at].unwrap();
        let l = Tagged::new(at, position.literal);
        let k = Tagged::new(member.parent, member.literal);
        if !self.tableau.substitution.connect(l, k) {
            self.explain_unification_failure(l, k);
            return false;
        }

        for (index, literal) in position.clause.literals.iter().enumerate() {
            let location = self.location(at, index);
            let member = Member {
                parent: at,
                depth: member.depth + 1,
                literal: *literal,
            };
            self.tableau.members[location] = Some(member);
            if *literal != position.literal {
                self.tableau.open.push_back(location);
            }
        }
        self.tableau.open.pop_front();
        true
    }

    fn explain_unification_failure(&mut self, l: Tagged<Literal>, k: Tagged<Literal>) {
        let mut substitution = Substitution::default();
        // they could never connect - TODO improve this
        if !substitution.connect(l, k) {
            return;
        }

        let mut reset = substitution.len();
        'find_conflict: loop {
            for rule in &self.trail[1..] {
                let (l, k) = match rule {
                    Rule::Start(_) => unreachable!(),
                    Rule::Reduce(at, ancestor) => {
                        let l = self.tableau.members[*at].unwrap();
                        let l = Tagged::new(l.parent, l.literal);
                        let k = self.tableau.members[*ancestor].unwrap();
                        let k = Tagged::new(k.parent, k.literal);
                        (l, k)
                    }
                    Rule::Extend(at, position) => {
                        let member = self.tableau.members[*at].unwrap();
                        let l = Tagged::new(*at, position.literal);
                        let k = Tagged::new(member.parent, member.literal);
                        (l, k)
                    }
                };
                if !substitution.connect(l, k) {
                    substitution.undo_to(reset);
                    self.learn.insert(*rule);
                    if substitution.connect(l, k) {
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

    fn location(&mut self, parent: usize, child: usize) -> usize {
        let next = self.tableau.map.len();
        *self.tableau.map.entry((parent, child)).or_insert_with(|| {
            self.tableau.members.push(None);
            next
        })
    }
}
