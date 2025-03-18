use fnv::{FnvHashMap, FnvHashSet};
use std::collections::VecDeque;
use std::fmt;

use crate::subst::{Substitution, Tagged};
use crate::syntax::{Clause, Literal, Matrix, Position};
use crate::util::Perfect;

const DEPTH_LIMIT: usize = 4;

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

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    map: FnvHashMap<(usize, usize), usize>,
    members: FnvHashMap<usize, Member>,
    open: VecDeque<usize>,
    substitution: Substitution,
    trail: Vec<Rule>,
    learned: FnvHashSet<Rule>,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        Self {
            matrix,
            map: FnvHashMap::default(),
            members: FnvHashMap::default(),
            open: VecDeque::default(),
            substitution: Substitution::default(),
            trail: vec![],
            learned: FnvHashSet::default(),
        }
    }

    pub(crate) fn closed(&self) -> bool {
        self.open.is_empty() && !self.trail.is_empty()
    }

    pub(crate) fn graphviz(&self) {
        println!("digraph tableau {{");
        println!("\tnode [shape=none];");
        println!("\tl0 [label=\"\"];");
        for (location, member) in &self.members {
            println!(
                "\tl{} [label=\"{}. {}\"];",
                location, location, member.literal
            );
            println!("\tl{} -> l{};", member.parent, location);
        }
        println!("}}");
    }

    pub(crate) fn expand_or_backtrack(&mut self) {
        assert!(!self.closed());
        for rule in &self.trail {
            eprint!(" {}", rule);
        }
        eprintln!();
        self.learned.clear();

        if let Some(at) = self.open.pop_front() {
            let restore = self.substitution.len();
            let member = self.members[&at];
            let mut parent = member.parent;
            while parent != 0 {
                let member = self.members[&parent];
                let grandparent = member.parent;
                if self.apply_rule(Rule::Reduce(at, parent)) {
                    return;
                }
                self.substitution.undo_to(restore);
                parent = grandparent;
            }

            let Literal { polarity, atom } = member.literal;
            if member.depth == DEPTH_LIMIT {
                // TODO more complex logic here to make more general lemmas?
            } else if let Some(positions) = self.matrix.index.get(&(!polarity, atom.symbol)) {
                for position in positions {
                    if self.apply_rule(Rule::Extend(at, *position)) {
                        return;
                    }
                    self.substitution.undo_to(restore);
                }
            }

            parent = member.parent;
            for rule in self.trail.iter().rev() {
                match rule {
                    Rule::Start(_) => {
                        self.learned.insert(*rule);
                    }
                    Rule::Extend(here, _) if *here == parent => {
                        eprintln!("rule: {}", rule);
                        parent = self.members[&parent].parent;
                        self.learned.insert(*rule);
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

        eprint!("learn:");
        for reason in &self.learned {
            eprint!(" {}", reason);
        }
        eprintln!();

        self.graphviz();
        todo!()
    }

    fn apply_rule(&mut self, rule: Rule) -> bool {
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
        assert!(self.members.is_empty());
        assert!(self.open.is_empty());
        for (index, literal) in clause.literals.iter().enumerate() {
            let location = self.location(0, index);
            let member = Member {
                parent: 0,
                depth: 0,
                literal: *literal,
            };
            assert!(self.members.insert(location, member).is_none());
            self.open.push_back(location);
        }
        true
    }

    fn reduce(&mut self, at: usize, ancestor: usize) -> bool {
        let l = self.members[&at];
        let l = Tagged::new(l.parent, l.literal);
        let k = self.members[&ancestor];
        let k = Tagged::new(k.parent, k.literal);
        if !self.substitution.connect(l, k) {
            self.explain_unification_failure(l, k);
            return false;
        }
        true
    }

    fn extend(&mut self, at: usize, position: Position) -> bool {
        let member = self.members[&at];
        let l = Tagged::new(at, position.literal);
        let k = Tagged::new(member.parent, member.literal);
        if !self.substitution.connect(l, k) {
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
            self.members.insert(location, member);
            if *literal != position.literal {
                self.open.push_back(location);
            }
        }
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
                        let l = self.members[at];
                        let l = Tagged::new(l.parent, l.literal);
                        let k = self.members[ancestor];
                        let k = Tagged::new(k.parent, k.literal);
                        (l, k)
                    }
                    Rule::Extend(at, position) => {
                        let member = self.members[at];
                        let l = Tagged::new(*at, position.literal);
                        let k = Tagged::new(member.parent, member.literal);
                        (l, k)
                    }
                };
                if !substitution.connect(l, k) {
                    substitution.undo_to(reset);
                    self.learned.insert(*rule);
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
        let next = self.map.len() + 1;
        *self.map.entry((parent, child)).or_insert(next)
    }
}
