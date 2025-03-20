use crate::util::Perfect;
use fnv::{FnvHashMap, FnvHashSet};
use std::{fmt, rc::Rc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Sort {
    Bool,
    Obj,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum Name {
    Equality,
    Atom(&'static str),
    Quoted(&'static str),
    Number(&'static str),
    Distinct(&'static str),
    Skolem(usize),
    Definition(usize),
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Equality => write!(f, "sPE"),
            Self::Atom(s) | Self::Number(s) => write!(f, "{}", s),
            Self::Quoted(quoted) => write!(f, "'{}'", quoted),
            Self::Distinct(distinct) => write!(f, "\"{}\"", distinct),
            Self::Skolem(n) => write!(f, "sK{}", n),
            Self::Definition(n) => write!(f, "sP{}", n),
        }
    }
}

impl Name {
    pub(crate) fn needs_congruence(&self) -> bool {
        !matches!(self, Self::Equality | Self::Skolem(_) | Self::Definition(_))
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct Symbol {
    pub(crate) arity: usize,
    pub(crate) sort: Sort,
    pub(crate) name: Name,
}

impl Symbol {
    pub(crate) fn is_equality(&self) -> bool {
        matches!(self.name, Name::Equality)
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub(crate) struct Application {
    pub(crate) symbol: Perfect<Symbol>,
    pub(crate) args: Box<[Term]>,
}

impl fmt::Display for Application {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbol.name)?;
        if !self.args.is_empty() {
            write!(f, "({}", &self.args[0])?;
            for arg in &self.args[1..] {
                write!(f, ",{}", arg)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub(crate) enum Term {
    Var(usize),
    App(Perfect<Application>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(x) => write!(f, "X{}", x),
            Term::App(app) => write!(f, "{}", app),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Literal {
    pub(crate) polarity: bool,
    pub(crate) atom: Perfect<Application>,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.atom.symbol.is_equality() {
            self.atom.args[0].fmt(f)?;
            write!(f, "{}", if self.polarity { " = " } else { " != " })?;
            self.atom.args[1].fmt(f)
        } else {
            if !self.polarity {
                write!(f, "~")?;
            }
            write!(f, "{}", self.atom)
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub(crate) struct Disequation {
    pub(crate) left: Term,
    pub(crate) right: Term,
}

impl fmt::Display for Disequation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ≠ {}", self.left, self.right)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Extension {
    pub(crate) clause: Perfect<Clause>,
    pub(crate) index: usize,
}

#[derive(Debug, Clone)]
pub(crate) enum Source {
    Equality,
    Axiom { path: Rc<String>, name: String },
}

#[derive(Debug, Clone)]
pub(crate) struct Info {
    pub(crate) is_goal: bool,
    pub(crate) number: usize,
    pub(crate) source: Source,
}

#[derive(Debug)]
pub(crate) struct Clause {
    pub(crate) literals: Vec<Literal>,
    pub(crate) disequations: Vec<Disequation>,
    pub(crate) info: Info,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "cnf({}, {}, ",
            self.info.number,
            if self.info.is_goal {
                "negated_conjecture"
            } else {
                "axiom"
            }
        )?;
        if self.literals.is_empty() {
            write!(f, "$false")?;
        } else {
            write!(f, "{}", self.literals[0])?;
            for literal in &self.literals[1..] {
                write!(f, " | {}", literal)?;
            }
        }
        write!(f, "). %")?;
        for disequation in &self.disequations {
            write!(f, " {}", disequation)?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub(crate) struct Matrix {
    pub(crate) clauses: Vec<Perfect<Clause>>,
    pub(crate) start: Vec<Perfect<Clause>>,
    pub(crate) index: FnvHashMap<(bool, Perfect<Symbol>), Vec<Extension>>,
    pub(crate) have_conjecture: bool,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RcTerm {
    Variable(usize),
    Application(Rc<RcApplication>),
}

impl RcTerm {
    fn variables(&self, vars: &mut FnvHashSet<usize>) {
        match self {
            Self::Variable(x) => {
                vars.insert(*x);
            }
            Self::Application(application) => {
                application.variables(vars);
            }
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RcApplication {
    pub(crate) symbol: Perfect<Symbol>,
    pub(crate) args: Box<[RcTerm]>,
}

impl RcApplication {
    fn variables(&self, vars: &mut FnvHashSet<usize>) {
        for arg in &self.args {
            arg.variables(vars);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RcLiteral {
    pub(crate) polarity: bool,
    pub(crate) atom: Rc<RcApplication>,
}

impl RcLiteral {
    pub(crate) fn negated(&self) -> Self {
        Self {
            polarity: !self.polarity,
            atom: self.atom.clone(),
        }
    }

    pub(crate) fn variables(&self, vars: &mut FnvHashSet<usize>) {
        self.atom.variables(vars);
    }
}

#[derive(Debug)]
pub(crate) enum Formula {
    Bool(bool),
    Atom(Rc<RcApplication>),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Forall(usize, Box<Formula>),
    Exists(usize, Box<Formula>),
}

impl Formula {
    pub(crate) fn negated(self) -> Self {
        Self::Not(Box::new(self))
    }
}

#[derive(Debug)]
pub(crate) enum Nnf {
    Literal(RcLiteral),
    And(Vec<Nnf>),
    Or(Vec<Nnf>),
    Forall(usize, Box<Nnf>),
    Exists(usize, Box<Nnf>),
}

impl Nnf {
    pub(crate) fn negated(&self) -> Self {
        match self {
            Self::Literal(lit) => Self::Literal(lit.negated()),
            Self::And(fs) => Self::Or(fs.iter().map(|f| f.negated()).collect()),
            Self::Or(fs) => Self::And(fs.iter().map(|f| f.negated()).collect()),
            Self::Forall(x, f) => Self::Exists(*x, Box::new(f.negated())),
            Self::Exists(x, f) => Self::Exists(*x, Box::new(f.negated())),
        }
    }
}
