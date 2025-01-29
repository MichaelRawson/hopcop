use crate::builder::Builder;
use crate::syntax::*;
use fnv::{FnvHashMap, FnvHashSet};
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct PP {
    pub(crate) builder: Builder,
    bound: Vec<RcTerm>,
    subst: FnvHashMap<usize, Rc<RcApplication>>,
    fresh_skolem: usize,
    fresh_definition: usize,
    defs: Vec<Vec<RcLiteral>>,
    rename: FnvHashMap<usize, usize>,
    fresh_rename: usize,
}

pub(crate) fn nnf(polarity: bool, formula: &Formula) -> Nnf {
    match (polarity, formula) {
        (polarity, Formula::Bool(b)) => {
            if *b == polarity {
                Nnf::And(vec![])
            } else {
                Nnf::And(vec![Nnf::Or(vec![])])
            }
        }
        (polarity, Formula::Atom(atom)) => Nnf::Literal(RcLiteral {
            polarity,
            atom: atom.clone(),
        }),
        (polarity, Formula::Not(f)) => nnf(!polarity, f),
        (true, Formula::And(fs)) | (false, Formula::Or(fs)) => {
            Nnf::And(fs.iter().map(|f| nnf(polarity, f)).collect())
        }
        (true, Formula::Or(fs)) | (false, Formula::And(fs)) => {
            Nnf::Or(fs.iter().map(|f| nnf(polarity, f)).collect())
        }
        (polarity, Formula::Iff(l, r)) => {
            let lnnf = nnf(polarity, l);
            let nlnnf = lnnf.negated();
            let rnnf = nnf(true, r);
            let nrnnf = rnnf.negated();
            Nnf::And(vec![Nnf::Or(vec![nlnnf, rnnf]), Nnf::Or(vec![nrnnf, lnnf])])
        }
        (true, Formula::Forall(x, f)) | (false, Formula::Exists(x, f)) => {
            Nnf::Forall(*x, Box::new(nnf(polarity, f)))
        }
        (true, Formula::Exists(x, f)) | (false, Formula::Forall(x, f)) => {
            Nnf::Exists(*x, Box::new(nnf(polarity, f)))
        }
    }
}

impl PP {
    pub(crate) fn process(&mut self, formula: Formula, is_goal: bool, source: Source) {
        self.subst.clear();
        let nnf = nnf(true, &formula);
        self.clausify(nnf, is_goal, &source);
    }

    pub(crate) fn finish(self) -> Matrix {
        self.builder.finish()
    }

    fn clausify(&mut self, nnf: Nnf, is_goal: bool, source: &Source) {
        for mut clause in self.cnf(nnf) {
            self.rename_clause(&mut clause);
            let source = source.clone();
            let info = Info {
                is_goal,
                source,
                number: 0,
            };
            self.builder.rc_clause(clause, info);
        }
        while let Some(mut clause) = self.defs.pop() {
            self.rename_clause(&mut clause);
            let source = source.clone();
            let is_goal = false;
            let info = Info {
                is_goal,
                source,
                number: 0,
            };
            self.builder.rc_clause(clause, info);
        }
    }

    fn cnf(&mut self, formula: Nnf) -> Vec<Vec<RcLiteral>> {
        let clauses = match formula {
            Nnf::Literal(RcLiteral { polarity, atom }) => {
                vec![vec![RcLiteral {
                    polarity,
                    atom: self.substitute_application(&atom),
                }]]
            }
            Nnf::And(fs) => fs.into_iter().flat_map(|f| self.cnf(f)).collect(),
            Nnf::Or(fs) => {
                let mut result = vec![vec![]];
                for f in fs {
                    let mut cnf = self.cnf(f);
                    if result.len() > 1 && cnf.len() > 1 {
                        cnf = self.name(cnf);
                    }
                    result = Self::distribute(result, cnf);
                }
                result
            }
            Nnf::Forall(x, f) => {
                let bound = RcTerm::Variable(x);
                self.bound.push(bound);
                let result = self.cnf(*f);
                self.bound.pop();
                result
            }
            Nnf::Exists(x, f) => {
                let arity = self.bound.len();
                self.fresh_skolem += 1;
                let symbol = self.builder.symbol(Symbol {
                    arity,
                    sort: Sort::Obj,
                    name: Name::Skolem(self.fresh_skolem),
                });
                let skolem = RcApplication {
                    symbol,
                    args: self.bound.clone().into(),
                }
                .into();
                self.subst.insert(x, skolem);
                self.cnf(*f)
            }
        };
        let mut result = vec![];
        'clauses: for mut clause in clauses {
            clause.sort();
            clause.dedup();
            for literal in &clause {
                if literal.atom.symbol.is_equality() {
                    if let [ref x, ref y] = *literal.atom.args {
                        if x == y {
                            continue 'clauses;
                        }
                    }
                }
                for other in &clause {
                    if literal.atom == other.atom && literal.polarity != other.polarity {
                        continue 'clauses;
                    }
                }
            }
            result.push(clause);
        }
        result
    }

    fn name(&mut self, cnf: Vec<Vec<RcLiteral>>) -> Vec<Vec<RcLiteral>> {
        let mut vars = FnvHashSet::default();
        for clause in &cnf {
            for literal in clause {
                literal.variables(&mut vars);
            }
        }
        let symbol = self.builder.symbol(Symbol {
            arity: vars.len(),
            sort: Sort::Bool,
            name: Name::Definition(self.fresh_definition),
        });
        self.fresh_definition += 1;
        let args = vars.into_iter().map(RcTerm::Variable).collect();
        let lit = RcLiteral {
            polarity: true,
            atom: RcApplication { symbol, args }.into(),
        };
        for mut clause in cnf {
            clause.push(lit.negated());
            self.defs.push(clause);
        }
        vec![vec![lit]]
    }

    fn distribute(left: Vec<Vec<RcLiteral>>, right: Vec<Vec<RcLiteral>>) -> Vec<Vec<RcLiteral>> {
        let mut result = vec![];
        for c in &left {
            for d in &right {
                let mut clause = vec![];
                clause.extend(c.iter().cloned());
                clause.extend(d.iter().cloned());
                result.push(clause);
            }
        }
        result
    }

    fn rename_clause(&mut self, clause: &mut Vec<RcLiteral>) {
        self.fresh_rename = 0;
        self.rename.clear();
        for literal in clause {
            literal.atom = self.rename_application(&literal.atom);
        }
    }

    fn rename_application(&mut self, app: &RcApplication) -> Rc<RcApplication> {
        RcApplication {
            symbol: app.symbol,
            args: app.args.iter().map(|t| self.rename_term(t)).collect(),
        }
        .into()
    }

    fn rename_term(&mut self, term: &RcTerm) -> RcTerm {
        match term {
            RcTerm::Variable(x) => {
                let renamed = *self.rename.entry(*x).or_insert_with(|| {
                    let renamed = self.fresh_rename;
                    self.fresh_rename += 1;
                    renamed
                });
                RcTerm::Variable(renamed)
            }
            RcTerm::Application(app) => RcTerm::Application(self.rename_application(app)),
        }
    }

    fn substitute_application(&mut self, app: &RcApplication) -> Rc<RcApplication> {
        RcApplication {
            symbol: app.symbol,
            args: app.args.iter().map(|t| self.substitute_term(t)).collect(),
        }
        .into()
    }

    fn substitute_term(&mut self, term: &RcTerm) -> RcTerm {
        match term {
            RcTerm::Variable(x) => self
                .subst
                .get(x)
                .cloned()
                .map(RcTerm::Application)
                .unwrap_or_else(|| term.clone()),
            RcTerm::Application(app) => RcTerm::Application(self.substitute_application(app)),
        }
    }
}
