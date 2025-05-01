use crate::subst::{ROOT, Substitution};
use crate::syntax::*;
use crate::util::Perfect;
use fnv::FnvHashSet;

#[derive(Default)]
pub(crate) struct Builder {
    matrix: Matrix,
    symbols: FnvHashSet<&'static Symbol>,
    applications: FnvHashSet<&'static Application>,
    goals: Vec<&'static Clause>,
    positives: Vec<&'static Clause>,
    equality: Option<Perfect<Symbol>>,
    has_non_goal: bool,
    subst: Substitution,
}

impl Builder {
    pub(crate) fn notify_have_conjecture(&mut self) {
        self.matrix.have_conjecture = true;
    }

    pub(crate) fn symbol(&mut self, symbol: Symbol) -> Perfect<Symbol> {
        if let Some(already) = self.symbols.get(&symbol) {
            Perfect(already)
        } else {
            let symbol = Box::leak(Box::new(symbol));
            self.symbols.insert(symbol);
            Perfect(symbol)
        }
    }

    pub(crate) fn application(&mut self, app: Application) -> Perfect<Application> {
        if let Some(already) = self.applications.get(&app) {
            Perfect(already)
        } else {
            let app = Box::leak(Box::new(app));
            self.applications.insert(app);
            Perfect(app)
        }
    }

    pub(crate) fn finish(mut self) -> Matrix {
        self.add_equality_axioms();
        if self.goals.is_empty() || !self.has_non_goal {
            self.matrix.start = self.positives;
        } else {
            self.matrix.start = self.goals;
        }
        self.matrix
    }

    pub(crate) fn rc_clause(&mut self, literals: Vec<RcLiteral>, info: Info) {
        let literals = literals.iter().map(|l| self.rc_literal(l)).collect();
        self.clause(literals, info);
    }

    fn clause(&mut self, literals: Vec<Literal>, mut info: Info) {
        let positive = literals.iter().all(|lit| lit.polarity);
        info.number = self.matrix.clauses.len();

        let mut disequations = vec![];
        for i in 0..literals.len() {
            let l = &literals[i];
            for k in literals.iter().skip(i + 1) {
                if l.polarity != k.polarity && l.atom.symbol == k.atom.symbol {
                    let disequation = Disequation {
                        left: Term::App(l.atom),
                        right: Term::App(k.atom),
                    };
                    self.subst.clear();
                    if self.subst.unify(
                        ROOT.locate(disequation.left),
                        ROOT.locate(disequation.right),
                    ) {
                        disequations.push(disequation)
                    }
                }
            }
        }
        let clause = Box::leak(Box::new(Clause {
            literals,
            disequations,
            info,
        }));
        self.matrix.clauses.push(clause);
        if positive {
            self.positives.push(clause);
        }
        if clause.info.is_goal {
            self.goals.push(clause);
        } else {
            self.has_non_goal = true;
        }
        for (index, literal) in clause.literals.iter().enumerate() {
            self.matrix
                .index
                .entry((literal.polarity, literal.atom.symbol))
                .or_default()
                .push(Extension { clause, index });
        }
    }

    pub(crate) fn equality_symbol(&mut self) -> Perfect<Symbol> {
        if let Some(eq) = self.equality {
            return eq;
        }
        let symbol = Perfect::new(Symbol {
            arity: 2,
            sort: Sort::Bool,
            name: Name::Equality,
        });
        self.equality = Some(symbol);
        symbol
    }

    fn add_equality_axioms(&mut self) {
        let eq = if let Some(eq) = self.equality {
            eq
        } else {
            return;
        };
        let info = Info {
            is_goal: false,
            source: Source::Equality,
            number: self.matrix.clauses.len(),
        };
        let symbols = std::mem::take(&mut self.symbols);
        for symbol in symbols.into_iter().map(Perfect) {
            if symbol.arity == 0 || !symbol.name.needs_congruence() {
                continue;
            }
            let mut clause = vec![];
            let mut args1 = vec![];
            let mut args2 = vec![];
            for i in 0..symbol.arity {
                let x = Term::Var(2 * i);
                let y = Term::Var(2 * i + 1);
                clause.push(Literal {
                    polarity: false,
                    atom: self.equality(eq, x, y),
                });
                args1.push(x);
                args2.push(y);
            }
            let t1 = self.application(Application {
                symbol,
                args: args1.into(),
            });
            let t2 = self.application(Application {
                symbol,
                args: args2.into(),
            });
            match symbol.sort {
                Sort::Obj => {
                    clause.push(Literal {
                        polarity: true,
                        atom: self.equality(eq, Term::App(t1), Term::App(t2)),
                    });
                }
                Sort::Bool => {
                    clause.push(Literal {
                        polarity: false,
                        atom: t1,
                    });
                    clause.push(Literal {
                        polarity: true,
                        atom: t2,
                    });
                }
            }
            self.clause(clause, info.clone());
        }

        let x = Term::Var(0);
        let y = Term::Var(1);
        let z = Term::Var(2);
        let xx = self.equality(eq, x, x);
        let xy = self.equality(eq, x, y);
        let yx = self.equality(eq, y, x);
        let xz = self.equality(eq, x, z);
        let yz = self.equality(eq, y, z);
        self.clause(
            vec![Literal {
                polarity: true,
                atom: xx,
            }],
            info.clone(),
        );
        self.clause(
            vec![
                Literal {
                    polarity: false,
                    atom: xy,
                },
                Literal {
                    polarity: true,
                    atom: yx,
                },
            ],
            info.clone(),
        );
        self.clause(
            vec![
                Literal {
                    polarity: false,
                    atom: xy,
                },
                Literal {
                    polarity: false,
                    atom: yz,
                },
                Literal {
                    polarity: true,
                    atom: xz,
                },
            ],
            info,
        );
    }

    fn equality(&mut self, eq: Perfect<Symbol>, left: Term, right: Term) -> Perfect<Application> {
        self.application(Application {
            symbol: eq,
            args: vec![left, right].into(),
        })
    }

    fn rc_literal(&mut self, literal: &RcLiteral) -> Literal {
        Literal {
            polarity: literal.polarity,
            atom: self.rc_application(&literal.atom),
        }
    }

    fn rc_application(&mut self, app: &RcApplication) -> Perfect<Application> {
        let app = Application {
            symbol: app.symbol,
            args: app.args.iter().map(|t| self.rc_term(t)).collect(),
        };
        self.application(app)
    }

    fn rc_term(&mut self, term: &RcTerm) -> Term {
        match term {
            RcTerm::Variable(x) => Term::Var(*x),
            RcTerm::Application(app) => Term::App(self.rc_application(app)),
        }
    }
}
