use crate::pp::PP;
use crate::syntax::{self, RcApplication, RcTerm, Sort};
use anyhow::Context;
use fnv::FnvHashSet;
use std::error::Error;
use std::io::Read;
use std::path::Path;
use std::sync::Arc;
use std::{env, fmt, fs, path};
use tptp::cnf::*;
use tptp::common::*;
use tptp::fof::*;
use tptp::top::*;
use tptp::{TPTPIterator, cnf, common, fof};

#[derive(Debug)]
pub(crate) struct SyntaxError(String);

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: syntax error", self.0)
    }
}

impl Error for SyntaxError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[derive(Debug)]
pub(crate) struct Unsupported(String);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unsupported item: {}", self.0)
    }
}

impl Error for Unsupported {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

fn open_path_no_parent(path: &path::Path) -> anyhow::Result<fs::File> {
    let directory = env::var("TPTP_DIR")
        .map(path::PathBuf::from)
        .or_else(|_| env::current_dir())?;
    let path = directory.join(path);
    fs::File::open(&path)
        .map_err(anyhow::Error::from)
        .with_context(|| format!("opening '{}'...", path.display()))
}

fn open_path_with_parent(parent: &path::Path, path: &path::Path) -> anyhow::Result<fs::File> {
    fs::File::open(parent.join(path)).map_err(anyhow::Error::from)
}

fn open_path(parent: Option<&path::Path>, path: &path::Path) -> anyhow::Result<fs::File> {
    if let Some(parent) = parent {
        open_path_with_parent(parent, path)
            .or_else(|_| open_path_no_parent(path))
            .with_context(|| format!("failed relative include '{}'", parent.join(path).display()))
    } else {
        open_path_no_parent(path)
    }
}

#[derive(Default)]
struct Loader {
    pp: PP,
    fresh: usize,
    // TODO use hashmap as well
    free: Vec<(String, usize)>,
    bound: Vec<(String, usize)>,
    strings: FnvHashSet<&'static str>,
}

impl Loader {
    pub(crate) fn finish(self) -> syntax::Matrix {
        self.pp.finish()
    }

    fn intern(&mut self, str: &str) -> &'static str {
        if let Some(already) = self.strings.get(str) {
            already
        } else {
            let str = Box::leak(str.to_string().into_boxed_str());
            self.strings.insert(str);
            str
        }
    }

    fn defined_term(&mut self, term: common::DefinedTerm, sort: Sort) -> RcApplication {
        let name = match term {
            common::DefinedTerm::Number(number) => syntax::Name::Number(match number {
                Number::Integer(Integer(n)) => self.intern(n),
                Number::Rational(Rational(r)) => self.intern(r),
                Number::Real(Real(r)) => self.intern(r),
            }),
            common::DefinedTerm::Distinct(DistinctObject(distinct)) => {
                syntax::Name::Distinct(self.intern(distinct))
            }
        };
        let symbol = self.pp.builder.symbol(syntax::Symbol {
            arity: 0,
            sort,
            name,
        });
        RcApplication {
            symbol,
            args: vec![].into(),
        }
    }

    fn fof_plain_term(&mut self, term: PlainTerm, sort: Sort) -> anyhow::Result<RcApplication> {
        let (symbol, args) = match term {
            PlainTerm::Constant(c) => (c.0.0, vec![]),
            PlainTerm::Function(f, args) => (f.0, args.0),
        };
        let name = match symbol {
            AtomicWord::Lower(LowerWord(w)) => syntax::Name::Atom(self.intern(w)),
            AtomicWord::SingleQuoted(SingleQuoted(q)) => syntax::Name::Quoted(self.intern(q)),
        };
        let symbol = self.pp.builder.symbol(syntax::Symbol {
            arity: args.len(),
            sort,
            name,
        });
        let args = args
            .into_iter()
            .map(|t| self.fof_term(t, Sort::Obj))
            .collect::<anyhow::Result<_>>()?;
        Ok(RcApplication { symbol, args })
    }

    fn fof_defined_term(
        &mut self,
        term: fof::DefinedTerm,
        sort: Sort,
    ) -> anyhow::Result<RcApplication> {
        match term {
            fof::DefinedTerm::Defined(defined) => Ok(self.defined_term(defined, sort)),
            fof::DefinedTerm::Atomic(atomic) => Err(Unsupported(atomic.to_string()).into()),
        }
    }

    fn fof_function_term(
        &mut self,
        term: FunctionTerm,
        sort: Sort,
    ) -> anyhow::Result<RcApplication> {
        match term {
            FunctionTerm::Plain(term) => self.fof_plain_term(term, sort),
            FunctionTerm::Defined(def) => self.fof_defined_term(def, sort),
            FunctionTerm::System(system) => Err(Unsupported(system.to_string()).into()),
        }
    }

    fn fof_term(&mut self, term: Term, sort: Sort) -> anyhow::Result<RcTerm> {
        Ok(match term {
            Term::Function(term) => {
                RcTerm::Application(self.fof_function_term(*term, sort)?.into())
            }
            Term::Variable(x) => {
                let name = x.0.0;
                let var = if let Some((_, var)) =
                    self.bound.iter().rev().find(|(bound, _)| bound == name)
                {
                    *var
                } else if let Some((_, var)) = self.free.iter().find(|(free, _)| free == name) {
                    *var
                } else {
                    let var = self.fresh;
                    self.fresh += 1;
                    self.free.push((name.to_string(), var));
                    var
                };
                RcTerm::Variable(var)
            }
        })
    }

    fn fof_defined_plain_formula(
        &mut self,
        atom: DefinedPlainFormula,
    ) -> anyhow::Result<syntax::Formula> {
        match atom.0 {
            DefinedPlainTerm::Constant(c) => match c.0.0.0.0.0 {
                "true" => Ok(syntax::Formula::Bool(true)),
                "false" => Ok(syntax::Formula::Bool(false)),
                _ => Err(Unsupported(c.to_string()).into()),
            },
            f @ DefinedPlainTerm::Function(_, _) => Err(Unsupported(f.to_string()).into()),
        }
    }

    fn fof_defined_atomic_formula(
        &mut self,
        atom: DefinedAtomicFormula,
    ) -> anyhow::Result<syntax::Formula> {
        Ok(match atom {
            DefinedAtomicFormula::Plain(plain) => self.fof_defined_plain_formula(plain)?,
            DefinedAtomicFormula::Infix(infix) => syntax::Formula::Atom(
                RcApplication {
                    symbol: self.pp.builder.equality_symbol(),
                    args: vec![
                        self.fof_term(*infix.left, syntax::Sort::Obj)?,
                        self.fof_term(*infix.right, syntax::Sort::Obj)?,
                    ]
                    .into(),
                }
                .into(),
            ),
        })
    }

    fn fof_atomic_formula(&mut self, atom: AtomicFormula) -> anyhow::Result<syntax::Formula> {
        match atom {
            AtomicFormula::Plain(plain) => Ok(syntax::Formula::Atom(
                self.fof_plain_term(plain.0, Sort::Bool)?.into(),
            )),
            AtomicFormula::Defined(defined) => Ok(self.fof_defined_atomic_formula(defined)?),
            AtomicFormula::System(system) => Err(Unsupported(system.to_string()).into()),
        }
    }

    fn fof_infix_unary(&mut self, infix: InfixUnary) -> anyhow::Result<syntax::Formula> {
        Ok(syntax::Formula::Atom(
            RcApplication {
                symbol: self.pp.builder.equality_symbol(),
                args: vec![
                    self.fof_term(*infix.left, syntax::Sort::Obj)?,
                    self.fof_term(*infix.right, syntax::Sort::Obj)?,
                ]
                .into(),
            }
            .into(),
        )
        .negated())
    }

    fn fof_unit_formula(&mut self, fof: UnitFormula) -> anyhow::Result<syntax::Formula> {
        match fof {
            UnitFormula::Unitary(f) => self.fof_unitary_formula(f),
            UnitFormula::Unary(f) => self.fof_unary_formula(f),
        }
    }

    fn fof_binary_assoc(&mut self, fof: BinaryAssoc) -> anyhow::Result<syntax::Formula> {
        Ok(match fof {
            BinaryAssoc::And(fs) => syntax::Formula::And(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(f))
                    .collect::<anyhow::Result<_>>()?,
            ),
            BinaryAssoc::Or(fs) => syntax::Formula::Or(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(f))
                    .collect::<anyhow::Result<_>>()?,
            ),
        })
    }

    fn fof_binary_nonassoc(&mut self, fof: BinaryNonassoc) -> anyhow::Result<syntax::Formula> {
        let left = self.fof_unit_formula(*fof.left)?;
        let right = self.fof_unit_formula(*fof.right)?;
        use NonassocConnective as NC;
        Ok(match fof.op {
            NC::LRImplies => syntax::Formula::Or(vec![left.negated(), right]),
            NC::RLImplies => syntax::Formula::Or(vec![left, right.negated()]),
            NC::Equivalent => syntax::Formula::Iff(Box::new(left), Box::new(right)),
            NC::NotEquivalent => syntax::Formula::Iff(Box::new(left), Box::new(right)).negated(),
            NC::NotAnd => syntax::Formula::And(vec![left, right]).negated(),
            NC::NotOr => syntax::Formula::Or(vec![left, right]).negated(),
        })
    }

    fn fof_binary_formula(&mut self, fof: BinaryFormula) -> anyhow::Result<syntax::Formula> {
        match fof {
            BinaryFormula::Assoc(f) => self.fof_binary_assoc(f),
            BinaryFormula::Nonassoc(f) => self.fof_binary_nonassoc(f),
        }
    }

    fn fof_quantified_formula(
        &mut self,
        fof: QuantifiedFormula,
    ) -> anyhow::Result<syntax::Formula> {
        let num_bound = fof.bound.0.len();
        for x in fof.bound.0.into_iter() {
            let string = x.0.0.to_string();
            let var = self.fresh;
            self.fresh += 1;
            self.bound.push((string, var));
        }
        let mut f = self.fof_unit_formula(*fof.formula)?;
        for _ in 0..num_bound {
            let (_, var) = self.bound.pop().expect("bound this earlier");
            f = match fof.quantifier {
                Quantifier::Forall => syntax::Formula::Forall(var, Box::new(f)),
                Quantifier::Exists => syntax::Formula::Exists(var, Box::new(f)),
            };
        }
        Ok(f)
    }

    fn fof_unitary_formula(&mut self, fof: UnitaryFormula) -> anyhow::Result<syntax::Formula> {
        Ok(match fof {
            UnitaryFormula::Quantified(f) => self.fof_quantified_formula(f)?,
            UnitaryFormula::Atomic(f) => self.fof_atomic_formula(*f)?,
            UnitaryFormula::Parenthesised(f) => self.fof_logic_formula(*f)?,
        })
    }

    fn fof_unary_formula(&mut self, fof: UnaryFormula) -> anyhow::Result<syntax::Formula> {
        Ok(match fof {
            UnaryFormula::Unary(_, f) => self.fof_unit_formula(*f)?.negated(),
            UnaryFormula::InfixUnary(f) => self.fof_infix_unary(f)?,
        })
    }

    fn fof_logic_formula(&mut self, fof: LogicFormula) -> anyhow::Result<syntax::Formula> {
        match fof {
            LogicFormula::Binary(f) => self.fof_binary_formula(f),
            LogicFormula::Unary(f) => self.fof_unary_formula(f),
            LogicFormula::Unitary(f) => self.fof_unitary_formula(f),
        }
    }

    fn fof_formula(&mut self, fof: fof::Formula) -> anyhow::Result<syntax::Formula> {
        self.fof_logic_formula(fof.0)
    }

    fn literal(&mut self, lit: Literal) -> anyhow::Result<syntax::Formula> {
        Ok(match lit {
            Literal::Atomic(atomic) => self.fof_atomic_formula(atomic)?,
            Literal::NegatedAtomic(atomic) => self.fof_atomic_formula(atomic)?.negated(),
            Literal::Infix(infix) => self.fof_infix_unary(infix)?,
        })
    }

    fn cnf_formula(&mut self, cnf: cnf::Formula) -> anyhow::Result<syntax::Formula> {
        let disjunction = match cnf {
            cnf::Formula::Disjunction(d) => d,
            cnf::Formula::Parenthesised(d) => d,
        };
        Ok(syntax::Formula::Or(
            disjunction
                .0
                .into_iter()
                .map(|lit| self.literal(lit))
                .collect::<anyhow::Result<_>>()?,
        ))
    }

    fn annotated<D: Dialect + fmt::Display>(
        &mut self,
        selection: Option<&FnvHashSet<Name>>,
        path: Arc<String>,
        annotated: Annotated<D>,
        original: Option<Arc<String>>,
    ) -> anyhow::Result<()> {
        if selection
            .map(|selection| !selection.contains(&annotated.name))
            .unwrap_or_default()
        {
            return Ok(());
        }

        let role = (annotated.role.0).0;
        let negate = role == "conjecture";
        let is_goal = negate || role == "negated_conjecture";
        let source = syntax::Source::Axiom {
            path,
            name: format!("{}", &annotated.name).into(),
            original,
        };

        self.fresh = 0;
        self.free.clear();
        let mut formula = annotated.formula.load(self)?;
        if negate {
            formula = formula.negated();
        }
        if is_goal {
            self.pp.builder.notify_have_conjecture();
        }
        self.pp.process(formula, negate, is_goal, source);
        Ok(())
    }

    fn load(
        &mut self,
        parent: Option<&path::Path>,
        selection: Option<FnvHashSet<Name>>,
        path: &path::Path,
    ) -> anyhow::Result<()> {
        let display_path = Arc::new(format!("'{}'", path.display()));
        let mut bytes = vec![];
        open_path(parent, path)?.read_to_end(&mut bytes)?;
        for statement in TPTPIterator::<()>::new(&bytes) {
            let statement = statement.map_err(|_| SyntaxError(path.display().to_string()))?;
            match statement {
                TPTPInput::Annotated(annotated) => match *annotated {
                    AnnotatedFormula::Tfx(_) => {
                        return Err(Unsupported(annotated.to_string()).into());
                    }
                    AnnotatedFormula::Fof(fof) => {
                        let original = format!("{}", fof.0.formula).into();
                        self.annotated(
                            selection.as_ref(),
                            display_path.clone(),
                            fof.0,
                            Some(original),
                        )?;
                    }
                    AnnotatedFormula::Cnf(cnf) => {
                        self.annotated(selection.as_ref(), display_path.clone(), cnf.0, None)?;
                    }
                },
                TPTPInput::Include(include) => {
                    let Include {
                        file_name,
                        selection,
                    } = *include;
                    let included = path::Path::new((file_name.0).0);
                    let selection: Option<FnvHashSet<_>> =
                        selection.0.map(|list| list.0.into_iter().collect());
                    self.load(path.parent(), selection, included)
                        .with_context(|| format!("included '{}'", included.display(),))?;
                }
            }
        }
        Ok(())
    }
}

trait Dialect {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Formula>;
}

impl Dialect for fof::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Formula> {
        loader.fof_formula(self)
    }
}

impl Dialect for cnf::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Formula> {
        loader.cnf_formula(self)
    }
}

pub(crate) fn load(path: &Path) -> anyhow::Result<syntax::Matrix> {
    let mut loader = Loader::default();
    loader
        .load(None, None, path)
        .with_context(|| format!("failed to load from '{}'", path.display()))?;
    Ok(loader.finish())
}
