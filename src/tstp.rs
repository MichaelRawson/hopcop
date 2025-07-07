use crate::options::Options;
use crate::syntax::{Clause, Source};
use crate::tptp::{SyntaxError, Unsupported};
use std::io::Write;

fn get_problem_name(options: &Options) -> &str {
    options
        .path
        .file_stem()
        .and_then(|name| name.to_str())
        .unwrap_or_default()
}

pub(crate) fn load_error(error: &anyhow::Error) {
    if error.is::<SyntaxError>() {
        println!("% SZS status SyntaxError");
    } else if error.is::<Unsupported>() {
        println!("% SZS status Inappropriate");
    } else if error.is::<std::io::Error>() {
        println!("% SZS status OSError");
    }
}

pub(crate) fn theorem<W: Write>(w: &mut W, options: &Options) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status Theorem for {name}")?;
    Ok(())
}

pub(crate) fn gaveup<W: Write>(w: &mut W, options: &Options) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status GaveUp for {name}")?;
    Ok(())
}

pub(crate) fn timeout<W: Write>(w: &mut W, options: &Options) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status TimeOut for {name}")?;
    Ok(())
}

pub(crate) fn input_clause<W: Write>(w: &mut W, clause: &Clause) -> anyhow::Result<()> {
    let (path, name) = if let Source::Axiom { path, name } = &clause.info.source {
        (path, name)
    } else {
        return Ok(());
    };
    write!(w, "cnf({}, plain, ", clause.info.number,)?;
    let mut first = true;
    for literal in &clause.literals {
        if !first {
            write!(w, " | ")?;
        }
        first = false;
        write!(w, "{literal}")?;
    }
    write!(w, ", inference(cnf, [status(esa)], [")?;
    if clause.info.negated {
        write!(w, "inference(negate_conjecture, [status(cth)], [")?;
    }
    write!(w, "file({path}, {name})")?;
    if clause.info.negated {
        write!(w, "])")?;
    }
    writeln!(w, "])).")?;
    Ok(())
}
