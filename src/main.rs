mod builder;
mod options;
mod pp;
mod search;
mod subst;
mod syntax;
mod tptp;
mod tstp;
mod util;

use crate::options::Options;
use anyhow::Context;
use search::Search;
use std::io::stdout;
use std::sync::Arc;
use std::time::{Duration, Instant};

const STACK: usize = 0x1000000;

fn report_err<T>(err: anyhow::Error) -> T {
    eprintln!("hopcop: {:?}", err.context("fatal error, exiting"));
    std::process::exit(1);
}

fn start(options: &Options) {
    let matrix = tptp::load(&options.path).unwrap_or_else(|err| {
        tstp::load_error(&err);
        report_err(err)
    });
    if options.clausify {
        for clause in &matrix.clauses {
            println!("{}", clause);
        }
        return;
    }
    if matrix.start.is_empty() {
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::gaveup(&mut lock, options)
            .context("giving up")
            .unwrap_or_else(report_err);
    }

    let mut search = Search::new(&matrix);
    loop {
        search.expand_or_backtrack();
    }
    search.graphviz();
    std::process::exit(0);
}

fn main() {
    let start_time = Instant::now();
    let options = Arc::new(Options::new());

    let thread_options = options.clone();
    let thread = std::thread::Builder::new()
        .stack_size(STACK)
        .name("hopcop".to_string())
        .spawn(move || start(&thread_options))
        .context("spawning thread with large stack")
        .unwrap_or_else(report_err);

    if let Some(time_limit) = options.time {
        let assigned = Duration::new(time_limit, 0);
        let elapsed = start_time.elapsed();
        if let Some(remaining) = assigned.checked_sub(elapsed) {
            std::thread::sleep(remaining);
        }
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::timeout(&mut lock, &options)
            .context("reporting timeout")
            .unwrap_or_else(report_err);
        std::process::exit(0);
    } else {
        let _ = thread.join();
    }
}
