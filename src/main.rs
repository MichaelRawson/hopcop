mod builder;
mod options;
mod pp;
mod syntax;
mod tptp;
mod tstp;
mod util;

use crate::options::Options;
use anyhow::Context;
use std::io::stdout;
use std::time::{Duration, Instant};

const STACK: usize = 0x1000000;

fn report_err<T>(err: anyhow::Error) -> T {
    eprintln!("satcop: {:?}", err.context("fatal error, exiting"));
    std::process::exit(1);
}

/*
fn go(matrix: Arc<Matrix>, options: Arc<Options>) {
    let mut search = Search::default();
    //search.seed(index as u64);
    search.go(&matrix);

    let stdout = stdout();
    let mut lock = stdout.lock();
    if options.statistics {
        statistics::print(&mut lock)
            .context("printing statistics")
            .unwrap_or_else(report_err);
    }
    search
        .print_proof(&mut lock, &options, &matrix)
        .context("printing proof")
        .unwrap_or_else(report_err);
    std::process::exit(0);
}
*/

fn main() {
    let start = Instant::now();
    let options = Options::new();
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
        tstp::gaveup(&mut lock, &options)
            .context("printing gaveup")
            .unwrap_or_else(report_err);
        return;
    }

    /*
    let thread_options = options.clone();
    std::thread::Builder::new()
        .stack_size(STACK)
        .name("satcop".to_string())
        .spawn(move || go(matrix, thread_options))
        .context("spawning thread")
        .unwrap_or_else(report_err);
    */

    if let Some(limit) = options.time {
        let assigned = Duration::new(limit, 0);
        let elapsed = start.elapsed();
        if let Some(remaining) = assigned.checked_sub(elapsed) {
            std::thread::sleep(remaining);
        }
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::timeout(&mut lock, &options)
            .context("printing timeout")
            .unwrap_or_else(report_err);
        std::process::exit(0);
    } else {
        loop {
            std::thread::sleep(Duration::new(u64::MAX, 0));
        }
    }
}
