use clap::Parser;
use std::path::PathBuf;

#[derive(Parser)]
#[command(version, about)]
/*
#[clap(
    name = "HopCoP",
    about = env!("CARGO_PKG_DESCRIPTION"),
    version = 
    author = env!("CARGO_PKG_AUTHORS")
)]
*/
pub(crate) struct Options {
    /// path to input problem
    pub(crate) path: PathBuf,

    #[arg(long)]
    /// Print normal form and exit
    pub(crate) clausify: bool,

    #[arg(long)]
    /// Print search statistics
    pub(crate) statistics: bool,

    #[arg(long)]
    /// Do not print proof
    pub(crate) quiet: bool,

    #[arg(long)]
    /// Enforce time limit (secs)
    pub(crate) time: Option<u64>,
}

impl Options {
    pub(crate) fn new() -> Self {
        Self::parse()
    }
}
