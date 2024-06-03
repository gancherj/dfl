use std::io::BufWriter;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::process::ExitCode;
use std::{fs, io::BufReader};

pub mod ast;
pub mod check;
pub mod error;
pub mod permission;
pub mod riptide;
pub mod smt;
pub mod span;

use crate::error::Error;
use crate::{ast::*, check::PermCheckMode, permission::PermInferOptions, riptide::Graph};

use clap::{command, Parser};
use error::SpannedError;
use lalrpop_util::lalrpop_mod;
use riptide::TranslationOptions;
use smt::SolverOptions;
use span::{FilePath, Source};

lalrpop_mod!(pub syntax);

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Source file
    source: String,

    /// Enable permission check
    #[arg(long, default_value_t = false)]
    check_perm: bool,

    /// Enable permission inference
    #[arg(long, default_value_t = false)]
    infer_perm: bool,

    /// Enable array slices for permission inference
    #[arg(long, default_value_t = false)]
    array_slices: bool,

    /// Enable if-then-else for permission inference
    #[arg(long, default_value_t = false)]
    use_ite: bool,

    /// Number of fractions for permission inference
    #[arg(long, default_value_t = 1)]
    num_fractions: usize,

    /// Turn off syntactic restriction when
    /// synthesizing permissions
    #[arg(long, default_value_t = false)]
    no_perm_grammar: bool,

    /// Max grammar size when synthesizing permissions
    #[arg(long)]
    max_grammar_size: Option<u32>,

    /// Path to the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "cvc5")]
    solver: String,

    /// Options for the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "--no-interactive --incremental")]
    solver_flags: Vec<String>,

    /// Log SMT commands into the given file
    #[arg(long)]
    log_smt: Option<String>,
}

fn type_check(mut args: Args) -> Result<(), Error> {
    let path: FilePath = args.source.into();

    let ctx = match Path::new(path.as_str()).extension().map(|s| s.as_bytes()) {
        // Parse from dfl source
        Some(b"dfl") => {
            let src: Source = fs::read_to_string(path.as_str())?.into();
            let program = syntax::ProgramParser::new()
                .parse(&path, &src, src.as_str())
                .map_err(|e| SpannedError::from_parse_error(&path, &src, e))?;
            Ctx::from(&program)?
        }

        // Translate from RipTide dataflow graph
        Some(b"o2p") => {
            let o2p_file = fs::File::open(path.as_str())?;
            let reader = BufReader::new(o2p_file);
            let graph = Graph::from_reader(reader)?;
            println!("parsed: {:?}", graph);
            // println!("{}", graph.to_program(32).unwrap());
            let ctx = graph.to_program(&TranslationOptions { word_width: 32 })?;
            let program: Program = (&ctx).into();

            println!("{}", program);
            ctx
        }

        _ => Err(format!("unknown extension {}", path))?,
    };

    if args.check_perm && args.infer_perm {
        Err("cannot set both --check-perm and --infer-perm".to_string())?;
    }

    let solver_options = SolverOptions {
        log: match args.log_smt {
            Some(log_path) => Some(BufWriter::new(fs::File::create(log_path)?)),
            None => None,
        },
    };

    ctx.type_check(&mut if args.check_perm {
        let mut solver = smt::Solver::new(args.solver, &args.solver_flags, solver_options)?;
        solver.set_logic("ALL")?;
        PermCheckMode::Check(solver)
    } else if args.infer_perm {
        if args.solver == "cvc5" {
            args.solver_flags
                .extend(["--lang", "sygus", "--sygus-si", "use"].map(|s| s.to_string()));

            if let Some(size) = args.max_grammar_size {
                args.solver_flags
                    .extend(["--sygus-abort-size".to_string(), size.to_string()]);
            }
        }

        let mut solver = smt::Solver::new(args.solver, &args.solver_flags, solver_options)?;
        solver.set_logic("ALL")?;
        PermCheckMode::Infer(
            solver,
            PermInferOptions {
                array_slices: args.array_slices,
                use_ite: args.use_ite,
                num_fractions: args.num_fractions,
                perm_grammar: !args.no_perm_grammar,
            },
        )
    } else {
        PermCheckMode::None
    })?;

    Ok(())
}

fn main() -> ExitCode {
    match type_check(Args::parse()) {
        Ok(..) => ExitCode::from(0),
        Err(err) => {
            eprintln!("{}", err);
            ExitCode::from(1)
        }
    }
}
