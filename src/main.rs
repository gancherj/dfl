use std::io::BufWriter;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::process::ExitCode;
use std::rc::Rc;
use std::{fs, io::BufReader};

pub mod ast;
pub mod check;
pub mod error;
pub mod execution;
pub mod mc;
pub mod permission;
pub mod riptide;
pub mod smt;
pub mod span;

use crate::error::Error;
use crate::{ast::*, check::PermCheckMode, permission::PermInferOptions, riptide::Graph};

use clap::{command, Parser};
use error::SpannedError;
use execution::Configuration;
use lalrpop_util::lalrpop_mod;
use mc::{ChanEquality, ModelChecker, PredicateX};
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

    /// Run deadlock checker
    #[arg(long, default_value_t = false)]
    check_deadlock: bool,

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
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "z3")]
    solver: String,

    /// Options for the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ')]
    solver_flags: Vec<String>,

    /// Log SMT commands into the given file
    #[arg(long)]
    log_smt: Option<String>,

    /// Log compiled dfl program into the given file
    #[arg(long)]
    log_dfl: Option<String>,
}

impl Args {
    /// Generate a solver instance
    fn gen_solver(&self) -> Result<smt::Solver, Error> {
        let solver_options = SolverOptions {
            log: match &self.log_smt {
                Some(log_path) => Some(BufWriter::new(fs::File::create(log_path)?)),
                None => None,
            },
        };
        Ok(smt::Solver::new(self.solver.clone(), &self.solver_flags, solver_options)?)
    }
}

/// Parse input file (in dfl or o2p), then return the context
fn parse_input(args: &Args) -> Result<(Rc<Ctx>, Vec<ChanEquality>), Error> {
    let path: FilePath = args.source.as_str().into();

    // Equality constraints when compiled from o2p
    let mut chan_eqs = Vec::new();

    match Path::new(path.as_str()).extension().map(|s| s.as_bytes()) {
        // Parse from dfl source
        Some(b"dfl") => {
            let src: Source = fs::read_to_string(path.as_str())?.into();
            let program = syntax::ProgramParser::new()
                .parse(&path, &src, src.as_str())
                .map_err(|e| SpannedError::from_parse_error(&path, &src, e))?;
            Ok((Rc::new(Ctx::from(&program)?), Vec::new()))
        }

        // Translate from RipTide dataflow graph
        Some(b"o2p") => {
            let o2p_file = fs::File::open(path.as_str())?;
            let reader = BufReader::new(o2p_file);
            let graph = Graph::from_reader(reader)?;
            // println!("parsed: {:?}", graph);
            // println!("{}", graph.to_program(32).unwrap());
            let ctx = graph.to_program(&TranslationOptions { word_width: 32 })?;

            // Gather equalities between channels for model checking
            // TODO: tidy this up
            for op in graph.ops.iter() {
                for chans in op.outputs.values() {
                    // All channels connected to the same output port should be equal
                    chan_eqs.push(ChanEquality {
                        chans: chans.iter().map(|c| Graph::channel_name(c)).collect(),
                    });

                    // println!("output equality: {}", chan_eqs.last().unwrap().chans.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(" = "));
                }
            }

            Ok((Rc::new(ctx), chan_eqs))
        }

        _ => Err(format!("unknown extension {}", path))?,
    }
}

/// Run model checker for deadlocks
fn deadlock_check(args: &Args, ctx: &Rc<Ctx>, chan_eqs: Vec<ChanEquality>) -> Result<(), Error> {
    let mut mc = ModelChecker::new(&ctx, [
        // Whether a boolean value is true or false
        // Rc::new(PredicateX { typ: TermTypeX::bool(), var: "x".into(), term: smt::TermX::var("x") }),

        // Whether an integer is 0 or not
        // Rc::new(PredicateX { typ: TermTypeX::int(), var: "x".into(), term: smt::TermX::eq(smt::TermX::var("x"), smt::TermX::int(0)) }),

        // Whether a BV32 is 0
        Rc::new(PredicateX { typ: TermTypeX::bit_vec(32), var: "x".into(), term: smt::TermX::eq(smt::TermX::var("x"), smt::TermX::bit_vec(0, 32)) }),
    ], chan_eqs);

    let mut solver = args.gen_solver()?;
    solver.set_logic("ALL")?;

    for cmd in Configuration::gen_smt_prelude(&ctx)? {
        // println!("{}", cmd);
        solver.send_command(cmd)?;
    }

    mc.compute_reachable_shapes(&mut solver, "Program", 1)?;

    println!("==============================");
    let cycle = mc.find_wait_cycle(&mut solver)?;
    if let Some(cycle) = cycle {
        println!(
            "has wait cycle: {}",
            cycle
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" -> ")
        );
    } else {
        println!("no cycles found");
    }

    Ok(())
}

/// Type check the context
fn type_check(args: &Args, ctx: &Rc<Ctx>) -> Result<(), Error> {
    let mut solver = args.gen_solver()?;
    solver.set_logic("ALL")?;

    ctx.type_check(&mut if args.check_perm {
        PermCheckMode::Check(solver)
    } else if args.infer_perm {
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
    })
}

/// Check the arguments provided and make modifications if necessary
fn check_args(args: &mut Args) -> Result<(), Error> {
    if args.check_perm && args.infer_perm {
        Err("cannot set both --check-perm and --infer-perm".to_string())?;
    }

    // Add additional flags for solvers
    if args.solver == "cvc5" {
        args.solver_flags
            .extend(["--no-interactive", "--incremental"]
                .map(|s| s.to_string()));

        if args.infer_perm {
            // Additional arguments for the SyGuS mode
            args.solver_flags
                .extend(["--lang", "sygus", "--sygus-si", "use"].map(|s| s.to_string()));

            if let Some(size) = args.max_grammar_size {
                args.solver_flags
                    .extend(["--sygus-abort-size".to_string(), size.to_string()]);
            }
        }
    } else if args.solver == "z3" {
        args.solver_flags
            .extend(["-in"]
                .map(|s| s.to_string()));

        assert!(!args.infer_perm, "SyGuS not supported by Z3; use CVC5 instead");
    }

    Ok(())
}

fn main_args(mut args: Args) -> Result<(), Error> {
    check_args(&mut args)?;
    let (ctx, chan_eqs) = parse_input(&args)?;

    if let Some(log_dfl) = &args.log_dfl {
        let program: Program = ctx.as_ref().into();
        fs::write(log_dfl, program.to_string())?;
    }

    type_check(&args, &ctx)?;
    if args.check_deadlock {
        deadlock_check(&args, &ctx, chan_eqs)?;
    }
    Ok(())
}

fn main() -> ExitCode {
    match main_args(Args::parse()) {
        Ok(..) => ExitCode::from(0),
        Err(err) => {
            eprintln!("{}", err);
            ExitCode::from(1)
        }
    }
}
