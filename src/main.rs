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

// fn dfs(config: &Configuration) -> Result<(), Error> {
//     for branch in config.step_one_proc()? {
//         println!("stepped: {}", branch);
//         match branch {
//             execution::StepResult::Step(_, config) => dfs(&config)?,
//             _ => {}
//         }
//     }
//     Ok(())
// }

fn type_check(mut args: Args) -> Result<(), Error> {
    let path: FilePath = args.source.into();

    // Equality constraints when compiled from o2p
    let mut chan_eqs = Vec::new();

    let ctx = match Path::new(path.as_str()).extension().map(|s| s.as_bytes()) {
        // Parse from dfl source
        Some(b"dfl") => {
            let src: Source = fs::read_to_string(path.as_str())?.into();
            let program = syntax::ProgramParser::new()
                .parse(&path, &src, src.as_str())
                .map_err(|e| SpannedError::from_parse_error(&path, &src, e))?;
            Rc::new(Ctx::from(&program)?)
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

            // Gather equalities between channels for model checking
            // TODO: tidy this up
            for op in graph.ops.iter() {
                for chans in op.outputs.values() {
                    // All channels connected to the same output port should be equal
                    chan_eqs.push(ChanEquality {
                        chans: chans.iter().map(|c| Graph::channel_name(c)).collect(),
                    });

                    println!("output equality: {}", chan_eqs.last().unwrap().chans.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(" = "));
                }
            }

            Rc::new(ctx)
        }

        _ => Err(format!("unknown extension {}", path))?,
    };

    {
        // TODO: test code for symbolic execution
        // let mut smt_ctx = EncodingCtx::new("exec");
        // let config = Configuration::new(&mut smt_ctx, &ctx, "Program".to_string(), 1)?;
        // println!("init config: {}", config);
        // dfs(&config);
        let solver_options = SolverOptions {
            log: match &args.log_smt {
                Some(log_path) => Some(BufWriter::new(fs::File::create(log_path)?)),
                None => None,
            },
        };
        let mut mc = ModelChecker::new(&ctx, [
            // Whether a boolean value is true or false
            // Rc::new(PredicateX { typ: TermTypeX::bool(), var: "x".into(), term: smt::TermX::var("x") }),

            // Whether an integer is 0 or not
            // Rc::new(PredicateX { typ: TermTypeX::int(), var: "x".into(), term: smt::TermX::eq(smt::TermX::var("x"), smt::TermX::int(0)) }),

            // Whether a BV32 is 0
            Rc::new(PredicateX { typ: TermTypeX::bit_vec(32), var: "x".into(), term: smt::TermX::eq(smt::TermX::var("x"), smt::TermX::bit_vec(0, 32)) }),
        ], chan_eqs);
        let mut solver = smt::Solver::new(args.solver.clone(), &args.solver_flags, solver_options)?;
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

        return Ok(());
    }

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
