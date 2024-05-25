use std::fs;

pub mod ast;
pub mod check;
pub mod permission;
pub mod smt;
pub mod span;

use crate::{ast::*, check::PermCheckMode};

use clap::{command, Parser};
use lalrpop_util::{lalrpop_mod, ParseError};

lalrpop_mod!(pub dfl);

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

    /// Path to the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "z3")]
    solver: String,

    /// Options for the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "-in")]
    solver_opts: Vec<String>,
}

fn get_line_col_num(src: &str, offset: usize) -> Option<(usize, usize)> {
    if offset > src.len() {
        return None;
    }

    let mut line = 1;
    let mut col = 1;

    for (idx, ch) in src.char_indices() {
        if idx == offset {
            return Some((line, col));
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }

    if offset == src.len() {
        Some((line, col))
    } else {
        None
    }
}

fn main() {
    // let mut solver = smt::Solver::new("z3", &["-in"]).expect("failed to create solver");

    // solver.send_command(smt::CommandX::declare_const("a", smt::Sort::Int))
    //     .expect("failed to send command");

    // solver.send_command(smt::CommandX::assert(smt::TermX::lt(
    //     smt::TermX::var("a"),
    //     smt::TermX::int(0),
    // ))).unwrap();

    // solver.send_command(smt::CommandX::assert(smt::TermX::lt(
    //     smt::TermX::int(0),
    //     smt::TermX::var("a"),
    // ))).unwrap();

    // println!("check-sat result: {}", solver.check_sat().unwrap());

    // let result = solver.send_command_with_output(smt::CommandX::get_model())
    //     .expect("failed to send command");

    // println!("get-model result: {}", result);

    // solver.close().unwrap();

    let args = Args::parse();

    let path = &args.source;
    let src = fs::read_to_string(path).expect("failed to read input file");
    let parsed = dfl::ProgramParser::new().parse(&src);

    match parsed {
        Ok(program) => {
            let ctx = Ctx::from(&program).unwrap();
            // println!("{:?}", ctx);

            assert!(!(args.check_perm && args.infer_perm));

            let mut mode = if args.check_perm {
                PermCheckMode::Check(smt::Solver::new(args.solver, &args.solver_opts).expect("failed to create solver"))
            } else if args.infer_perm {
                let mut solver = smt::Solver::new(args.solver, &args.solver_opts).expect("failed to create solver");
                solver.set_logic("LIA").expect("failed to set logic");
                PermCheckMode::Infer(solver)
            } else {
                PermCheckMode::None
            };
            
            match ctx.type_check(&mut mode) {
                Ok(()) => {},
                Err(err) => {
                    let loc = match err.span {
                        Some(span) => {
                            let (line, col) = get_line_col_num(&src, span.start).unwrap();
                            format!("{}:{}:{}", path, line, col)
                        }
                        None => format!("{}", path)
                    };
                    println!("typing error: {}: {}", loc, err.msg);
                },
            }
        }
        Err(e) => {
            let msg = match e {
                ParseError::InvalidToken { location } => {
                    let (line, col) = get_line_col_num(&src, location).unwrap();
                    format!("invalid token at {}:{}:{}", path, line, col)
                }
                ParseError::UnrecognizedEof { location, .. } => {
                    let (line, col) = get_line_col_num(&src, location).unwrap();
                    format!("unexpected eof at {}:{}:{}", path, line, col)
                }
                ParseError::UnrecognizedToken { token: (start, token, _), .. } => {
                    let (line, col) = get_line_col_num(&src, start).unwrap();
                    format!("unexpected token {} at {}:{}:{}", token, path, line, col)
                }
                ParseError::ExtraToken { token: (start, token, _) } => {
                    let (line, col) = get_line_col_num(&src, start).unwrap();
                    format!("extra token {} at {}:{}:{}", token, path, line, col)
                }
                ParseError::User { error } => error.to_string(),
            };

            println!("parsing error: {}", msg);
        }
    }
}
