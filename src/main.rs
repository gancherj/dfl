use std::{fs, io::BufReader};

pub mod ast;
pub mod check;
pub mod permission;
pub mod smt;
pub mod span;
pub mod riptide;

use crate::{ast::*, check::PermCheckMode, permission::PermInferOptions, riptide::Graph};

use clap::{command, Parser};
use lalrpop_util::{lalrpop_mod, ParseError};

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

    /// Path to the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "cvc5")]
    solver: String,

    /// Options for the SMT solver
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "--no-interactive --incremental")]
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
    // let o2p_file = fs::File::open("/Users/zhengyao/work/riptide-verification/examples/test-1/test-1.o2p").unwrap();
    // let reader = BufReader::new(o2p_file);
    // let graph = Graph::from_reader(reader).unwrap();
    // println!("parsed: {:?}", graph);
    // println!("{}", graph.to_program(32).unwrap());
    
    let mut args = Args::parse();

    let path = &args.source;
    let src = fs::read_to_string(path).expect("failed to read input file");
    let parsed = syntax::ProgramParser::new().parse(&src);

    match parsed {
        Ok(program) => {
            let ctx = Ctx::from(&program).unwrap();

            assert!(!(args.check_perm && args.infer_perm));

            let mut mode =
                if args.check_perm {
                    let mut solver = smt::Solver::new(args.solver, &args.solver_opts)
                        .expect("failed to create solver");
                    solver.set_logic("ALL").expect("failed to set logic");
                    PermCheckMode::Check(solver)
                } else if args.infer_perm {
                    if args.solver == "cvc5" {
                        args.solver_opts.extend(["--lang", "sygus", "--sygus-si", "use"].map(|s| s.to_string()));
                    }

                    let mut solver = smt::Solver::new(args.solver, &args.solver_opts)
                        .expect("failed to create solver");
                    solver.set_logic("ALL").expect("failed to set logic");
                    PermCheckMode::Infer(
                        solver,
                        PermInferOptions {
                            array_slices: args.array_slices,
                            use_ite: args.use_ite,
                            num_fractions: args.num_fractions,
                        },
                    )
                } else {
                    PermCheckMode::None
                };

            match ctx.type_check(&mut mode) {
                Ok(()) => {}
                Err(err) => {
                    let loc = match err.span {
                        Some(span) => {
                            let (line, col) = get_line_col_num(&src, span.start).unwrap();
                            format!("{}:{}:{}", path, line, col)
                        }
                        None => format!("{}", path),
                    };
                    println!("typing error: {}: {}", loc, err.msg);
                }
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
                ParseError::UnrecognizedToken {
                    token: (start, token, _),
                    ..
                } => {
                    let (line, col) = get_line_col_num(&src, start).unwrap();
                    format!("unexpected token {} at {}:{}:{}", token, path, line, col)
                }
                ParseError::ExtraToken {
                    token: (start, token, _),
                } => {
                    let (line, col) = get_line_col_num(&src, start).unwrap();
                    format!("extra token {} at {}:{}:{}", token, path, line, col)
                }
                ParseError::User { error } => error.to_string(),
            };

            println!("parsing error: {}", msg);
        }
    }
}
