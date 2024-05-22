use std::env;
use std::fs;

pub mod ast;
pub mod check;
pub mod permission;
pub mod smt;

use crate::ast::*;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub dfl);

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

    let args: Vec<_> = env::args().collect();
    if args.len() < 2 {
        println!("Missing file")
    } else {
        let fp = &args[1];
        let contents = fs::read_to_string(fp).expect("Unknown file");
        let parsed = dfl::ProgramParser::new().parse(&contents);
        match parsed {
            Ok(program) => {
                println!("Parsing success!");
                let ctx = Ctx::from(&program).unwrap();
                println!("{:?}", ctx);
                ctx.type_check().unwrap();
            }
            Err(e) => println!("Parse error: {}", e),
        }
    }
}
