use std::env;
use std::fs;

pub mod ast;
pub mod check;
pub mod permission;

use crate::ast::*;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub dfl);

fn main() {
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
