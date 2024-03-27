pub mod ast;
pub mod check;
pub mod permissions;
use std::env;
use std::fs;
use lalrpop_util::lalrpop_mod;
use crate::check::*;
lalrpop_mod!(pub dfl);
fn main() {
    let args : Vec<_> = env::args().collect();
    if args.len() < 2 {
        println!("Missing file")
    }
    else {
        let fp = &args[1];
        let contents = fs::read_to_string(fp).expect("Unknown file");
        let oparsed = dfl::DeclsParser::new().parse(&contents);
        match oparsed {
            Ok(parsed) => {
                let res = check_decls(parsed);
                println!("Type checking success!");
                println!("{res:?}")
            },
            Err(e) => println!("Parse error: {}", e)
        }
    }
}
