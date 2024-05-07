use std::env;
use std::fs;

pub mod ast;
// pub mod check;
// pub mod permissions;
// use crate::check::*;

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
        let parsed = dfl::DeclsParser::new().parse(&contents);
        match parsed {
            Ok(decls) => {
                println!("Parsing success!");

                let mut ctx = Ctx::new();
                for decl in decls {
                    match decl {
                        Decl::Mut(decl) => {
                            if ctx.muts.contains_key(&decl.name) {
                                panic!("duplicate mutable definition {:?}", decl.name);
                            }
                            ctx.muts.insert(decl.name.clone(), decl);
                        },
                        Decl::Chan(decl) => {
                            if ctx.chans.contains_key(&decl.name) {
                                panic!("duplicate channel definition {:?}", decl.name);
                            }
                            ctx.chans.insert(decl.name.clone(), decl);
                        },
                        Decl::Proc(decl) => {
                            if ctx.procs.contains_key(&decl.name) {
                                panic!("duplicate process definition {:?}", decl.name);
                            }
                            ctx.procs.insert(decl.name.clone(), decl);
                        },
                    }
                }
                
                println!("{:?}", ctx);
            }
            Err(e) => println!("Parse error: {}", e),
        }
    }
}
