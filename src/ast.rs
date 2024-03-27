#![allow(unused_imports)]
#![allow(dead_code)]
use fraction::Fraction;
use im::hashmap::*;
use im::hashset::*;
use std::rc::Rc;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Var {
    pub pvar: String
    // ident: u32,
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Chan(pub String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Location(pub String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct ProcName(pub String);

#[derive(Debug)]
pub enum Expr {
    EVar(Var),
    EInt(u32),
    EAdd(Rc<Expr>, Rc<Expr>),
}

#[derive(Debug)]
pub enum Proc {
    PDebug(Rc<Proc>),
    PSend(Chan, Rc<Expr>, Rc<Proc>),
    PRecv(Chan, Var, Rc<Proc>),
    PWrite(Location, Rc<Expr>, Rc<Proc>),
    PRead(Location, Var, Rc<Proc>),
    PCall(ProcName),
    Par(Rc<Proc>, Rc<Proc>),
    PSkip,
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Permission(pub HashMap<Location, Fraction>);

#[derive(Clone, Debug, PartialEq)]
pub struct ProcTy {
    pub ins: HashSet<Chan>,
    pub outs: HashSet<Chan>,
}

#[derive(Debug)]
pub enum Decl {
    DeclLoc(Location),
    DeclChan(Chan, Permission),
    DeclProc(ProcName, ProcTy, Rc<Proc>)
}
