#![allow(unused_imports)]
#![allow(dead_code)]
use fraction::Fraction;
use im::hashmap::*;
use im::hashset::*;
use std::rc::Rc;
use std::fmt;

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


impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.pvar)
    }
}

impl fmt::Display for Chan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for ProcName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Permission {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.iter().try_for_each(|(loc,v)| write!(f, "{} {} ", v, loc))
    }
}
        

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::EVar(v) => v.fmt(f),
            Expr::EInt(i) => i.fmt(f),
            Expr::EAdd(e1, e2) => write!(f, "{} + {}", e1, e2)
        }
    }
}
