use std::collections::HashSet;
use std::rc::Rc;

use indexmap::IndexMap;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct MutName(pub String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct ChanName(pub String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct ProcName(pub String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Var(pub String);

#[derive(Debug)]
pub enum PermFraction {
    Write,
    Read(u32),
}

#[derive(Debug)]
pub enum MutReference {
    Base(MutName),
    Index(MutName, Term),
    Slice(MutName, Option<Term>, Option<Term>),
}

pub type Permission = Rc<PermissionX>;
#[derive(Debug)]
pub enum PermissionX {
    Empty,
    Var(Var),
    Add(Permission, Permission),
    Ite(Term, Permission, Permission),
    Fraction(PermFraction, MutReference),
}

#[derive(Debug)]
pub enum BaseType {
    Bool,
    Int,
}

#[derive(Debug)]
pub enum MutType {
    Base(BaseType),
    Array(BaseType),
}

#[derive(Debug)]
pub struct PermType {
    pub var: Var,
    pub base: BaseType,
    pub perm: Permission,
}

#[derive(Debug)]
pub struct ProcType {
    pub ins: Vec<ChanName>,
    pub outs: Vec<ChanName>,
}

#[derive(Debug)]
pub struct ProcParams {
    pub params: Vec<(Var, MutType)>,
}

pub type Term = Rc<TermX>;
#[derive(Debug)]
pub enum TermX {
    Var(Var),
    Bool(bool),
    Int(i32),

    Add(Term, Term),
    Mul(Term, Term),

    And(Term, Term),
    Less(Term, Term),
    Equal(Term, Term),
    Not(Term),
}

pub type Proc = Rc<ProcX>;
#[derive(Debug)]
pub enum ProcX {
    Skip,
    Send(ChanName, Term, Proc),
    Recv(ChanName, Var, Proc),
    Write(MutReference, Term, Proc),
    Read(MutReference, Var, Proc),
    Ite(Term, Proc, Proc),
    Call(ProcName, Vec<Term>),
    Par(Proc, Proc),
    Debug(Proc),
}

#[derive(Debug)]
pub struct MutDecl {
    pub name: MutName,
    pub typ: MutType,
}

#[derive(Debug)]
pub struct ChanDecl {
    pub name: ChanName,
    pub typ: PermType,
}

#[derive(Debug)]
pub struct ProcDecl {
    pub name: ProcName,
    pub params: ProcParams,
    pub typ: ProcType,
    pub body: Proc,
}

#[derive(Debug)]
pub enum Decl {
    Mut(MutDecl),
    Chan(ChanDecl),
    Proc(ProcDecl),
}

#[derive(Debug)]
pub struct Ctx {
    pub muts: IndexMap<MutName, MutDecl>,
    pub chans: IndexMap<ChanName, ChanDecl>,
    pub procs: IndexMap<ProcName, ProcDecl>,
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx {
            muts: IndexMap::new(),
            chans: IndexMap::new(),
            procs: IndexMap::new(),
        }
    }
}

impl TermX {
    fn free_vars_inplace(&self, vars: &mut HashSet<Var>) {
        match self {
            TermX::Var(var) => {
                vars.insert(var.clone());
            }
            TermX::Bool(_) => {}
            TermX::Int(_) => {}
            TermX::Add(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Mul(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::And(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Less(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Equal(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Not(t) => {
                t.free_vars_inplace(vars);
            }
        }
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let mut vars = HashSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }
}

impl PermissionX {
    fn free_vars_inplace(&self, vars: &mut HashSet<Var>) {
        match self {
            PermissionX::Empty => {}
            PermissionX::Var(var) => {
                vars.insert(var.clone());
            }
            PermissionX::Add(p1, p2) => {
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Ite(t, p1, p2) => {
                t.free_vars_inplace(vars);
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Fraction(..) => {}
        }
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let mut vars = HashSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }
}
