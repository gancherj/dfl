use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

use indexmap::IndexMap;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct MutName(pub Rc<str>);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct ChanName(pub Rc<str>);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct ProcName(pub Rc<str>);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Var(pub Rc<str>);

#[derive(Clone, Copy, Debug)]
pub enum PermFraction {
    Write,
    Read(u32),
}

pub type MutReference = Rc<MutReferenceX>;
#[derive(Debug)]
pub enum MutReferenceX {
    Base(MutName),
    Index(MutName, Term),
    Slice(MutName, Option<Term>, Option<Term>),
}

pub type Permission = Rc<PermissionX>;
#[derive(Debug)]
pub enum PermissionX {
    Empty,
    Add(Permission, Permission),
    Sub(Permission, Permission),
    Ite(Term, Permission, Permission),
    Fraction(PermFraction, MutReference),
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum BaseType {
    Bool,
    Int,
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum MutType {
    Base(BaseType),
    Array(BaseType),
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

pub type MutDecl = Rc<MutDeclX>;
#[derive(Debug)]
pub struct MutDeclX {
    pub name: MutName,
    pub typ: MutType,
}

pub type ChanDecl = Rc<ChanDeclX>;
#[derive(Debug)]
pub struct ChanDeclX {
    pub name: ChanName,
    pub typ: BaseType,
    pub perm: Permission,
}

#[derive(Debug)]
pub struct ProcParam {
    pub name: Var,
    pub typ: BaseType,
}

pub type ProcResource = Rc<ProcResourceX>;
#[derive(Debug)]
pub enum ProcResourceX {
    Perm(Permission),
    Input(ChanName),
    Output(ChanName),
}

pub type ProcDecl = Rc<ProcDeclX>;
#[derive(Debug)]
pub struct ProcDeclX {
    pub name: ProcName,
    pub params: Vec<ProcParam>,
    pub res: Vec<ProcResource>,
    pub body: Proc,
}

#[derive(Debug)]
pub enum Decl {
    Mut(MutDecl),
    Chan(ChanDecl),
    Proc(ProcDecl),
}

pub struct Program {
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub struct Ctx {
    pub muts: IndexMap<MutName, MutDecl>,
    pub chans: IndexMap<ChanName, ChanDecl>,
    pub procs: IndexMap<ProcName, ProcDecl>,
}

impl From<&ChanName> for Var {
    fn from(value: &ChanName) -> Var {
        Var(value.0.clone())
    }
}

impl From<&str> for Var {
    fn from(value: &str) -> Var {
        Var(value.into())
    }
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx {
            muts: IndexMap::new(),
            chans: IndexMap::new(),
            procs: IndexMap::new(),
        }
    }

    pub fn from(prog: &Program) -> Result<Ctx, String> {
        let mut ctx = Ctx::new();
        for decl in &prog.decls {
            match decl {
                Decl::Mut(decl) => {
                    if ctx.muts.contains_key(&decl.name) {
                        return Err(format!("duplicate mutable declaration {:?}", decl.name));
                    }
                    ctx.muts.insert(decl.name.clone(), decl.clone());
                }
                Decl::Chan(decl) => {
                    if ctx.chans.contains_key(&decl.name) {
                        return Err(format!("duplicate channel declaration {:?}", decl.name));
                    }
                    ctx.chans.insert(decl.name.clone(), decl.clone());
                }
                Decl::Proc(decl) => {
                    if ctx.procs.contains_key(&decl.name) {
                        return Err(format!("duplicate process definition {:?}", decl.name));
                    }
                    ctx.procs.insert(decl.name.clone(), decl.clone());
                }
            }
        }
        Ok(ctx)
    }
}

impl TermX {
    pub fn var(v: &Var) -> Term {
        Rc::new(TermX::Var(v.clone()))
    }

    /// Returns Some if the term is substituted, None if unchanged
    fn substitute_inplace(term: &Term, subst: &IndexMap<Var, Term>) -> Option<Term> {
        match term.as_ref() {
            TermX::Var(var) => Some(subst.get(var)?.clone()),
            TermX::Bool(_) => None,
            TermX::Int(_) => None,
            TermX::Add(t1, t2) => {
                let t1_subst = Self::substitute_inplace(t1, subst);
                let t2_subst = Self::substitute_inplace(t2, subst);

                if t1_subst.is_some() || t2_subst.is_some() {
                    Some(Rc::new(TermX::Add(
                        t1_subst.unwrap_or(t1.clone()),
                        t2_subst.unwrap_or(t2.clone()),
                    )))
                } else {
                    None
                }
            }
            TermX::Mul(t1, t2) => {
                let t1_subst = Self::substitute_inplace(t1, subst);
                let t2_subst = Self::substitute_inplace(t2, subst);

                if t1_subst.is_some() || t2_subst.is_some() {
                    Some(Rc::new(TermX::Mul(
                        t1_subst.unwrap_or(t1.clone()),
                        t2_subst.unwrap_or(t2.clone()),
                    )))
                } else {
                    None
                }
            }
            TermX::And(t1, t2) => {
                let t1_subst = Self::substitute_inplace(t1, subst);
                let t2_subst = Self::substitute_inplace(t2, subst);

                if t1_subst.is_some() || t2_subst.is_some() {
                    Some(Rc::new(TermX::And(
                        t1_subst.unwrap_or(t1.clone()),
                        t2_subst.unwrap_or(t2.clone()),
                    )))
                } else {
                    None
                }
            }
            TermX::Less(t1, t2) => {
                let t1_subst = Self::substitute_inplace(t1, subst);
                let t2_subst = Self::substitute_inplace(t2, subst);

                if t1_subst.is_some() || t2_subst.is_some() {
                    Some(Rc::new(TermX::Less(
                        t1_subst.unwrap_or(t1.clone()),
                        t2_subst.unwrap_or(t2.clone()),
                    )))
                } else {
                    None
                }
            }
            TermX::Equal(t1, t2) => {
                let t1_subst = Self::substitute_inplace(t1, subst);
                let t2_subst = Self::substitute_inplace(t2, subst);

                if t1_subst.is_some() || t2_subst.is_some() {
                    Some(Rc::new(TermX::Equal(
                        t1_subst.unwrap_or(t1.clone()),
                        t2_subst.unwrap_or(t2.clone()),
                    )))
                } else {
                    None
                }
            }
            TermX::Not(t) => Self::substitute_inplace(t, subst).map(|t| Rc::new(TermX::Not(t))),
        }
    }

    /// Substitutes into a term without modifying unchanged subtrees
    pub fn substitute(term: &Term, subst: &IndexMap<Var, Term>) -> Term {
        Self::substitute_inplace(term, subst).unwrap_or(term.clone())
    }

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

    /// Precedence of the top level operator
    fn precedence(&self) -> u32 {
        match self {
            TermX::Var(..) => 0,
            TermX::Bool(..) => 0,
            TermX::Int(..) => 0,
            TermX::Add(..) => 2,
            TermX::Mul(..) => 1,
            TermX::And(..) => 5,
            TermX::Less(..) => 3,
            TermX::Equal(..) => 3,
            TermX::Not(..) => 4,
        }
    }
}

impl PermissionX {
    pub fn is_empty(&self) -> bool {
        match self {
            PermissionX::Empty => true,
            _ => false,
        }
    }

    pub fn empty() -> Permission {
        Rc::new(PermissionX::Empty)
    }

    pub fn add(p1: &Permission, p2: &Permission) -> Permission {
        if p1.is_empty() {
            p2.clone()
        } else if p2.is_empty() {
            p1.clone()
        } else {
            Rc::new(PermissionX::Add(p1.clone(), p2.clone()))
        }
    }

    pub fn sub(p1: &Permission, p2: &Permission) -> Permission {
        if p2.is_empty() {
            p1.clone()
        } else {
            Rc::new(PermissionX::Sub(p1.clone(), p2.clone()))
        }
    }

    /// Returns Some if the term is substituted, None if unchanged
    fn substitute_inplace(perm: &Permission, subst: &IndexMap<Var, Term>) -> Option<Permission> {
        match perm.as_ref() {
            PermissionX::Empty => None,
            PermissionX::Add(p1, p2) => {
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if p1_subst.is_some() || p2_subst.is_some() {
                    Some(Rc::new(PermissionX::Add(
                        p1_subst.unwrap_or(p1.clone()),
                        p2_subst.unwrap_or(p2.clone()),
                    )))
                } else {
                    None
                }
            }
            PermissionX::Sub(p1, p2) => {
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if p1_subst.is_some() || p2_subst.is_some() {
                    Some(Rc::new(PermissionX::Sub(
                        p1_subst.unwrap_or(p1.clone()),
                        p2_subst.unwrap_or(p2.clone()),
                    )))
                } else {
                    None
                }
            }
            PermissionX::Ite(t, p1, p2) => {
                let t_subst = TermX::substitute_inplace(t, subst);
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if t_subst.is_some() || p1_subst.is_some() || p2_subst.is_some() {
                    Some(Rc::new(PermissionX::Ite(
                        t_subst.unwrap_or(t.clone()),
                        p1_subst.unwrap_or(p1.clone()),
                        p2_subst.unwrap_or(p2.clone()),
                    )))
                } else {
                    None
                }
            }
            PermissionX::Fraction(frac, mut_ref) => {
                match mut_ref.as_ref() {
                    MutReferenceX::Base(_) => None,
                    MutReferenceX::Index(name, term) => {
                        let term_subst = TermX::substitute_inplace(term, subst);
                        if term_subst.is_some() {
                            Some(Rc::new(PermissionX::Fraction(
                                *frac,
                                Rc::new(MutReferenceX::Index(name.clone(), term_subst.unwrap())),
                            )))
                        } else {
                            None
                        }
                    },
                    MutReferenceX::Slice(name, t1, t2) => {
                        let t1_subst = t1.as_ref().map(|t| TermX::substitute_inplace(&t, subst)).flatten();
                        let t2_subst = t2.as_ref().map(|t| TermX::substitute_inplace(&t, subst)).flatten();
                        if t1_subst.is_some() || t2_subst.is_some() {
                            Some(Rc::new(PermissionX::Fraction(
                                *frac,
                                Rc::new(MutReferenceX::Slice(name.clone(),
                                    if t1.is_some() { Some(t1_subst.unwrap_or(t1.as_ref().unwrap().clone())) } else { None },
                                    if t2.is_some() { Some(t2_subst.unwrap_or(t2.as_ref().unwrap().clone())) } else { None },
                                )),
                            )))
                        } else {
                            None
                        }
                    },
                }
            }
        }
    }

    /// Substitutes into a permission without modifying unchanged subtrees
    pub fn substitute(perm: &Permission, subst: &IndexMap<Var, Term>) -> Permission {
        Self::substitute_inplace(perm, subst).unwrap_or(perm.clone())
    }

    pub fn substitute_one(perm: &Permission, var: &Var, subterm: &Term) -> Permission {
        PermissionX::substitute(perm, &IndexMap::from([ (var.clone(), subterm.clone()) ]))
    }

    fn free_vars_inplace(&self, vars: &mut HashSet<Var>) {
        match self {
            PermissionX::Empty => {}
            PermissionX::Add(p1, p2) => {
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Sub(p1, p2) => {
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Ite(t, p1, p2) => {
                t.free_vars_inplace(vars);
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Fraction(_, mut_ref) => match mut_ref.as_ref() {
                MutReferenceX::Base(_) => {}
                MutReferenceX::Index(_, t) => {
                    t.free_vars_inplace(vars);
                }
                MutReferenceX::Slice(_, t1, t2) => {
                    if let Some(t1) = t1 {
                        t1.free_vars_inplace(vars);
                    }
                    if let Some(t2) = t2 {
                        t2.free_vars_inplace(vars);
                    }
                }
            },
        }
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let mut vars = HashSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }
}

impl ProcX {
    pub fn skip() -> Proc {
        Rc::new(ProcX::Skip)
    }

    pub fn par(p1: &Proc, p2: &Proc) -> Proc {
        Rc::new(ProcX::Par(p1.clone(), p2.clone()))
    }

    pub fn call(name: &ProcName, args: &[Term]) -> Proc {
        Rc::new(ProcX::Call(name.clone(), Vec::from(args)))
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for MutName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for ChanName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for ProcName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BaseType::Bool => write!(f, "bool"),
            BaseType::Int => write!(f, "int"),
        }
    }
}

impl fmt::Display for MutType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutType::Base(base) => write!(f, "{}", base),
            MutType::Array(base) => write!(f, "[{}]", base),
        }
    }
}

impl fmt::Display for TermX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermX::Var(var) => write!(f, "{}", var),
            TermX::Bool(b) => write!(f, "{}", b),
            TermX::Int(i) => write!(f, "{}", i),
            TermX::Add(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " + {}", t2)?;
                } else {
                    write!(f, " + ({})", t2)?;
                }
                Ok(())
            },
            TermX::Mul(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " * {}", t2)?;
                } else {
                    write!(f, " * ({})", t2)?;
                }
                Ok(())
            },
            TermX::And(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " and {}", t2)?;
                } else {
                    write!(f, " and ({})", t2)?;
                }
                Ok(())
            },
            TermX::Less(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " < {}", t2)?;
                } else {
                    write!(f, " < ({})", t2)?;
                }
                Ok(())
            },
            TermX::Equal(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " = {}", t2)?;
                } else {
                    write!(f, " = ({})", t2)?;
                }
                Ok(())
            },
            TermX::Not(t) => {
                if t.precedence() <= self.precedence() {
                    write!(f, "not {}", t)?;
                } else {
                    write!(f, "not ({})", t)?;
                }
                Ok(())
            },
        }
    }
}

impl fmt::Display for PermFraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermFraction::Write => write!(f, "write"),
            PermFraction::Read(k) => write!(f, "read_{}", k),
        }
    }
}

impl fmt::Display for MutReferenceX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutReferenceX::Base(name) => write!(f, "{}", name),
            MutReferenceX::Index(name, t) => write!(f, "{}[{}]", name, t),
            MutReferenceX::Slice(name, t1, t2) =>
                write!(
                    f, "{}[{}..{}]", name,
                    t1.as_ref().unwrap_or(&Rc::new(TermX::Var(Var::from("")))),
                    t2.as_ref().unwrap_or(&Rc::new(TermX::Var(Var::from("")))),
                ),
        }
    }
}

impl fmt::Display for PermissionX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermissionX::Empty => write!(f, "0"),
            PermissionX::Add(p1, p2) =>
                if match p2.as_ref() {
                    PermissionX::Sub(..) => true,
                    _ => false,
                } {
                    write!(f, "{} + ({})", p1, p2)
                } else {
                    write!(f, "{} + {}", p1, p2)
                }
            PermissionX::Sub(p1, p2) =>
                if match p2.as_ref() {
                    PermissionX::Add(..) => true,
                    PermissionX::Sub(..) => true,
                    _ => false,
                } {
                    write!(f, "{} - ({})", p1, p2)
                } else {
                    write!(f, "{} - {}", p1, p2)
                },
            PermissionX::Ite(t, p1, p2) =>
                write!(f, "if {} then {} else {} end", t, p1, p2),
            PermissionX::Fraction(frac, mut_ref) =>
                write!(f, "{} {}", frac, mut_ref),
        }
    }
}
