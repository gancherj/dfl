use std::{borrow::Borrow, fmt};
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::span::*;

/// Macro for defining string types like
/// pub struct $NAME(Rc<str>);
macro_rules! rc_str_type {
    ($typ_name:ident, $fmt_pattern:expr) => {
        #[derive(Hash, Eq, PartialEq, Clone, Debug)]
        pub struct $typ_name(Rc<str>);

        impl From<&$typ_name> for Rc<str> {
            fn from(v: &$typ_name) -> Self {
                v.0.clone()
            }
        }

        impl<S: Into<Rc<str>>> From<S> for $typ_name {
            fn from(v: S) -> Self {
                $typ_name(v.into())
            }
        }

        impl fmt::Display for $typ_name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, $fmt_pattern, self.0)
            }
        }

        impl $typ_name {
            pub fn as_str(&self) -> &str {
                self.0.as_ref()
            }
        }
    };
}

rc_str_type!(MutName, "{}");
rc_str_type!(ChanName, "{}");
rc_str_type!(ProcName, "{}");
rc_str_type!(Var, "{}");
rc_str_type!(Const, "const({})");
rc_str_type!(PermVar, "{}");

#[derive(Clone, Copy, Debug)]
pub enum PermFraction {
    Write,
    Read(u32),
}

pub type MutReference = RcSpanned<MutReferenceX>;
#[derive(Debug)]
pub enum MutReferenceX {
    Base(MutName),
    Deref(Term),
    Index(MutReference, Term),
    Slice(MutReference, Option<Term>, Option<Term>),
}

pub type Permission = RcSpanned<PermissionX>;
#[derive(Debug)]
pub enum PermissionX {
    Empty,
    Add(Permission, Permission),
    Sub(Permission, Permission),
    Ite(Term, Permission, Permission),
    Fraction(PermFraction, MutReference),
    Var(PermVar, Vec<Term>),
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum BaseType {
    Bool,
    Int,
    Ref(Rc<[MutName]>, usize),
}

pub type MutType = Rc<MutTypeX>;
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum MutTypeX {
    Base(BaseType),
    Array(MutType),
}

pub type Term = RcSpanned<TermX>;
#[derive(Debug)]
pub enum TermX {
    Var(Var),
    Const(Const),
    Bool(bool),
    Int(i64),

    Ref(MutReference),

    Add(Term, Term),
    Mul(Term, Term),

    And(Term, Term),
    Less(Term, Term),
    Equal(Term, Term),
    Not(Term),
}

pub type Proc = RcSpanned<ProcX>;
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

pub type ConstDecl = RcSpanned<ConstDeclX>;
#[derive(Debug)]
pub struct ConstDeclX {
    pub name: Const,
    pub typ: BaseType,
}

pub type PermDecl = RcSpanned<PermDeclX>;
#[derive(Debug)]
pub struct PermDeclX {
    pub name: PermVar,
    pub param_typs: Vec<BaseType>,
}

pub type MutDecl = RcSpanned<MutDeclX>;
#[derive(Debug)]
pub struct MutDeclX {
    pub name: MutName,
    pub typ: MutType,
}

pub type ChanDecl = RcSpanned<ChanDeclX>;
#[derive(Debug)]
pub struct ChanDeclX {
    pub name: ChanName,
    pub typ: BaseType,
    pub perm: Permission,
}

#[derive(Clone, Debug)]
pub struct ProcParam {
    pub name: Var,
    pub typ: BaseType,
}

pub type ProcResource = RcSpanned<ProcResourceX>;
#[derive(Debug)]
pub enum ProcResourceX {
    Perm(Permission),
    Input(ChanName),
    Output(ChanName),
}

pub type ProcDecl = RcSpanned<ProcDeclX>;
#[derive(Debug)]
pub struct ProcDeclX {
    pub name: ProcName,
    pub params: Vec<ProcParam>,
    pub res: Vec<ProcResource>,
    pub all_res: bool,
    pub body: Proc,
}

#[derive(Debug)]
pub enum Decl {
    Const(ConstDecl),
    Perm(PermDecl),
    Mut(MutDecl),
    Chan(ChanDecl),
    Proc(ProcDecl),
}

pub struct Program {
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub struct Ctx {
    pub consts: IndexMap<Const, ConstDecl>,
    pub perms: IndexMap<PermVar, PermDecl>,
    pub muts: IndexMap<MutName, MutDecl>,
    pub chans: IndexMap<ChanName, ChanDecl>,
    pub procs: IndexMap<ProcName, ProcDecl>,
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx {
            consts: IndexMap::new(),
            perms: IndexMap::new(),
            muts: IndexMap::new(),
            chans: IndexMap::new(),
            procs: IndexMap::new(),
        }
    }

    /// Process a parsed AST into a context
    /// This do some preprocessing including
    /// replacing constants and some notations like
    /// "all" resources
    pub fn from(prog: &Program) -> Result<Ctx, String> {
        let mut ctx = Ctx::new();
        let mut subst = IndexMap::new();

        // Collect all constants and mutables first
        for decl in &prog.decls {
            match decl {
                Decl::Const(decl) => {
                    if ctx.consts.contains_key(&decl.name) {
                        return Err(format!("duplicate constant declaration {:?}", decl.name));
                    }
                    ctx.consts.insert(decl.name.clone(), decl.clone());
                    subst.insert(Var::from(&decl.name), TermX::constant(&decl.name));
                }
                Decl::Mut(decl) => {
                    if ctx.muts.contains_key(&decl.name) {
                        return Err(format!("duplicate mutable declaration {:?}", decl.name));
                    }
                    ctx.muts.insert(decl.name.clone(), decl.clone());
                }
                _ => {}
            }
        }

        // Collect all permissions
        for decl in &prog.decls {
            match decl {
                Decl::Perm(decl) => {
                    if ctx.perms.contains_key(&decl.name) {
                        return Err(format!("duplicate permission variable declaration {:?}", decl.name));
                    }
                    ctx.perms.insert(decl.name.clone(), decl.clone());
                }
                _ => {}
            }
        }

        // Collect channel declarations converting some Var to Const
        for decl in &prog.decls {
            match decl {
                Decl::Chan(decl) => {
                    if ctx.chans.contains_key(&decl.name) {
                        return Err(format!("duplicate channel declaration {:?}", decl.name));
                    }
                    // Substitute constants
                    ctx.chans.insert(decl.name.clone(), Spanned::spanned_option(decl.span, ChanDeclX {
                        name: decl.name.clone(),
                        typ: decl.typ.clone(),
                        perm: PermissionX::substitute(&decl.perm, &subst),
                    }));
                }
                _ => {}
            }
        }
        
        // Collect process declarations while converting some Var to Const
        // and also expanding "all" resource notation
        for decl in &prog.decls {
            match decl {
                Decl::Proc(decl) => {
                    if ctx.procs.contains_key(&decl.name) {
                        return Err(format!("duplicate process definition {:?}", decl.name));
                    }

                    // Copy new resources with constants substituted
                    let mut new_res = Vec::new();

                    if decl.all_res {
                        // The process should have all mutable and channel resources in the context
                        for mut_name in ctx.muts.keys() {
                            // Add write permission to mut_name
                            new_res.push(Spanned::spanned_option(decl.span, ProcResourceX::Perm(
                                Spanned::spanned_option(decl.span, PermissionX::Fraction(
                                    PermFraction::Write,
                                    Spanned::spanned_option(decl.span, MutReferenceX::Base(mut_name.clone())),
                                ),
                            ))));
                        }

                        for chan_name in ctx.chans.keys() {
                            new_res.push(Spanned::spanned_option(decl.span, ProcResourceX::Input(chan_name.clone())));
                            new_res.push(Spanned::spanned_option(decl.span, ProcResourceX::Output(chan_name.clone())));
                        }
                    } else {
                        for res in &decl.res {
                            let res_subst = match &res.x {
                                ProcResourceX::Perm(p) =>
                                    Spanned::spanned_option(res.span, ProcResourceX::Perm(PermissionX::substitute(p, &subst))),
                                _ => res.clone(),
                            };
                            new_res.push(res_subst);
                        }
                    }

                    // Copy a new substitution with process parameters shadowed
                    let mut new_subst = IndexMap::new();
                    for (v, c) in &subst {
                        new_subst.insert(v.clone(), c.clone());
                    }
                    for param in &decl.params {
                        new_subst.shift_remove(&param.name);
                    }

                    // Substitute the process body
                    let new_body = ProcX::substitute(&decl.body, &mut new_subst);

                    ctx.procs.insert(decl.name.clone(), Spanned::spanned_option(decl.span, ProcDeclX {
                        name: decl.name.clone(),
                        params: decl.params.iter().map(|p| p.clone()).collect(),
                        res: new_res,
                        all_res: false,
                        body: new_body,
                    }));
                }
                _ => {}
            }
        }
        Ok(ctx)
    }
}

impl TermX {
    pub fn var(v: impl Into<Var>) -> Term {
        Spanned::new(TermX::Var(v.into()))
    }

    pub fn constant(c: impl Into<Const>) -> Term {
        Spanned::new(TermX::Const(c.into()))
    }

    pub fn not(t: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::Not(t.borrow().clone()))
    }

    /// Returns Some if the term is substituted, None if unchanged
    fn substitute_inplace(term: impl Borrow<Term>, subst: &IndexMap<Var, Term>) -> Option<Term> {
        match &term.borrow().x {
            TermX::Var(var) => Some(subst.get(var)?.clone()),
            TermX::Const(..) => None,
            TermX::Bool(..) => None,
            TermX::Int(..) => None,
            TermX::Ref(m) => {
                let m_subst = MutReferenceX::substitute_inplace(m, subst);
                if m_subst.is_some() {
                    Some(Spanned::spanned_option(term.borrow().span, TermX::Ref(m_subst.unwrap())))
                } else {
                    None
                }
            }
            TermX::Add(t1, t2) => {
                let t1_subst = Self::substitute_inplace(t1, subst);
                let t2_subst = Self::substitute_inplace(t2, subst);

                if t1_subst.is_some() || t2_subst.is_some() {
                    Some(Spanned::spanned_option(term.borrow().span, TermX::Add(
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
                    Some(Spanned::spanned_option(term.borrow().span, TermX::Mul(
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
                    Some(Spanned::spanned_option(term.borrow().span, TermX::And(
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
                    Some(Spanned::spanned_option(term.borrow().span, TermX::Less(
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
                    Some(Spanned::spanned_option(term.borrow().span, TermX::Equal(
                        t1_subst.unwrap_or(t1.clone()),
                        t2_subst.unwrap_or(t2.clone()),
                    )))
                } else {
                    None
                }
            }
            TermX::Not(t) =>
                Self::substitute_inplace(t, subst).map(|t| Spanned::spanned_option(term.borrow().span, TermX::Not(t))),
        }
    }

    /// Substitutes into a term without modifying unchanged subtrees
    pub fn substitute(term: impl Borrow<Term>, subst: &IndexMap<Var, Term>) -> Term {
        Self::substitute_inplace(term.borrow(), subst).unwrap_or(term.borrow().clone())
    }

    fn free_vars_inplace(&self, vars: &mut IndexSet<Var>) {
        match self {
            TermX::Var(var) => {
                vars.insert(var.clone());
            }
            TermX::Const(..) => {}
            TermX::Bool(..) => {}
            TermX::Int(..) => {}
            TermX::Ref(m) => {
                m.free_vars_inplace(vars);
            }
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

    pub fn free_vars(&self) -> IndexSet<Var> {
        let mut vars = IndexSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }

    /// Precedence of the top level operator
    fn precedence(&self) -> u32 {
        match self {
            TermX::Var(..) => 0,
            TermX::Const(..) => 0,
            TermX::Bool(..) => 0,
            TermX::Int(..) => 0,
            TermX::Ref(..) => 0,
            TermX::Add(..) => 2,
            TermX::Mul(..) => 1,
            TermX::And(..) => 5,
            TermX::Less(..) => 3,
            TermX::Equal(..) => 3,
            TermX::Not(..) => 4,
        }
    }
}

impl MutTypeX {
    /// get_deref_type([[int]], 0) = [[int]]
    /// get_deref_type([[int]], 1) = [int]
    /// get_deref_type([[int]], 3) = None
    pub fn get_deref_type(typ: &MutType, level: usize) -> Option<MutType> {
        if level == 0 {
            Some(typ.clone())
        } else {
            match typ.as_ref() {
                MutTypeX::Base(..) => None,
                MutTypeX::Array(t) => MutTypeX::get_deref_type(t, level - 1),
            }
        }
    }

    pub fn get_base_type(&self) -> &BaseType {
        match self {
            MutTypeX::Base(t) => t,
            MutTypeX::Array(t) => t.get_base_type(),
        }
    }

    pub fn get_dimensions(&self) -> usize {
        match self {
            MutTypeX::Base(..) => 0,
            MutTypeX::Array(t) => t.get_dimensions() + 1,
        }
    }
}

impl MutReferenceX {
    /// Check if the base type is a direct reference instead of a deref
    pub fn is_simple(&self) -> bool {
        match self {
            MutReferenceX::Base(..) => true,
            MutReferenceX::Deref(..) => false,
            MutReferenceX::Index(m, ..) => m.is_simple(),
            MutReferenceX::Slice(m, ..) => m.is_simple(),
        }
    }

    fn free_vars_inplace(&self, vars: &mut IndexSet<Var>) {
        match self {
            MutReferenceX::Base(..) => {}
            MutReferenceX::Deref(t) => {
                t.free_vars_inplace(vars);
            }
            MutReferenceX::Index(m, t) => {
                m.free_vars_inplace(vars);
                TermX::free_vars_inplace(t, vars);
            }
            MutReferenceX::Slice(m, t1, t2) => {
                m.free_vars_inplace(vars);
                if let Some(t1) = t1 {
                    TermX::free_vars_inplace(t1, vars);
                }
                if let Some(t2) = t2 {
                    TermX::free_vars_inplace(t2, vars);
                }
            }
        }
    }

    /// Returns None if unchanged
    fn substitute_inplace(mut_ref: impl Borrow<MutReference>, subst: &IndexMap<Var, Term>) -> Option<MutReference> {
        match &mut_ref.borrow().x {
            MutReferenceX::Base(..) => None,
            MutReferenceX::Deref(t) => {
                let t_subst = TermX::substitute_inplace(t, subst);
                if t_subst.is_some() {
                    Some(Spanned::spanned_option(mut_ref.borrow().span, MutReferenceX::Deref(t_subst.unwrap())))
                } else {
                    None
                }
            }
            MutReferenceX::Index(m, t) => {
                let m_subst = Self::substitute_inplace(m, subst);
                let t_subst = TermX::substitute_inplace(t, subst);
                if m_subst.is_some() || t_subst.is_some() {
                    Some(Spanned::spanned_option(mut_ref.borrow().span, MutReferenceX::Index(
                        m_subst.unwrap_or(m.clone()),
                        t_subst.unwrap_or(t.clone()),
                    )))
                } else {
                    None
                }
            }
            MutReferenceX::Slice(m, t1, t2) => {
                let m_subst = Self::substitute_inplace(m, subst);
                let t1_subst = t1.as_ref().map(|t| TermX::substitute_inplace(t, subst)).flatten();
                let t2_subst = t2.as_ref().map(|t| TermX::substitute_inplace(t, subst)).flatten();
                if m_subst.is_some() || t1_subst.is_some() || t2_subst.is_some() {
                    Some(Spanned::spanned_option(mut_ref.borrow().span, MutReferenceX::Slice(
                        m_subst.unwrap_or(m.clone()),
                        if t1.is_some() { Some(t1_subst.unwrap_or(t1.as_ref().unwrap().clone())) } else { None },
                        if t2.is_some() { Some(t2_subst.unwrap_or(t2.as_ref().unwrap().clone())) } else { None },
                    )))
                } else {
                    None
                }
            }
        }
    }

    // Substitute the highest level deref with a fixed reference to a mutable
    pub fn substitute_deref_with_mut_name(mut_ref: impl Borrow<MutReference>, name: &MutName) -> MutReference {
        match &mut_ref.borrow().x {
            MutReferenceX::Base(..) => mut_ref.borrow().clone(),
            MutReferenceX::Deref(..) => Spanned::spanned_option(mut_ref.borrow().span, MutReferenceX::Base(name.clone())),
            MutReferenceX::Index(m, t) =>
                Spanned::spanned_option(mut_ref.borrow().span, MutReferenceX::Index(MutReferenceX::substitute_deref_with_mut_name(m, name), t.clone())),
            MutReferenceX::Slice(m, t1, t2) =>
                Spanned::spanned_option(mut_ref.borrow().span, MutReferenceX::Slice(MutReferenceX::substitute_deref_with_mut_name(m, name), t1.clone(), t2.clone())),
        }
    }
}

impl ProcX {
    /// Returns None if unchanged
    // TODO: this functinon currently assumes no capturing of variables
    fn substitute_inplace(proc: impl Borrow<Proc>, subst: &mut IndexMap<Var, Term>) -> Option<Proc> {
        match &proc.borrow().x {
            ProcX::Skip => None,
            ProcX::Send(c, t, p) => {
                let t_subst = TermX::substitute_inplace(t, subst);
                let p_subst = Self::substitute_inplace(p, subst);

                if t_subst.is_some() || p_subst.is_some() {
                    Some(ProcX::send(
                        c,
                        &t_subst.unwrap_or(t.clone()),
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Recv(c, v, p) => {
                let p_subst = if let Some(t) = subst.get(v) {
                    let t_clone = t.clone();
                    subst.shift_remove(v);
                    let p_subst = Self::substitute_inplace(p, subst);
                    subst.insert(v.clone(), t_clone); // TODO: might mess up the order of terms
                    p_subst
                } else {
                    Self::substitute_inplace(p, subst)
                };

                if p_subst.is_some() {
                    Some(ProcX::recv(
                        c, v,
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Write(m, t, p) => {
                let m_subst = MutReferenceX::substitute_inplace(m, subst);
                let t_subst = TermX::substitute_inplace(t, subst);
                let p_subst = Self::substitute_inplace(p, subst);

                if m_subst.is_some() || t_subst.is_some() || p_subst.is_some() {
                    Some(ProcX::write(
                        &m_subst.unwrap_or(m.clone()),
                        &t_subst.unwrap_or(t.clone()),
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Read(m, v, p) => {
                let m_subst = MutReferenceX::substitute_inplace(m, subst);
                let p_subst = if let Some(t) = subst.get(v) {
                    let t_clone = t.clone();
                    subst.shift_remove(v);
                    let p_subst = Self::substitute_inplace(p, subst);
                    subst.insert(v.clone(), t_clone); // TODO: might mess up the order of terms
                    p_subst
                } else {
                    Self::substitute_inplace(p, subst)
                };

                if m_subst.is_some() || p_subst.is_some() {
                    Some(ProcX::read(
                        &m_subst.unwrap_or(m.clone()),
                        v,
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Ite(t, p1, p2) => {
                let t_subst = TermX::substitute_inplace(t, subst);
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if t_subst.is_some() || p1_subst.is_some() || p2_subst.is_some() {
                    Some(ProcX::ite(
                        &t_subst.unwrap_or(t.clone()),
                        &p1_subst.unwrap_or(p1.clone()),
                        &p2_subst.unwrap_or(p2.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Call(n, args) => {
                let mut new_args = Vec::new();
                let mut changed = false;

                for arg in args {
                    let arg_subst = TermX::substitute_inplace(arg, subst);
                    if let Some(arg_subst) = arg_subst {
                        changed = true;
                        new_args.push(arg_subst);
                    } else {
                        new_args.push(arg.clone());
                    }
                }

                if changed {
                    Some(ProcX::call(n, &new_args))
                } else {
                    None
                }
            }
            ProcX::Par(p1, p2) => {
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if p1_subst.is_some() || p2_subst.is_some() {
                    Some(ProcX::par(
                        &p1_subst.unwrap_or(p1.clone()),
                        &p2_subst.unwrap_or(p2.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Debug(..) => None,
        }
    }

    /// Substitutes into a permission without modifying unchanged subtrees
    pub fn substitute(p: impl Borrow<Proc>, subst: &mut IndexMap<Var, Term>) -> Proc {
        Self::substitute_inplace(p.borrow(), subst).unwrap_or(p.borrow().clone())
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
        Spanned::new(PermissionX::Empty)
    }

    pub fn add(p1: impl Borrow<Permission>, p2: impl Borrow<Permission>) -> Permission {
        if p1.borrow().is_empty() {
            p2.borrow().clone()
        } else if p2.borrow().is_empty() {
            p1.borrow().clone()
        } else {
            Spanned::new(PermissionX::Add(p1.borrow().clone(), p2.borrow().clone()))
        }
    }

    pub fn sub(p1: impl Borrow<Permission>, p2: impl Borrow<Permission>) -> Permission {
        if p2.borrow().is_empty() {
            p1.borrow().clone()
        } else {
            Spanned::new(PermissionX::Sub(p1.borrow().clone(), p2.borrow().clone()))
        }
    }

    /// Returns Some if the term is substituted, None if unchanged
    fn substitute_inplace(perm: impl Borrow<Permission>, subst: &IndexMap<Var, Term>) -> Option<Permission> {
        match &perm.borrow().x {
            PermissionX::Empty => None,
            PermissionX::Add(p1, p2) => {
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if p1_subst.is_some() || p2_subst.is_some() {
                    Some(Spanned::spanned_option(perm.borrow().span, PermissionX::Add(
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
                    Some(Spanned::spanned_option(perm.borrow().span, PermissionX::Sub(
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
                    Some(Spanned::spanned_option(perm.borrow().span, PermissionX::Ite(
                        t_subst.unwrap_or(t.clone()),
                        p1_subst.unwrap_or(p1.clone()),
                        p2_subst.unwrap_or(p2.clone()),
                    )))
                } else {
                    None
                }
            }
            PermissionX::Fraction(frac, mut_ref) => {
                let mut_ref_subst = MutReferenceX::substitute_inplace(mut_ref, subst);
                if mut_ref_subst.is_some() {
                    Some(Spanned::spanned_option(perm.borrow().span, PermissionX::Fraction(*frac, mut_ref_subst.unwrap())))
                } else {
                    None
                }
            }
            PermissionX::Var(v, terms) => {
                let mut terms_subst = Vec::new();
                let mut modified = false;

                for term in terms {
                    let term_subst = TermX::substitute_inplace(term, subst);
                    if let Some(term_subst) = term_subst {
                        modified = true;
                        terms_subst.push(term_subst);
                    } else {
                        terms_subst.push(term.clone());
                    }
                }

                if modified {
                    Some(Spanned::spanned_option(perm.borrow().span, PermissionX::Var(v.clone(), terms_subst)))
                } else {
                    None
                }
            }
        }
    }

    /// Substitutes into a permission without modifying unchanged subtrees
    pub fn substitute(perm: impl Borrow<Permission>, subst: &IndexMap<Var, Term>) -> Permission {
        Self::substitute_inplace(perm.borrow(), subst).unwrap_or(perm.borrow().clone())
    }

    pub fn substitute_one(perm: impl Borrow<Permission>, var: impl Into<Var>, subterm: impl Borrow<Term>) -> Permission {
        PermissionX::substitute(perm, &IndexMap::from([ (var.into(), subterm.borrow().clone()) ]))
    }

    fn free_vars_inplace(&self, vars: &mut IndexSet<Var>) {
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
            PermissionX::Fraction(_, mut_ref) => {
                mut_ref.free_vars_inplace(vars);
            }
            PermissionX::Var(_, terms) => {
                for t in terms {
                    t.free_vars_inplace(vars);
                }
            }
        }
    }

    pub fn free_vars(&self) -> IndexSet<Var> {
        let mut vars = IndexSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }
}

impl ProcX {
    pub fn skip() -> Proc {
        Spanned::new(ProcX::Skip)
    }

    pub fn send(c: impl Into<ChanName>, t: impl Borrow<Term>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Send(c.into(), t.borrow().clone(), p.borrow().clone()))
    }

    pub fn recv(c: impl Into<ChanName>, v: impl Into<Var>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Recv(c.into(), v.into(), p.borrow().clone()))
    }

    pub fn write(m: impl Borrow<MutReference>, t: impl Borrow<Term>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Write(m.borrow().clone(), t.borrow().clone(), p.borrow().clone()))
    }

    pub fn read(m: impl Borrow<MutReference>, v: impl Into<Var>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Read(m.borrow().clone(), v.into(), p.borrow().clone()))
    }

    pub fn ite(t: impl Borrow<Term>, p1: impl Borrow<Proc>, p2: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Ite(t.borrow().clone(), p1.borrow().clone(), p2.borrow().clone()))
    }

    pub fn par(p1: impl Borrow<Proc>, p2: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Par(p1.borrow().clone(), p2.borrow().clone()))
    }

    pub fn call(name: impl Into<ProcName>, args: impl IntoIterator<Item=impl Borrow<Term>>) -> Proc {
        Spanned::new(ProcX::Call(name.into(), args.into_iter().map(|t| t.borrow().clone()).collect()))
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BaseType::Bool => write!(f, "bool"),
            BaseType::Int => write!(f, "int"),
            BaseType::Ref(ns, level) => if ns.len() == 1 {
                write!(f, "&{}{}", ns[0], "[*]".repeat(*level))
            } else {
                write!(f, "&{{{}}}{}", ns.iter().map(|n| n.0.as_ref()).collect::<Vec<&str>>().join(", "), "[*]".repeat(*level))
            }
        }
    }
}

impl fmt::Display for MutTypeX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutTypeX::Base(base) => write!(f, "{}", base),
            MutTypeX::Array(base) => write!(f, "[{}]", base),
        }
    }
}

impl fmt::Display for TermX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermX::Var(var) => write!(f, "{}", var),
            TermX::Const(c) => write!(f, "{}", c),
            TermX::Bool(b) => write!(f, "{}", b),
            TermX::Int(i) => write!(f, "{}", i),
            TermX::Ref(m) => write!(f, "&{}", m),
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
            MutReferenceX::Deref(t) =>
                if TermX::precedence(t) > 0 {
                    write!(f, "*{}", t)
                } else {
                    write!(f, "*({})", t)
                }
            MutReferenceX::Index(m, t) => write!(f, "{}[{}]", m, t),
            MutReferenceX::Slice(m, t1, t2) =>
                write!(
                    f, "{}[{}..{}]", m,
                    t1.as_ref().unwrap_or(&TermX::var("")),
                    t2.as_ref().unwrap_or(&TermX::var("")),
                ),
        }
    }
}

impl fmt::Display for PermissionX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermissionX::Empty => write!(f, "0"),
            PermissionX::Add(p1, p2) =>
                if match &p2.x {
                    PermissionX::Sub(..) => true,
                    _ => false,
                } {
                    write!(f, "{} + ({})", p1, p2)
                } else {
                    write!(f, "{} + {}", p1, p2)
                }
            PermissionX::Sub(p1, p2) =>
                if match &p2.x {
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
            PermissionX::Var(v, ts) => {
                write!(f, "{}(", v)?;
                for (i, t) in ts.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", t)?;
                    } else {
                        write!(f, ", {}", t)?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}
