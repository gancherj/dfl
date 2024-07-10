use std::hash::Hash;

use im::{Vector, vector, HashMap};

use crate::ast::*;
use crate::error::{Error, SpannedError};
use crate::smt;

#[derive(Debug, Clone)]
pub struct ChanState {
    pub bound: usize,
    pub queue: Vector<smt::Term>,
}

#[derive(Debug, Clone)]
/**
 * We do not allow arbitrary process term to
 * be used as intermediate state. In a sense,
 * the body of a process definition is "atomic."
 *
 * If one wants fine-grained control over where
 * "context-switching" can happen, one can split
 * statements into multiple process definitions.
 */
pub struct ProcState {
    pub name: ProcName,
    pub args: Vector<smt::Term>,
}

#[derive(Debug, Clone)]
pub struct Configuration {
    pub consts: HashMap<Const, smt::Term>,
    pub muts: HashMap<MutName, smt::Term>,
    pub chans: HashMap<ChanName, ChanState>,
    pub procs: Vector<ProcState>,
    pub path_condition: Vector<smt::Term>,
}

impl MutTypeX {
    pub fn as_smt_sort(&self) -> smt::Sort {
        match self {
            MutTypeX::Base(base) => base.as_smt_sort(),
            MutTypeX::Array(idx, value) => smt::SortX::array(idx.as_smt_sort(), value.as_smt_sort()),
        }
    }
}

impl ChanState {
    pub fn new(bound: usize) -> ChanState {
        ChanState {
            bound,
            queue: Vector::new(),
        }
    }
}

/**
 * Encoding of references in SMT
 *
 * Suppose we have mutables
 * mut A: array(t1, array(t2, t3))
 * mut B: array(t4, t5)
 * mut C: t6
 * where ti's are base types
 *
 * Then we define the reference sort as
 * (declare-datatype Ref (
 *   (ref2-A (ref2-A-idx1 t1) (ref-A-idx2 t2))
 *   (ref1-A (ref1-A-idx1 t1))
 *   (ref0-A)
 *   (ref1-B (ref1-B-idx1 t4))
 *   (ref0-B)
 *   (ref0-C)
 * ))
 *
 * MutReference is interpreted as:
 * Base(M) => ref0-M
 * Deref(t) => t
 * Index(r, t) => (match r (case (ref1-A i1) (ref2-A i1 t)) ...)
 * Slice(r, t) => (match r (case (ref1-A i1) (ref1-A (+ i1 t))) ...)
 */

impl Configuration {
    // TODO: merge with TermX::as_smt_term
    pub fn interpret_term(consts: &HashMap<Const, smt::Term>, local: &HashMap<Var, smt::Term>, term: &Term) -> Result<smt::Term, SpannedError> {
        match &term.x {
            TermX::Var(v) => local.get(v).cloned().ok_or(SpannedError::spanned(
                &term.span,
                format!("undefined variable {v}"),
            )),
            TermX::Const(c) => consts.get(c).cloned().ok_or(SpannedError::spanned(
                &term.span,
                format!("undefined constant {c}"),
            )),
            TermX::Bool(b) => Ok(smt::TermX::bool(*b)),
            TermX::Int(i) => {
                if *i >= 0 {
                    Ok(smt::TermX::int(*i as u64))
                } else {
                    Ok(smt::TermX::neg(smt::TermX::int(-i as u64)))
                }
            }
            TermX::BitVec(i, w) => Ok(smt::TermX::bit_vec(*i, *w)),
            TermX::Ref(..) => unimplemented!("reference"),
            TermX::Add(t1, t2) => Ok(smt::TermX::add(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVAdd(t1, t2) => Ok(smt::TermX::bvadd(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVSub(t1, t2) => Ok(smt::TermX::bvsub(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVMul(t1, t2) => Ok(smt::TermX::bvmul(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVSHL(t1, t2) => Ok(smt::TermX::bvshl(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVASHR(t1, t2) => Ok(smt::TermX::bvashr(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVLSHR(t1, t2) => Ok(smt::TermX::bvlshr(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVAnd(t1, t2) => Ok(smt::TermX::bvand(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVOr(t1, t2) => Ok(smt::TermX::bvor(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVXor(t1, t2) => Ok(smt::TermX::bvxor(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::Mul(t1, t2) => Ok(smt::TermX::mul(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::Less(t1, t2) => Ok(smt::TermX::lt(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVULT(t1, t2) => Ok(smt::TermX::bvult(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVUGT(t1, t2) => Ok(smt::TermX::bvugt(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVULE(t1, t2) => Ok(smt::TermX::bvule(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVUGE(t1, t2) => Ok(smt::TermX::bvuge(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVSLT(t1, t2) => Ok(smt::TermX::bvslt(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVSGT(t1, t2) => Ok(smt::TermX::bvsgt(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVSLE(t1, t2) => Ok(smt::TermX::bvsle(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::BVSGE(t1, t2) => Ok(smt::TermX::bvsge(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::And(t1, t2) => Ok(smt::TermX::and([
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            ])),
            TermX::Equal(t1, t2) => Ok(smt::TermX::eq(
                Configuration::interpret_term(consts, local, t1)?,
                Configuration::interpret_term(consts, local, t2)?,
            )),
            TermX::Not(t) => Ok(smt::TermX::not(Configuration::interpret_term(consts, local, t)?)),
        }
    }

    /**
     * Assume the body is a parallel composition of process calls (or skip),
     * extract a list of process states from the composition.
     */
    fn decompose_parallels(consts: &HashMap<Const, smt::Term>, proc: &Proc) -> Result<Vector<ProcState>, SpannedError> {
        match &proc.x {
            ProcX::Skip => Ok(Vector::new()),
            ProcX::Call(name, args) =>
                Ok(vector![ProcState {
                    name: name.clone(),
                    args: args.iter().map(|arg| Configuration::interpret_term(consts, &HashMap::new(), arg))
                        .collect::<Result<Vector<smt::Term>, SpannedError>>()?,
                }]),
            ProcX::Par(left, right) => {
                let mut left_procs = Configuration::decompose_parallels(consts, left)?;
                let right_procs = Configuration::decompose_parallels(consts, right)?;
                left_procs.append(right_procs);
                Ok(left_procs)
            },
            _ => SpannedError::new_err(format!("expecting parallel composition or process call, got {}", proc)),
        }
    }

    /**
     * Create an initial configuration based on a context and entry process
     */
    pub fn new(smt_ctx: &mut smt::EncodingCtx, ctx: &Ctx, entry: impl Into<ProcName>, chan_bound: usize) -> Result<Configuration, Error> {
        let mut consts = HashMap::new();
        let mut muts = HashMap::new();
        let mut chans = HashMap::new();

        for decl in ctx.consts.values() {
            let ident = smt_ctx.fresh_const(format!("const_{}", decl.name), decl.typ.as_smt_sort());
            consts.insert(decl.name.clone(), smt::TermX::var(ident));
        }

        for decl in ctx.muts.values() {
            let ident = smt_ctx.fresh_const(format!("mut_{}", decl.name), decl.typ.as_smt_sort());
            muts.insert(decl.name.clone(), smt::TermX::var(ident));

        }

        for decl in ctx.chans.values() {
            chans.insert(decl.name.clone(), ChanState::new(chan_bound));
        }

        let entry_name: ProcName = entry.into();
        let entry_proc = ctx.procs.get(&entry_name).ok_or(format!("entry process {} not found", &entry_name))?;

        if !entry_proc.params.is_empty() {
            Err(format!("entry process {} should not have parameters", &entry_name))?;
        }

        let procs = Configuration::decompose_parallels(&consts, &entry_proc.body)?;

        Ok(Configuration {
            consts,
            muts,
            chans,
            procs,
            path_condition: Vector::new(),
        })
    }
}
