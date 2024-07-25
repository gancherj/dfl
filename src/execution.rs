use std::fmt;
use std::rc::Rc;

use im::{vector, HashMap, Vector};
use indexmap::IndexSet;

use crate::ast::*;
use crate::error::{Error, SpannedError};
use crate::smt;

/**
 * All references, no matter their types, are using sort Ref
 *
 * We have overloaded functions (for any T in { Int, BV })
 * (declare-fun ref_index (Ref T) Ref)
 * (declare-fun ref_offset (Ref T) Ref)
 *
 * (declare-fun ref_read (<all mutables> Ref) T)
 *
 * For each mutable M
 * (declare-fun ref_write_M (<all mutables> Ref T) <type of M>)
 * (declare-const ref_base_M Ref)
 *
 * We leave these functions uninterpreted for now
 * For more exact semantics, we can axiomatize them separately
 */
const SMT_ENCODING_REF_SORT: &str = "Ref";
const SMT_ENCODING_REF_INDEX: &str = "ref_index";
const SMT_ENCODING_REF_OFFSET: &str = "ref_offset";
const SMT_ENCODING_REF_READ: &str = "ref_read";
const SMT_ENCODING_REF_WRITE: &str = "ref_write_";
const SMT_ENCODING_REF_BASE: &str = "ref_base_";

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
pub enum ProcState {
    Call(ProcName, Vector<smt::Term>),
    End,
}

#[derive(Debug, Clone)]
pub struct Configuration {
    pub ctx: Rc<Ctx>,
    pub consts: HashMap<Const, smt::Term>,
    pub muts: HashMap<MutName, smt::Term>,
    pub chans: HashMap<ChanName, ChanState>,
    pub procs: Vector<ProcState>,
    pub path_conditions: Vector<smt::Term>,
}

#[derive(Debug, Clone)]
pub enum ProcEvalResult {
    // Process is blocked, and the remaining process term, the modified configuration, and the additional path conditions are returned
    Partial(Proc, Configuration, Vector<smt::Term>),

    // Process hits another process call or skip
    Full(ProcState, Configuration),
}

#[derive(Debug, Clone)]
pub enum StepResult {
    Step(ProcName, Configuration),
    Terminal(Configuration),
}

impl MutTypeX {
    pub fn as_smt_sort(&self) -> smt::Sort {
        match self {
            MutTypeX::Base(base) => base.as_smt_sort(),
            MutTypeX::Array(idx, value) => {
                smt::SortX::array(idx.as_smt_sort(), value.as_smt_sort())
            }
        }
    }
}

impl TermTypeX {
    pub fn as_smt_sort(&self) -> smt::Sort {
        match self {
            TermTypeX::Base(typ) => typ.as_smt_sort(),
            TermTypeX::Ref(..) => smt::SortX::id(SMT_ENCODING_REF_SORT),
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

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn pop(&mut self) -> Option<smt::Term> {
        self.queue.pop_front()
    }

    pub fn push(&mut self, value: smt::Term) -> bool {
        if self.queue.len() >= self.bound {
            false
        } else {
            self.queue.push_back(value);
            true
        }
    }

    pub fn values(&self) -> impl Iterator<Item = &smt::Term> {
        self.queue.iter()
    }

    pub fn get(&self, idx: usize) -> Option<&smt::Term> {
        self.queue.get(idx)
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
    /**
     * Add SMT prelude to the encoding context (including declarations for
     * functions related to references)
     *
     * This should only be called once for each context
     */

//      * We have overloaded functions (for any T in { Int, BV })
//  * (declare-fun ref_index (Ref T) Ref)
//  * (declare-fun ref_offset (Ref T) Ref)
//  *
//  * (declare-fun ref_read (<all mutables> Ref) T)
//  *
//  * For each mutable M
//  * (declare-fun ref_write_M (<all mutables> Ref T) <type of M>)
//  * (declare-const ref_base_M Ref)
//  *
    pub fn gen_smt_prelude(ctx: &Ctx) -> Result<Vec<smt::Command>, Error> {
        let mut cmds = vec![
            smt::CommandX::declare_sort(SMT_ENCODING_REF_SORT, 0),
        ];
        let ref_sort = smt::SortX::id(SMT_ENCODING_REF_SORT);

        // A list of SMT sorts of all mutables
        let mutable_sorts =
            ctx.muts.values().map(|decl| decl.typ.as_smt_sort()).collect::<Vec<_>>();

        // A set of SMT sorts of base types of mutables
        let mutable_base_sorts =
            ctx.muts.values().map(|decl| decl.typ.get_base().as_smt_sort()).collect::<IndexSet<_>>();

        for base_sort in mutable_base_sorts.iter() {
            cmds.push(smt::CommandX::declare_fun(SMT_ENCODING_REF_INDEX, [ &ref_sort, base_sort ], &ref_sort));
            cmds.push(smt::CommandX::declare_fun(SMT_ENCODING_REF_OFFSET, [ &ref_sort, base_sort ], &ref_sort));
            cmds.push(smt::CommandX::declare_fun(SMT_ENCODING_REF_READ, mutable_sorts.iter().chain([ &ref_sort ]), base_sort));

            for decl in ctx.muts.values() {
                cmds.push(smt::CommandX::declare_fun(
                    &format!("{}{}", SMT_ENCODING_REF_WRITE, decl.name),
                    mutable_sorts.iter().chain([ &ref_sort, base_sort ]),
                    decl.typ.as_smt_sort(),
                ));
            }

            for decl in ctx.muts.values() {
                cmds.push(smt::CommandX::declare_const(&format!("{}{}", SMT_ENCODING_REF_BASE, decl.name), &ref_sort));
            }
        }

        Ok(cmds)
    }

    /**
     * Create an initial configuration based on a context and entry process
     */
    pub fn new(
        smt_ctx: &mut smt::EncodingCtx,
        ctx: &Rc<Ctx>,
        entry: impl Into<ProcName>,
        chan_bound: usize,
    ) -> Result<Configuration, Error> {
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
        let entry_proc = ctx
            .procs
            .get(&entry_name)
            .ok_or(format!("entry process {} not found", &entry_name))?;

        if !entry_proc.params.is_empty() {
            Err(format!(
                "entry process {} should not have parameters",
                &entry_name
            ))?;
        }

        let mut config = Configuration {
            ctx: ctx.clone(),
            consts,
            muts,
            chans,
            procs: Vector::new(),
            path_conditions: Vector::new(),
        };

        config.procs = config.decompose_parallels(&entry_proc.body)?;

        Ok(config)
    }

    /**
     * Assume the body is a parallel composition of process calls (or skip),
     * extract a list of process states from the composition.
     */
    fn decompose_parallels(&self, proc: &Proc) -> Result<Vector<ProcState>, SpannedError> {
        match &proc.x {
            ProcX::Skip => Ok(Vector::new()),
            ProcX::Call(name, args) => Ok(vector![ProcState::Call(
                name.clone(),
                args.iter()
                    .map(|arg| self.eval_term(&HashMap::new(), arg))
                    .collect::<Result<Vector<smt::Term>, SpannedError>>()?,
            )]),
            ProcX::Par(left, right) => {
                let mut left_procs = self.decompose_parallels(left)?;
                let right_procs = self.decompose_parallels(right)?;
                left_procs.append(right_procs);
                Ok(left_procs)
            }
            _ => SpannedError::new_err(format!(
                "expecting parallel composition or process call, got {}",
                proc
            )),
        }
    }

    pub fn eval_mut_ref(
        &self,
        local: &HashMap<Var, smt::Term>,
        mut_ref: &MutReference,
    ) -> Result<smt::Term, SpannedError>
    {
        match &mut_ref.x {
            MutReferenceX::Base(name) => Ok(smt::TermX::var(format!("{}{}", SMT_ENCODING_REF_BASE, name))),
            MutReferenceX::Deref(term) => self.eval_term(local, term),
            MutReferenceX::Index(base, idx) =>
                Ok(smt::TermX::app(
                    SMT_ENCODING_REF_INDEX,
                    [self.eval_mut_ref(local, base)?, self.eval_term(local, idx)?],
                )),
            MutReferenceX::Slice(base, None, ..) => self.eval_mut_ref(local, base),
            MutReferenceX::Slice(base, Some(offset), ..) =>
                Ok(smt::TermX::app(
                    SMT_ENCODING_REF_OFFSET,
                    [self.eval_mut_ref(local, base)?, self.eval_term(local, offset)?],
                )),
        }
    }

    // TODO: merge with TermX::as_smt_term
    pub fn eval_term(
        &self,
        local: &HashMap<Var, smt::Term>,
        term: &Term,
    ) -> Result<smt::Term, SpannedError> {
        match &term.x {
            TermX::Var(v) => local.get(v).cloned().ok_or(SpannedError::spanned(
                &term.span,
                format!("undefined variable {v}"),
            )),
            TermX::Const(c) => self.consts.get(c).cloned().ok_or(SpannedError::spanned(
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
            TermX::Ref(mut_ref) => self.eval_mut_ref(local, mut_ref),
            TermX::Add(t1, t2) => Ok(smt::TermX::add(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVAdd(t1, t2) => Ok(smt::TermX::bvadd(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVSub(t1, t2) => Ok(smt::TermX::bvsub(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVMul(t1, t2) => Ok(smt::TermX::bvmul(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVSHL(t1, t2) => Ok(smt::TermX::bvshl(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVFSHL(t1, t2, t3, w) => Ok(smt::TermX::bvfshl(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
                self.eval_term(local, t3)?,
                *w,
            )),
            TermX::BVASHR(t1, t2) => Ok(smt::TermX::bvashr(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVLSHR(t1, t2) => Ok(smt::TermX::bvlshr(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVAnd(t1, t2) => Ok(smt::TermX::bvand(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVOr(t1, t2) => Ok(smt::TermX::bvor(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVXor(t1, t2) => Ok(smt::TermX::bvxor(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::Mul(t1, t2) => Ok(smt::TermX::mul(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::Less(t1, t2) => Ok(smt::TermX::lt(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVULT(t1, t2) => Ok(smt::TermX::bvult(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVUGT(t1, t2) => Ok(smt::TermX::bvugt(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVULE(t1, t2) => Ok(smt::TermX::bvule(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVUGE(t1, t2) => Ok(smt::TermX::bvuge(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVSLT(t1, t2) => Ok(smt::TermX::bvslt(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVSGT(t1, t2) => Ok(smt::TermX::bvsgt(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVSLE(t1, t2) => Ok(smt::TermX::bvsle(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::BVSGE(t1, t2) => Ok(smt::TermX::bvsge(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::And(t1, t2) => Ok(smt::TermX::and([
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            ])),
            TermX::Equal(t1, t2) => Ok(smt::TermX::eq(
                self.eval_term(local, t1)?,
                self.eval_term(local, t2)?,
            )),
            TermX::Not(t) => Ok(smt::TermX::not(self.eval_term(local, t)?)),
        }
    }

    /**
     * Read the value of the mutable reference
     */
    fn eval_mut_ref_read(
        &self,
        local: &HashMap<Var, smt::Term>,
        mut_ref: &MutReference,
    ) -> Result<smt::Term, SpannedError> {
        Ok(smt::TermX::app(
            SMT_ENCODING_REF_READ,
            // TODO: error if keys not found?
            // All mutables followed by the reference
            self.ctx.muts.keys().filter_map(|name| {
                self.muts.get(name).cloned()
            }).chain([self.eval_mut_ref(local, mut_ref)?]),
        ))
    }

    /**
     * Return an updated array/base term expressing the update mutable value
     *
     * e.g. mut A: [[[int]]]
     * write x -> A[a][b][c]
     * ==>
     * (store A a
     * (store (select A a) b
     * (store (select (select A a) b) c x)))
     */
    fn eval_mut_ref_write(
        &mut self,
        local: &HashMap<Var, smt::Term>,
        mut_ref: &MutReference,
        value: &smt::Term,
    ) -> Result<(), SpannedError> {
        let mut_ref_smt = self.eval_mut_ref(local, mut_ref)?;
        for name in self.ctx.muts.keys() {
            self.muts.insert(name.clone(), smt::TermX::app(
                format!("{}{}", SMT_ENCODING_REF_WRITE, name),
                // All mutables followed by the reference and the updated value
                self.ctx.muts.keys().map(|name| {
                    self.muts.get(name).unwrap().clone()
                }).chain([
                    mut_ref_smt.clone(),
                    value.clone(),
                ]),
            ));
        }
        Ok(())
    }

    fn eval_proc(
        &self,
        local: &mut HashMap<Var, smt::Term>,
        proc: &Proc,
    ) -> Result<Vector<ProcEvalResult>, Error> {
        self.clone().eval_proc_helper(self, local, proc)
    }

    /**
     * Execute a process until
     * - Skip
     * - Another process call
     * - Blocked recv/send
     * (without checking feasibility of path conditions)
     */
    fn eval_proc_helper(
        mut self,
        old_config: &Configuration,
        local: &mut HashMap<Var, smt::Term>,
        proc: &Proc,
    ) -> Result<Vector<ProcEvalResult>, Error> {
        match &proc.x {
            ProcX::Skip => Ok(vector![ProcEvalResult::Full(ProcState::End, self)]),

            ProcX::Send(name, term, cont) => {
                let value = self.eval_term(local, term)?;
                let chan = self
                    .chans
                    .get_mut(name)
                    .ok_or(format!("channel {} not found", name))?;
                if chan.push(value) {
                    Ok(self.eval_proc_helper(old_config, local, cont)?)
                } else {
                    // Blocked
                    let new_path_conditions = self
                        .path_conditions
                        .split_off(old_config.path_conditions.len());
                    Ok(vector![ProcEvalResult::Partial(
                        proc.clone(),
                        self,
                        new_path_conditions
                    )])
                }
            }

            ProcX::Recv(name, var, cont) => {
                let chan = self
                    .chans
                    .get_mut(name)
                    .ok_or(format!("channel {} not found", name))?;
                match chan.pop() {
                    None => {
                        let new_path_conditions = self
                            .path_conditions
                            .split_off(old_config.path_conditions.len());
                        Ok(vector![ProcEvalResult::Partial(
                            proc.clone(),
                            self,
                            new_path_conditions
                        )])
                    }
                    Some(value) => {
                        local.insert(var.clone(), value);
                        Ok(self.eval_proc_helper(old_config, local, cont)?)
                    }
                }
            }

            ProcX::Write(mut_ref, term, cont) => {
                // let (name, updated) =
                //     self.eval_mut_ref_write(local, mut_ref, &self.eval_term(local, term)?)?;
                // self.muts.insert(name, updated);
                self.eval_mut_ref_write(local, mut_ref, &self.eval_term(local, term)?)?;
                Ok(self.eval_proc_helper(old_config, local, cont)?)
            }

            ProcX::Read(mut_ref, var, cont) => {
                let value = self.eval_mut_ref_read(local, mut_ref)?;
                local.insert(var.clone(), value);
                Ok(self.eval_proc_helper(old_config, local, cont)?)
            }

            ProcX::Ite(t, p1, p2) => {
                let mut copy = self.clone();
                let mut local_copy = local.clone();
                self.path_conditions.push_back(self.eval_term(local, t)?);
                copy.path_conditions
                    .push_back(smt::TermX::not(self.eval_term(local, t)?));
                Ok(self.eval_proc_helper(old_config, local, p1)?
                    + copy.eval_proc_helper(old_config, &mut local_copy, p2)?)
            }

            ProcX::Call(name, args) => Ok(vector![ProcEvalResult::Full(
                ProcState::Call(
                    name.clone(),
                    args.iter()
                        .map(|arg| self.eval_term(local, arg))
                        .collect::<Result<Vector<smt::Term>, SpannedError>>()?,
                ),
                self
            )]),
            ProcX::Par(..) => Err(format!(
                "parallel composition only allowed at the top level"
            ))?,
        }
    }

    pub fn eval_proc_state(&self, proc_state: &ProcState) -> Result<Vector<ProcEvalResult>, Error> {
        match proc_state {
            ProcState::End => Ok(vector![]),
            ProcState::Call(proc_name, proc_args) => {
                let mut local = HashMap::new();

                let proc_decl = self
                    .ctx
                    .procs
                    .get(proc_name)
                    .ok_or(format!("process {} not found", proc_name))?;

                assert!(proc_decl.params.len() == proc_args.len());

                for (param, arg) in proc_decl.params.iter().zip(proc_args.iter()) {
                    local.insert(param.name.clone(), arg.clone());
                }

                self.eval_proc(&mut local, &proc_decl.body)
            }
        }
    }

    /**
     * Return true iff the path condition is satisfiable
     */
    pub fn feasible(&self, solver: &mut smt::Solver) -> Result<smt::CheckSatResult, Error> {
        solver.push()?;
        solver.assert(smt::TermX::and(&self.path_conditions))?;
        let result = solver.check_sat()?;
        solver.pop()?;
        Ok(result)
    }

    /**
     * Search for a process that can run until the next process call.
     * If we hit branching where one branch cannot make progress,
     * we continue searching for a process in the branch without progress.
     */
    pub fn step_one_proc(&self) -> Result<Vector<StepResult>, Error> {
        let mut config = self.clone();

        let mut stepped_branches = Vector::new();

        for (i, proc_state) in self.procs.iter().enumerate() {
            if let ProcState::Call(proc_name, ..) = proc_state {
                let results = config.eval_proc_state(proc_state)?;
                assert!(results.len() > 0);

                // If the results are all partial, then none of the branches can make progress until a call
                // so we just move on to the next process while restoring the path conditions
                if results.iter().all(|r| match r {
                    ProcEvalResult::Partial(..) => true,
                    _ => false,
                }) {
                    continue;
                }

                // All partial branches can be merged together, with the new path condition being the disjunction
                // of new path conditions in each partial branch
                let partial_condition = smt::TermX::or(results.iter().filter_map(|r| match r {
                    // Take the conjunction of all new path conditions (compared to config.path_conditions)
                    ProcEvalResult::Partial(_, _, new_path_conditions) => {
                        Some(smt::TermX::and(new_path_conditions))
                    }
                    _ => None,
                }));

                // Other full/end results can be collected into stepped_branches
                let mut has_partial = false;
                for result in results {
                    match result {
                        ProcEvalResult::Full(new_proc_state, mut new_config) => {
                            // Update process state
                            new_config.procs[i] = new_proc_state;
                            stepped_branches
                                .push_back(StepResult::Step(proc_name.clone(), new_config));
                        }
                        _ => {
                            has_partial = true;
                        }
                    }
                }

                if !has_partial {
                    break;
                }

                if i == self.procs.len() - 1 {
                    // Under partial_condition, the original config (self)
                    // cannot make progress on any process, so we conclude
                    // it is terminal
                    stepped_branches.push_back(StepResult::Terminal(self.clone()));
                } else {
                    // Continue with the union of all partial branches
                    config.path_conditions.push_back(partial_condition);
                }
            }
        }

        Ok(stepped_branches)
    }
}

impl fmt::Display for ChanState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (i, value) in self.queue.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", value)?;
            } else {
                write!(f, ", {}", value)?;
            }
        }
        write!(f, "] (max {})", self.bound)
    }
}

impl fmt::Display for ProcState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProcState::Call(name, args) => write!(
                f,
                "{}({})",
                name,
                args.iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ProcState::End => write!(f, "skip"),
        }
    }
}

impl fmt::Display for Configuration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Configuration {{")?;

        for name in self.ctx.consts.keys() {
            writeln!(f, "  const {} => {}", name, self.consts[name])?;
        }

        for name in self.ctx.muts.keys() {
            writeln!(f, "  mut {} => {}", name, self.muts[name])?;
        }

        for name in self.ctx.chans.keys() {
            writeln!(f, "  chan {} => {}", name, self.chans[name])?;
        }

        writeln!(
            f,
            "  proc {}",
            self.procs
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" || ")
        )?;

        for condition in self.path_conditions.iter() {
            writeln!(f, "  constraint {}", condition)?;
        }

        write!(f, "}}")
    }
}

impl fmt::Display for StepResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StepResult::Step(name, config) => write!(f, "Step({}, {})", name, config),
            StepResult::Terminal(config) => write!(f, "Terminal({})", config),
        }
    }
}
