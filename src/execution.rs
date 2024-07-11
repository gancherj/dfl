use std::hash::Hash;
use std::rc::Rc;

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
    pub ctx: Rc<Ctx>,
    pub consts: HashMap<Const, smt::Term>,
    pub muts: HashMap<MutName, smt::Term>,
    pub chans: HashMap<ChanName, ChanState>,
    pub procs: Vector<ProcState>,
    pub path_condition: Vector<smt::Term>,
}

#[derive(Debug, Clone)]
pub enum EvalResult {
    // Process is blocked, and the remaining process term is returned
    Partial(Proc, Configuration),

    // Process hits another process call
    Full(ProcState, Configuration),

    // Process hits skip
    End(Configuration),
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
     * Create an initial configuration based on a context and entry process
     */
    pub fn new(smt_ctx: &mut smt::EncodingCtx, ctx: &Rc<Ctx>, entry: impl Into<ProcName>, chan_bound: usize) -> Result<Configuration, Error> {
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

        let mut config = Configuration {
            ctx: ctx.clone(),
            consts,
            muts,
            chans,
            procs: Vector::new(),
            path_condition: Vector::new(),
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
            ProcX::Call(name, args) =>
                Ok(vector![ProcState {
                    name: name.clone(),
                    args: args.iter().map(|arg| self.eval_term(&HashMap::new(), arg))
                        .collect::<Result<Vector<smt::Term>, SpannedError>>()?,
                }]),
            ProcX::Par(left, right) => {
                let mut left_procs = self.decompose_parallels(left)?;
                let right_procs = self.decompose_parallels(right)?;
                left_procs.append(right_procs);
                Ok(left_procs)
            },
            _ => SpannedError::new_err(format!("expecting parallel composition or process call, got {}", proc)),
        }
    }

    // TODO: merge with TermX::as_smt_term
    pub fn eval_term(&self, local: &HashMap<Var, smt::Term>, term: &Term) -> Result<smt::Term, SpannedError> {
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
            TermX::Ref(..) => unimplemented!("reference"),
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
    fn eval_mut_ref_read(&self, local: &HashMap<Var, smt::Term>, mut_ref: &MutReference) -> Result<smt::Term, SpannedError> {
        match &mut_ref.x {
            MutReferenceX::Base(name) => self.muts.get(name).cloned().ok_or(SpannedError::spanned(
                &mut_ref.span,
                format!("mutable {} not found", name),
            )),
            MutReferenceX::Deref(..) => unimplemented!("dereference"),
            MutReferenceX::Index(mut_ref, idx) =>
                Ok(smt::TermX::select(
                    self.eval_mut_ref_read(local, mut_ref)?,
                    self.eval_term(local, idx)?,
                )),
            MutReferenceX::Slice(..) => unimplemented!("slice"),
        }
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
    fn eval_mut_ref_write(&self, local: &HashMap<Var, smt::Term>, mut_ref: &MutReference, value: &smt::Term) -> Result<(MutName, smt::Term), SpannedError> {
        match &mut_ref.x {
            MutReferenceX::Base(name) => Ok((name.clone(), value.clone())),
            MutReferenceX::Deref(..) => unimplemented!("dereference"),
            MutReferenceX::Index(mut_ref, idx) => {
                self.eval_mut_ref_write(
                    local, mut_ref,
                    &smt::TermX::store(
                        self.eval_mut_ref_read(local, mut_ref)?,
                        self.eval_term(local, idx)?,
                        value,
                    ),
                )
            },
            MutReferenceX::Slice(..) => unimplemented!("slice"),
        }
    }

    /**
     * Execute a process until
     * - Skip
     * - Another process call
     * - Blocked recv/send
     * (without checking feasibility of path conditions)
     */
    fn eval_proc(mut self, local: &mut HashMap<Var, smt::Term>, proc: &Proc) -> Result<Vector<EvalResult>, Error> {
        match &proc.x {
            ProcX::Skip => Ok(vector![EvalResult::End(self)]),

            ProcX::Send(name, term, cont) => {
                let value = self.eval_term(local, term)?;
                let chan = self.chans.get_mut(name).ok_or(format!("channel {} not found", name))?;
                if chan.push(value) {
                    Ok(self.eval_proc(local, cont)?)
                } else {
                    // Blocked
                    Ok(vector![EvalResult::Partial(proc.clone(), self)])
                }
            },

            ProcX::Recv(name, var, cont) => {
                let chan = self.chans.get_mut(name).ok_or(format!("channel {} not found", name))?;
                match chan.pop() {
                    None => Ok(vector![EvalResult::Partial(proc.clone(), self)]),
                    Some(value) => {
                        local.insert(var.clone(), value);
                        Ok(self.eval_proc(local, cont)?)
                    }
                }
            },

            ProcX::Write(mut_ref, term, cont) => {
                let (name, updated) = self.eval_mut_ref_write(local, mut_ref, &self.eval_term(local, term)?)?;
                self.muts.insert(name, updated);
                Ok(self.eval_proc(local, cont)?)
            },

            ProcX::Read(mut_ref, var, cont) => {
                let value = self.eval_mut_ref_read(local, mut_ref)?;
                local.insert(var.clone(), value);
                Ok(self.eval_proc(local, cont)?)
            },

            ProcX::Ite(t, p1, p2) => {
                let mut copy = self.clone();
                self.path_condition.push_back(self.eval_term(local, t)?);
                copy.path_condition.push_back(smt::TermX::not(self.eval_term(local, t)?));
                Ok(self.eval_proc(local, p1)? + copy.eval_proc(local, p2)?)
            },

            ProcX::Call(name, args) =>
                Ok(vector![EvalResult::Full(ProcState {
                    name: name.clone(),
                    args: args.iter().map(|arg| self.eval_term(local, arg))
                        .collect::<Result<Vector<smt::Term>, SpannedError>>()?,
                }, self)]),
            ProcX::Par(..) => Err(format!("parallel composition only allowed at the top level"))?,
        }
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
            let mut local = HashMap::new();

            let proc_decl = self.ctx.procs.get(&proc_state.name)
                .ok_or(format!("process {} not found", proc_state.name))?;

            assert!(proc_decl.params.len() == proc_state.args.len());

            for (param, arg) in proc_decl.params.iter().zip(proc_state.args.iter()) {
                local.insert(param.name.clone(), arg.clone());
            }

            let results = config.clone().eval_proc(&mut local, &proc_decl.body)?;
            assert!(results.len() > 0);

            // If the results are all partial, then none of the branches can make progress until a call
            // so we just move on to the next process while restoring the path conditions
            if results.iter().all(|r| match r { EvalResult::Partial(..) => true, _ => false, }) {
                continue;
            }

            // All partial branches can be merged together, with the new path condition being the disjunction
            // of new path conditions in each partial branch
            let partial_condition = smt::TermX::or(
                results.iter().filter_map(|r| match r {
                    // Take the conjunction of all new path conditions (compared to config.path_condition)
                    EvalResult::Partial(_, new_config) => Some(
                        smt::TermX::and(new_config.path_condition.iter().skip(config.path_condition.len()))
                    ),
                    _ => None,
                })
            );

            // Other full/end results can be collected into stepped_branches
            let mut has_partial = false;
            for result in results {
                match result {
                    EvalResult::Full(new_proc_state, mut new_config) => {
                        // Update process state
                        new_config.procs[i] = new_proc_state;
                        stepped_branches.push_back(StepResult::Step(proc_state.name.clone(), new_config));
                    },
                    EvalResult::End(mut new_config) => {
                        // Remove the process state as it has finished
                        new_config.procs.remove(i);
                        stepped_branches.push_back(StepResult::Step(proc_state.name.clone(), new_config));
                    },
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
                config.path_condition.push_back(partial_condition);
            }
        }

        Ok(stepped_branches)
    }
}
