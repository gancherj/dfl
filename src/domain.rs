use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;
use std::hash::{Hash, Hasher};

use im;

use crate::ast::*;
use crate::error::Error;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum BoolDomainValue {
    True,
    False,
    Top,
}

pub trait Domain {
    type Value: Clone + fmt::Display + Eq + PartialEq + Hash;

    fn interpret(&mut self, local: &im::HashMap<Var, Self::Value>, term: &Term) -> Result<Self::Value, Error>;
    fn get_top(&mut self) -> Self::Value;
    fn test_bool(&mut self, value: &Self::Value) -> Result<BoolDomainValue, Error>;
    fn less_equal(&mut self, v1: &Self::Value, v2: &Self::Value) -> Result<bool, Error>;
}

pub struct ChanState<D: Domain> {
    pub bound: usize,
    pub queue: im::Vector<D::Value>,
}

/**
 * We do not allow arbitrary process term to
 * be used as intermediate state. In a sense,
 * the body of a process definition is "atomic."
 *
 * If one wants fine-grained control over where
 * "context-switching" can happen, one can split
 * statements into multiple process definitions.
 */
pub enum ProcState<D: Domain> {
    Call(ProcName, im::Vector<D::Value>),
    Stop,
}

pub type ChanIndex = usize;

pub struct Configuration<D: Domain> {
    pub ctx: Rc<Ctx>,
    pub chan_to_index: Rc<HashMap<ChanName, ChanIndex>>,
    pub index_to_chan: Rc<Vec<ChanName>>,

    pub chans: im::Vector<ChanState<D>>,
    pub procs: im::Vector<ProcState<D>>,
}

pub enum ProcEvalResult<D: Domain> {
    // Process is blocked, and the remaining process term, the modified configuration, and the additional path conditions are returned
    Partial(Proc, Configuration<D>),

    // Process hits another process call or skip
    Full(ProcState<D>, Configuration<D>),
}

pub struct StepResult<D: Domain>(ProcName, Configuration<D>);

pub struct WaitDependencyGraph {
    edges: HashMap<ProcName, HashSet<ProcName>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Shape {
    chans: Vec<usize>,
    procs: Vec<Option<ProcName>>, // Some if the process is alive, otherwise None
}

impl<D: Domain> ChanState<D> {
    pub fn new(bound: usize) -> ChanState<D> {
        ChanState {
            bound,
            queue: im::Vector::new(),
        }
    }

    pub fn pop(&mut self) -> Option<D::Value> {
        self.queue.pop_front()
    }

    pub fn push(&mut self, value: D::Value) -> bool {
        if self.queue.len() >= self.bound {
            false
        } else {
            self.queue.push_back(value);
            true
        }
    }
}

impl ProcX {
    /// Decompose parallel compositions into processes not starting with Par
    fn decompose_parallels(proc: &Proc) -> Vec<Proc> {
        let mut procs = Vec::new();
        let mut stack = Vec::new();

        stack.push(proc);

        while let Some(proc) = stack.pop() {
            match &proc.x {
                ProcX::Par(p1, p2) => {
                    stack.push(p2);
                    stack.push(p1);
                }
                _ => procs.push(proc.clone()),
            }
        }

        procs
    }
}

impl<D: Domain> Configuration<D> {
    pub fn new(ctx: &Rc<Ctx>, domain: &mut D, entry: impl Into<ProcName>, chan_bound: usize) -> Result<Configuration<D>, Error> {
        let mut procs = im::Vector::new();

        let entry_name = entry.into();
        let entry_decl = ctx.procs.get(&entry_name)
            .ok_or(format!("entry process {} not found", &entry_name))?;

        if entry_decl.params.len() > 0 {
            Err(format!("entry process {} should not have parameters", &entry_name))?;
        }

        // Decompose the top level parallel composition
        for proc in ProcX::decompose_parallels(&entry_decl.body) {
            match &proc.x {
                ProcX::Stop => {}
                ProcX::Call(name, args) => {
                    procs.push_back(ProcState::Call(
                        name.clone(),
                        // Abstract each argument
                        args.iter().map(|t| domain.interpret(&im::HashMap::new(), t))
                            .collect::<Result<im::Vector<_>, _>>()?,
                    ));
                }
                _ => Err(format!("entry process {} should be a parallel composition of process calls or stop", &entry_name))?,
            }
        }

        Ok(Configuration {
            ctx: ctx.clone(),
            chan_to_index: Rc::new(ctx.chans.keys().enumerate().map(|(i, name)| (name.clone(), i)).collect()),
            index_to_chan: Rc::new(ctx.chans.keys().cloned().collect()),
            chans: ctx.chans.values().map(|_| ChanState::new(chan_bound)).collect(),
            procs,
        })
    }

    fn get_mut_chan_state(&mut self, name: &ChanName) -> Result<&mut ChanState<D>, Error> {
        let idx = self.chan_to_index.get(name)
            .ok_or(format!("channel {} not found", name))?;
        Ok(self.chans.get_mut(*idx).ok_or("configuration invariant violated".to_string())?)
    }

    /**
     * Execute a process until
     * - Stop
     * - Another process call
     * - Blocked recv/send
     */
    fn eval_proc(
        mut self,
        domain: &mut D,
        local: &mut im::HashMap<Var, D::Value>,
        proc: &Proc,
        results: &mut Vec<ProcEvalResult<D>>,
    ) -> Result<(), Error> {
        match &proc.x {
            ProcX::Stop => {
                results.push(ProcEvalResult::Full(ProcState::Stop, self));
                Ok(())
            }

            ProcX::Send(name, term, cont) => {
                let value = domain.interpret(local, term)?;
                let chan = self.get_mut_chan_state(name)?;
                if chan.push(value) {
                    self.eval_proc(domain, local, cont, results)
                } else {
                    results.push(ProcEvalResult::Partial(proc.clone(), self));
                    Ok(())
                }
            }

            ProcX::Recv(name, var, cont) => {
                let chan = self.get_mut_chan_state(name)?;
                match chan.pop() {
                    None => {
                        results.push(ProcEvalResult::Partial(proc.clone(), self));
                        Ok(())
                    }
                    Some(value) => {
                        local.insert(var.clone(), value);
                        self.eval_proc(domain, local, cont, results)
                    }
                }
            },

            ProcX::Write(_, _, cont) =>
                // Ignore write operations
                self.eval_proc(domain, local, cont, results),

            ProcX::Read(_, var, cont) => {
                // Read values are always top
                local.insert(var.clone(), domain.get_top());
                self.eval_proc(domain, local, cont, results)
            }

            ProcX::Ite(term, left, right) => {
                let value = domain.interpret(local, term)?;
                match domain.test_bool(&value)? {
                    BoolDomainValue::True => self.eval_proc(domain, local, left, results),
                    BoolDomainValue::False => self.eval_proc(domain, local, right, results),
                    BoolDomainValue::Top => {
                        // Non-deterministically take both branches
                        let config_clone = self.clone();
                        let mut local_clone = local.clone();
                        self.eval_proc(domain, local, left, results)?;
                        config_clone.eval_proc(domain, &mut local_clone, right, results)
                    }
                }
            }

            ProcX::Call(name, args) => {
                results.push(ProcEvalResult::Full(
                    ProcState::Call(
                        name.clone(),
                        args.iter()
                            .map(|arg| domain.interpret(local, arg))
                            .collect::<Result<im::Vector<_>, _>>()?,
                    ),
                    self
                ));
                Ok(())
            }

            ProcX::Par(..) => Err(format!(
                "parallel composition only allowed at the top level"
            ))?,
        }
    }

    pub fn eval_proc_state(&self, domain: &mut D, proc_state: &ProcState<D>) -> Result<Vec<ProcEvalResult<D>>, Error> {
        match proc_state {
            ProcState::Stop => Ok(vec![]),
            ProcState::Call(proc_name, proc_args) => {
                let mut local = im::HashMap::new();
                let mut results = Vec::new();

                let proc_decl = self
                    .ctx
                    .procs
                    .get(proc_name)
                    .ok_or(format!("process {} not found", proc_name))?;

                assert!(proc_decl.params.len() == proc_args.len());

                // Create a local environment for process evaluation
                for (param, arg) in proc_decl.params.iter().zip(proc_args.iter()) {
                    local.insert(param.name.clone(), arg.clone());
                }

                self.clone().eval_proc(domain, &mut local, &proc_decl.body, &mut results)?;
                Ok(results)
            }
        }
    }

    /**
     * Non-deterministically fire any process until we hit skip or another process call
     * If no step can be taken, an empty vector is returned.
     * By default, step only returns the branches of the first process that can make progress
     * Setting `full` can enforce all processes to step
     */
    pub fn step(&self, domain: &mut D, full: bool) -> Result<Vec<StepResult<D>>, Error> {
        let mut branches = Vec::new();

        for (i, proc_state) in self.procs.iter().enumerate() {
            if let ProcState::Call(proc_name, ..) = proc_state {
                let results = self.eval_proc_state(domain, proc_state)?;
                assert!(results.len() > 0);

                for result in results {
                    match result {
                        ProcEvalResult::Full(new_proc_state, mut new_config) => {
                            // Update process state
                            new_config.procs[i] = new_proc_state;
                            branches.push(StepResult(proc_name.clone(), new_config));
                        }
                        _ => {}
                    }
                }

                // If !full, return once some process can make progress
                if !full && branches.len() != 0 {
                    break;
                }
            }
        }

        // println!("{} branches", branches.len());

        Ok(branches)
    }

    /// Component-wise comparison between each value in the configurations
    pub fn less_equal(&self, domain: &mut D, other: &Configuration<D>) -> Result<bool, Error> {
        assert!(self.chans.len() == other.chans.len());
        assert!(self.procs.len() == other.procs.len());

        for (s1, s2) in self.chans.iter().zip(other.chans.iter()) {
            assert!(s1.bound == s2.bound);

            if s1.queue.len() != s2.queue.len() {
                return Ok(false);
            }

            for (v1, v2) in s1.queue.iter().zip(s2.queue.iter()) {
                if !domain.less_equal(v1, v2)? {
                    return Ok(false);
                }
            }
        }

        for (p1, p2) in self.procs.iter().zip(other.procs.iter()) {
            match (p1, p2) {
                (ProcState::Call(name1, args1), ProcState::Call(name2, args2)) => {
                    if name1 != name2 {
                        return Ok(false);
                    }

                    assert!(args1.len() == args2.len());

                    for (a1, a2) in args1.iter().zip(args2.iter()) {
                        if !domain.less_equal(a1, a2)? {
                            return Ok(false);
                        }
                    }
                }
                (ProcState::Stop, ProcState::Stop) => {}
                _ => return Ok(false),
            }
        }

        Ok(true)
    }

    fn get_shape(&self) -> Result<Rc<Shape>, String> {
        let chans = self.chans.iter().map(|c| c.queue.len()).collect();
        let procs = self
            .procs
            .iter()
            .map(|s| match s {
                ProcState::Call(name, ..) => Some(name.clone()),
                ProcState::Stop => None,
            })
            .collect();

        Ok(Rc::new(Shape { chans, procs }))
    }

    /// Search for a deadlock state
    pub fn check_deadlock(&self, domain: &mut D) -> Result<(), Error> {
        let mut total_states = 0;
        let mut skipped = 0;

        let mut shapes: HashMap<Rc<Shape>, Vec<Rc<Configuration<D>>>> = HashMap::new();
        let mut stack = vec![Rc::new(self.clone())];

        let mut ancestor_index = HashMap::new();
        let mut ancestor_stack = Vec::new();

        // Fully expanded configurations
        let mut fully_expanded = HashSet::new();

        'outer: while let Some(config) = stack.pop() {
            if ancestor_index.contains_key(&config) {
                assert!(ancestor_stack.last() == Some(&config));
                ancestor_stack.pop();
                ancestor_index.remove(&config);
                continue;
            } else {
                // New config
                ancestor_stack.push(config.clone());
                ancestor_index.insert(config.clone(), ancestor_stack.len() - 1);
                stack.push(config.clone()); // revisit after visiting all children
            }

            // Do not re-explore less abstract states
            let shape = config.get_shape()?;
            if let Some(configs) = shapes.get_mut(&shape) {
                for explored_config in configs.iter() {
                    if config.less_equal(domain, explored_config)? {
                        skipped += 1;
                        continue 'outer;
                    }
                }
                configs.push(config.clone());
                total_states += 1;
            } else {
                // Add new shape
                shapes.insert(shape, vec![config.clone()]);
                total_states += 1;
            }

            // Check for deadlock
            if let Some(cycle) = config.find_wait_cycle(domain)? {
                println!("total states: {}, shapes: {}, skipped: {}", total_states, shapes.len(), skipped);
                println!("==============================");
                println!("{}", config);
                println!(
                    "has wait cycle: {}",
                    cycle
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(" -> ")
                );
                return Ok(());
            }

            if total_states % 1000 == 0 {
                println!("total states: {}, shapes: {}, skipped: {}", total_states, shapes.len(), skipped);
            }

            // Add all children
            for result in config.step(domain, false)? {
                let next_config = Rc::new(result.1);

                if let Some(index) = ancestor_index.get(&next_config) {
                    // TODO: check if the cycle contains a fully expanded node
                    let mut has_fully_expanded = false;
                    for ancestor in ancestor_stack.iter().skip(*index) {
                        if fully_expanded.contains(ancestor) {
                            has_fully_expanded = true;
                            break;
                        }
                    }
                    // Otherwise fully expand the ancestor and add unvisited children
                    if !has_fully_expanded {
                        let ancestor = &ancestor_stack[*index];
                        fully_expanded.insert(ancestor.clone());

                        let mut num_new_nodes = 0;

                        for result in ancestor.step(domain, true)? {
                            let ancestor_next_config = Rc::new(result.1);
                            if ancestor_index.contains_key(&ancestor_next_config) {
                                // Skip anything already in the ancestor stack
                                continue;
                            } else {
                                num_new_nodes += 1;
                                stack.push(ancestor_next_config);
                            }
                        }

                        println!("found insufficiently expanded cycle, adding {} new node(s)", num_new_nodes);
                    }
                } else {
                    stack.push(next_config);
                }
            }
        }

        println!("total states: {}, shapes: {}, skipped: {}", total_states, shapes.len(), skipped);

        Ok(())
    }

    /// Build a wait dependency graph from the configuration
    fn build_wait_dep_graph(&self, domain: &mut D) -> Result<WaitDependencyGraph, Error> {
        let mut edges = HashMap::new();

        // c -> owner of `input c`
        let mut in_chan_owners = HashMap::new();

        // c -> owner of `output c`
        let mut out_chan_owners = HashMap::new();

        // Map channels to their owners
        for proc_state in &self.procs {
            match proc_state {
                ProcState::Stop => {}
                ProcState::Call(proc_name, ..) => {
                    let decl = self
                        .ctx
                        .procs
                        .get(proc_name)
                        .ok_or(format!("undefined process"))?;
                    for res in &decl.res {
                        match &res.x {
                            ProcResourceX::Perm(..) => {}
                            ProcResourceX::Input(name) => {
                                in_chan_owners.insert(name.clone(), proc_name.clone());
                            }
                            ProcResourceX::Output(name) => {
                                out_chan_owners.insert(name.clone(), proc_name.clone());
                            }
                        }
                    }
                }
            }
        }

        // Iterate through each process state and gather their dependencies
        for proc_state in &self.procs {
            let mut out_edges = HashSet::new();

            if let ProcState::Call(proc_name, ..) = proc_state {
                let results = self.eval_proc_state(domain, proc_state)?;
                assert!(results.len() > 0);

                for result in results {
                    match result {
                        ProcEvalResult::Full(..) => {} // not stuck, no dependency
                        ProcEvalResult::Partial(rem, ..) => {
                            // println!("{} {}", proc_name, rem);
                            let owner = match &rem.x {
                                // Blocked on send, want to find the owner of input of the channel
                                ProcX::Send(chan, ..) => in_chan_owners.get(chan),
                                ProcX::Recv(chan, ..) => out_chan_owners.get(chan),
                                _ => unreachable!("blocked at non-blockable process"),
                            };

                            // If the owner is live, add the dependency (extend the path conditions if the dependency exists)
                            if let Some(owner) = owner {
                                if !out_edges.contains(owner) {
                                    out_edges.insert(owner.clone());
                                }
                            }
                        }
                    }
                }

                // Add out edges for proc_name
                edges.insert(proc_name.clone(), out_edges);
            }
        }

        Ok(WaitDependencyGraph { edges })
    }

    /**
     * Given a (symbolic) configuration, check if there
     * is a wait cycle between processes
     *
     * If so, return the processes involved in the cycle.
     * Otherwise return empty vector
     */
    fn find_wait_cycle(&self, domain: &mut D) -> Result<Option<Vec<ProcName>>, Error> {
        let wait_dep = self.build_wait_dep_graph(domain)?;

        // Find a cycle (with satisfiable path conditions) using dfs
        let mut stack = im::Vector::new();

        let mut unvisited = self.procs.iter().filter_map(|s| match s {
            ProcState::Call(name, ..) => Some(name.clone()),
            ProcState::Stop => None,
        }).collect::<HashSet<_>>(); // unvisited nodes

        let mut ancestor_index = HashMap::new();
        let mut ancestor_stack = Vec::new(); // ancestors for the current node

        while let Some(proc_name) = unvisited.iter().next().cloned() {
            unvisited.remove(&proc_name);

            // Still some unvisited processes
            stack.push_back(proc_name);

            while let Some(proc_name) = stack.pop_back() {
                if ancestor_index.contains_key(&proc_name) {
                    assert!(ancestor_stack.last() == Some(&proc_name));
                    ancestor_index.remove(&proc_name);
                    ancestor_stack.pop();
                    unvisited.remove(&proc_name);
                    continue;
                } else {
                    ancestor_index.insert(proc_name.clone(), ancestor_stack.len());
                    ancestor_stack.push(proc_name.clone());
                    // visit the node again to remove ancestor tag
                    // once all children are visited
                    stack.push_back(proc_name.clone());
                }

                // If any children points to an ancestor node, we found a cycle
                if let Some(out_edges) = wait_dep.edges.get(&proc_name) {
                    for child in out_edges.iter() {
                        if let Some(ancestor_idx) = ancestor_index.get(child) {
                            // Found a cycle
                            return Ok(Some(
                                ancestor_stack
                                    .iter()
                                    .skip(*ancestor_idx)
                                    .map(|p| (*p).clone())
                                    .collect(),
                            ));
                        } else {
                            stack.push_back(child.clone());
                        }
                    }
                }
            }
        }

        // All processes visited and found no cycles
        Ok(None)
    }
}

/**
 * Implement Eq and Hash traits for configuration
 *
 * In a configuration, ctx and chan_indices are ignored when comparing equality
 */
impl<D: Domain> PartialEq for ChanState<D> {
    fn eq(&self, other: &Self) -> bool {
        self.bound == other.bound && self.queue == other.queue
    }
}

impl<D: Domain> PartialEq for ProcState<D> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ProcState::Call(name1, args1), ProcState::Call(name2, args2)) => name1 == name2 && args1 == args2,
            (ProcState::Stop, ProcState::Stop) => true,
            _ => false,
        }
    }
}

impl<D: Domain> PartialEq for Configuration<D> {
    fn eq(&self, other: &Self) -> bool {
        self.chans == other.chans && self.procs == other.procs
    }
}

impl<D: Domain> Eq for ChanState<D> {}
impl<D: Domain> Eq for ProcState<D> {}
impl<D: Domain> Eq for Configuration<D> {}

impl<D: Domain> Hash for ChanState<D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bound.hash(state);
        self.queue.hash(state);
    }
}

impl<D: Domain> Hash for ProcState<D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            ProcState::Call(name, args) => {
                name.hash(state);
                args.hash(state);
            }
            ProcState::Stop => {
                "stop".hash(state);
            }
        }
    }
}

impl<D: Domain> Hash for Configuration<D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.chans.hash(state);
        self.procs.hash(state);
    }
}

/**
 * Manually implementing Clone traits since Rust doesn't
 * support automatically generating it for associated types.
 * https://github.com/rust-lang/rust/issues/44876
 */
impl<D: Domain> Clone for ChanState<D> {
    fn clone(&self) -> ChanState<D> {
        ChanState {
            bound: self.bound,
            queue: self.queue.clone(),
        }
    }
}

impl<D: Domain> Clone for ProcState<D> {
    fn clone(&self) -> ProcState<D> {
        match self {
            ProcState::Call(name, args) => ProcState::Call(name.clone(), args.clone()),
            ProcState::Stop => ProcState::Stop,
        }
    }
}

impl<D: Domain> Clone for Configuration<D> {
    fn clone(&self) -> Configuration<D> {
        Configuration {
            ctx: self.ctx.clone(),
            chan_to_index: self.chan_to_index.clone(),
            index_to_chan: self.index_to_chan.clone(),
            chans: self.chans.clone(),
            procs: self.procs.clone(),
        }
    }
}

impl<D: Domain> Clone for ProcEvalResult<D> {
    fn clone(&self) -> ProcEvalResult<D> {
        match self {
            ProcEvalResult::Partial(proc, config) => ProcEvalResult::Partial(proc.clone(), config.clone()),
            ProcEvalResult::Full(state, config) => ProcEvalResult::Full(state.clone(), config.clone()),
        }
    }
}

impl<D: Domain> Clone for StepResult<D> {
    fn clone(&self) -> StepResult<D> {
        StepResult(self.0.clone(), self.1.clone())
    }
}

/**
 * Implement Display traits for configurations
 */
impl<D: Domain> fmt::Display for ChanState<D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}] (max {})", self.queue.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", "), self.bound)
    }
}

impl<D: Domain> fmt::Display for ProcState<D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProcState::Call(name, args) =>
                write!(f, "{}({})", name, args.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")),
            ProcState::Stop => write!(f, "stop"),
        }
    }
}

impl<D: Domain> fmt::Display for Configuration<D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Configuration {{")?;

        for (name, state) in self.index_to_chan.iter().zip(self.chans.iter()) {
            writeln!(f, "  chan {} => {}", name, state)?;
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
        write!(f, "}}")
    }
}

impl<D: Domain> fmt::Display for StepResult<D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Step({}, {})", self.0, self.1)
    }
}

// pub trait Domain {
//     type Value: Clone + fmt::Display + Eq + PartialEq + Hash;

//     fn interpret(&mut self, local: &HashMap<Var, Self::Value>, term: &Term) -> Result<Self::Value, Error>;
//     fn get_top(&mut self) -> Self::Value;
//     fn test_bool(&mut self, value: Self::Value) -> Result<BoolDomainValue, Error>;
// }

/* Some domain implementations */

pub struct ZeroDomain {}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
/// A very coarse abstraction that only tests if an int is 0 or not
pub enum ZeroDomainValue {
    Top,
    True,
    False,
    Zero,
    NonZero,
}

impl fmt::Display for BoolDomainValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BoolDomainValue::True => write!(f, "true"),
            BoolDomainValue::False => write!(f, "false"),
            BoolDomainValue::Top => write!(f, "top"),
        }
    }
}

impl fmt::Display for ZeroDomainValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ZeroDomainValue::Top => write!(f, "top"),
            ZeroDomainValue::True => write!(f, "true"),
            ZeroDomainValue::False => write!(f, "false"),
            ZeroDomainValue::Zero => write!(f, "zero"),
            ZeroDomainValue::NonZero => write!(f, "non-zero"),
        }
    }
}

impl Domain for ZeroDomain {
    type Value = ZeroDomainValue;

    fn interpret(&mut self, local: &im::HashMap<Var, Self::Value>, term: &Term) -> Result<Self::Value, Error> {
        match &term.x {
            TermX::Var(v) => Ok(local.get(v).cloned().ok_or(format!("variable {} not found", v))?),
            TermX::Const(..) => Ok(ZeroDomainValue::Top),
            TermX::Bool(b) => if *b { Ok(ZeroDomainValue::True) } else { Ok(ZeroDomainValue::False) },
            TermX::Int(i) => if *i == 0 { Ok(ZeroDomainValue::Zero) } else { Ok(ZeroDomainValue::NonZero) },
            TermX::BitVec(..) => Ok(ZeroDomainValue::Top),
            TermX::Ref(..) => Ok(ZeroDomainValue::Top),

            TermX::Add(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (ZeroDomainValue::Zero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::Zero),
                    (ZeroDomainValue::Zero, ZeroDomainValue::NonZero) => Ok(ZeroDomainValue::NonZero),
                    (ZeroDomainValue::NonZero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::NonZero),
                    _ => Ok(ZeroDomainValue::Top),
                }

            TermX::Mul(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (ZeroDomainValue::Zero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::Zero),
                    (ZeroDomainValue::Zero, ZeroDomainValue::NonZero) => Ok(ZeroDomainValue::Zero),
                    (ZeroDomainValue::NonZero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::Zero),
                    _ => Ok(ZeroDomainValue::Top),
                }

            TermX::Less(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (ZeroDomainValue::Zero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::False),
                    _ => Ok(ZeroDomainValue::Top),
                }

            TermX::BVAdd(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVSub(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVMul(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVULT(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVUGT(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVULE(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVUGE(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVSLT(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVSGT(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVSLE(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVSGE(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVASHR(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVLSHR(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVSHL(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVFSHL(_, _, _, _) => Ok(ZeroDomainValue::Top),
            TermX::BVAnd(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVOr(_, _) => Ok(ZeroDomainValue::Top),
            TermX::BVXor(_, _) => Ok(ZeroDomainValue::Top),

            TermX::Equal(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (ZeroDomainValue::Zero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::True),
                    (ZeroDomainValue::NonZero, ZeroDomainValue::Zero) => Ok(ZeroDomainValue::False),
                    (ZeroDomainValue::Zero, ZeroDomainValue::NonZero) => Ok(ZeroDomainValue::False),
                    (ZeroDomainValue::True, ZeroDomainValue::True) => Ok(ZeroDomainValue::True),
                    (ZeroDomainValue::False, ZeroDomainValue::False) => Ok(ZeroDomainValue::True),
                    _ => Ok(ZeroDomainValue::Top),
                }

            TermX::And(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (ZeroDomainValue::True, ZeroDomainValue::True) => Ok(ZeroDomainValue::True),
                    (ZeroDomainValue::False, ZeroDomainValue::False) => Ok(ZeroDomainValue::False),
                    (ZeroDomainValue::False, ZeroDomainValue::True) => Ok(ZeroDomainValue::False),
                    (ZeroDomainValue::True, ZeroDomainValue::False) => Ok(ZeroDomainValue::False),
                    _ => Ok(ZeroDomainValue::Top),
                }

            TermX::Not(a) =>
                match self.interpret(local, a)? {
                    ZeroDomainValue::True => Ok(ZeroDomainValue::False),
                    ZeroDomainValue::False => Ok(ZeroDomainValue::True),
                    _ => Ok(ZeroDomainValue::Top),
                }
        }
    }

    fn get_top(&mut self) -> Self::Value {
        ZeroDomainValue::Top
    }

    fn test_bool(&mut self, value: &Self::Value) -> Result<BoolDomainValue, Error> {
        match value {
            ZeroDomainValue::Top => Ok(BoolDomainValue::Top),
            ZeroDomainValue::True => Ok(BoolDomainValue::True),
            ZeroDomainValue::False => Ok(BoolDomainValue::False),
            ZeroDomainValue::Zero => Err(format!("sort mismatch"))?,
            ZeroDomainValue::NonZero => Err(format!("sort mismatch"))?,
        }
    }

    fn less_equal(&mut self, v1: &Self::Value, v2: &Self::Value) -> Result<bool, Error> {
        match (v1, v2) {
            (_, ZeroDomainValue::Top) => Ok(true),
            (v1, v2) if v1 == v2 => Ok(true),
            _ => Ok(false),
        }
    }
}

pub struct BVZeroDomain {}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
/// A very coarse abstraction that only tests if an int is 0 or not
pub enum BVZeroDomainValue {
    Top,
    True,
    False,
    Zero,
    NonZero,
}

impl fmt::Display for BVZeroDomainValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BVZeroDomainValue::Top => write!(f, "top"),
            BVZeroDomainValue::True => write!(f, "true"),
            BVZeroDomainValue::False => write!(f, "false"),
            BVZeroDomainValue::Zero => write!(f, "zero"),
            BVZeroDomainValue::NonZero => write!(f, "non-zero"),
        }
    }
}

impl Domain for BVZeroDomain {
    type Value = BVZeroDomainValue;

    fn interpret(&mut self, local: &im::HashMap<Var, Self::Value>, term: &Term) -> Result<Self::Value, Error> {
        match &term.x {
            TermX::Var(v) => Ok(local.get(v).cloned().ok_or(format!("variable {} not found", v))?),
            TermX::Const(..) => Ok(BVZeroDomainValue::Top),
            TermX::Bool(b) => if *b { Ok(BVZeroDomainValue::True) } else { Ok(BVZeroDomainValue::False) },
            TermX::Int(..) => Ok(BVZeroDomainValue::Top),
            TermX::BitVec(i, _) => if *i == 0 { Ok(BVZeroDomainValue::Zero) } else { Ok(BVZeroDomainValue::NonZero) },
            TermX::Ref(..) => Ok(BVZeroDomainValue::Top),

            TermX::Add(..) => Ok(BVZeroDomainValue::Top),
            TermX::Mul(..) => Ok(BVZeroDomainValue::Top),
            TermX::Less(..) => Ok(BVZeroDomainValue::Top),

            TermX::BVAdd(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVSub(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVMul(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVULT(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVUGT(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVULE(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVUGE(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVSLT(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVSGT(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVSLE(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVSGE(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVASHR(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVLSHR(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVSHL(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVFSHL(_, _, _, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVAnd(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVOr(_, _) => Ok(BVZeroDomainValue::Top),
            TermX::BVXor(_, _) => Ok(BVZeroDomainValue::Top),

            TermX::Equal(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (BVZeroDomainValue::Zero, BVZeroDomainValue::Zero) => Ok(BVZeroDomainValue::True),
                    (BVZeroDomainValue::NonZero, BVZeroDomainValue::Zero) => Ok(BVZeroDomainValue::False),
                    (BVZeroDomainValue::Zero, BVZeroDomainValue::NonZero) => Ok(BVZeroDomainValue::False),
                    (BVZeroDomainValue::True, BVZeroDomainValue::True) => Ok(BVZeroDomainValue::True),
                    (BVZeroDomainValue::False, BVZeroDomainValue::False) => Ok(BVZeroDomainValue::True),
                    _ => Ok(BVZeroDomainValue::Top),
                }

            TermX::And(a, b) =>
                match (self.interpret(local, a)?, self.interpret(local, b)?) {
                    (BVZeroDomainValue::True, BVZeroDomainValue::True) => Ok(BVZeroDomainValue::True),
                    (BVZeroDomainValue::False, BVZeroDomainValue::False) => Ok(BVZeroDomainValue::False),
                    (BVZeroDomainValue::False, BVZeroDomainValue::True) => Ok(BVZeroDomainValue::False),
                    (BVZeroDomainValue::True, BVZeroDomainValue::False) => Ok(BVZeroDomainValue::False),
                    _ => Ok(BVZeroDomainValue::Top),
                }

            TermX::Not(a) =>
                match self.interpret(local, a)? {
                    BVZeroDomainValue::True => Ok(BVZeroDomainValue::False),
                    BVZeroDomainValue::False => Ok(BVZeroDomainValue::True),
                    _ => Ok(BVZeroDomainValue::Top),
                }
        }
    }

    fn get_top(&mut self) -> Self::Value {
        BVZeroDomainValue::Top
    }

    fn test_bool(&mut self, value: &Self::Value) -> Result<BoolDomainValue, Error> {
        match value {
            BVZeroDomainValue::Top => Ok(BoolDomainValue::Top),
            BVZeroDomainValue::True => Ok(BoolDomainValue::True),
            BVZeroDomainValue::False => Ok(BoolDomainValue::False),
            BVZeroDomainValue::Zero => Err(format!("sort mismatch"))?,
            BVZeroDomainValue::NonZero => Err(format!("sort mismatch"))?,
        }
    }

    fn less_equal(&mut self, v1: &Self::Value, v2: &Self::Value) -> Result<bool, Error> {
        match (v1, v2) {
            (_, BVZeroDomainValue::Top) => Ok(true),
            (v1, v2) if v1 == v2 => Ok(true),
            _ => Ok(false),
        }
    }
}
