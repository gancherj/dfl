use std::borrow::Borrow;
use std::ffi::OsStr;
use std::io::BufRead;
use std::rc::Rc;
use std::fmt;
use std::process;
use std::io;
use std::io::{Write, BufReader};
use im::HashSet;
use wait_timeout::ChildExt;
use std::time::Duration;

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Sort {
    Int,
    Bool,
    BitVec(u32),
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Ident(pub Rc<str>);

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum QuantKind {
    Forall,
    Exists,
}

#[derive(Debug)]
pub struct SortedVar {
    pub name: Ident,
    pub sort: Sort,
}

pub type Term = Rc<TermX>;
#[derive(Debug)]
pub enum TermX {
    Var(Ident),
    Int(u64),
    Bool(bool),
    App(Term, Vec<Term>),
    Quant(QuantKind, Vec<SortedVar>, Term),
}

pub type VarDecl = Rc<VarDeclX>;
#[derive(Debug)]
pub struct VarDeclX {
    pub name: Ident,
    pub sort: Sort,
}

pub type FunDecl = Rc<FunDeclX>;
#[derive(Debug)]
pub struct FunDeclX {
    pub name: Ident,
    pub inputs: Vec<Sort>,
    pub sort: Sort,
}

pub type SynthFunDecl = Rc<SynthFunDeclX>;
#[derive(Debug)]
pub struct SynthFunDeclX {
    pub name: Ident,
    pub inputs: Vec<SortedVar>,
    pub sort: Sort,
}

pub type Command = Rc<CommandX>;
#[derive(Debug)]
pub enum CommandX {
    Push,
    Pop,
    DeclareConst(VarDecl),
    DeclareFun(FunDecl),
    Assert(Term),
    CheckSat,
    GetModel,
    Exit,
    SetOption(Vec<String>),
    SetLogic(String),

    // Some commands for SyGuS
    SynthFun(SynthFunDecl),
    DeclareVar(VarDecl),
    Constraint(Term),
    CheckSynth,
}

pub struct Solver {
    process: process::Child,
    stdin: process::ChildStdin,
    stdout: BufReader<process::ChildStdout>,
}

/// Used when encoding stuff into SMT
/// This keeps track of things like fresh
/// variables/functions, etc.
pub struct EncodingCtx {
    prefix: String,
    fresh_var_count: u64,
    commands: Vec<Command>,
    used_names: HashSet<Ident>,
}

impl EncodingCtx {
    pub fn new(prefix: impl Into<String>) -> EncodingCtx {
        EncodingCtx {
            prefix: prefix.into(),
            fresh_var_count: 0,
            commands: Vec::new(),
            used_names: HashSet::new(),
        }
    }

    /// Generate a variable with the given name and sort
    /// If the variable already exists, return the same one
    // pub fn new_var(&mut self, name: impl AsRef<str>, sort: Sort) -> Ident {
    //     let name: Ident = format!("{}_{}", self.prefix, name.as_ref()).into();
    //     if self.consts.contains_key(&name) {
    //         assert!(self.consts.get(&name).unwrap().sort == sort);
    //     } else {
    //         self.consts.insert(name.clone(), Rc::new(VarDeclX {
    //             name: name.clone(),
    //             sort: sort,
    //         }));
    //     }
    //     name
    // }

    /// Find the next fresh name
    pub fn fresh_ident(&mut self, prefix: impl AsRef<str>) -> Ident {
        let mut name;
        loop {
            name = Ident::from(format!("{}_{}_{}", self.prefix, prefix.as_ref(), self.fresh_var_count));
            self.fresh_var_count += 1;
            if !self.used_names.contains(&name) {
                return name;
            }
        }
    }

    pub fn fresh_const(&mut self, prefix: impl AsRef<str>, sort: Sort) -> Ident {
        let name = self.fresh_ident(prefix);
        self.commands.push(CommandX::declare_const(&name, sort));
        name
    }

    pub fn fresh_var(&mut self, prefix: impl AsRef<str>, sort: Sort) -> Ident {
        let name = self.fresh_ident(prefix);
        self.commands.push(CommandX::declare_var(&name, sort));
        name
    }

    pub fn fresh_fun(&mut self, prefix: impl AsRef<str>, inputs: impl IntoIterator<Item=Sort>, sort: Sort) -> Ident {
        let name = self.fresh_ident(prefix);
        self.commands.push(CommandX::declare_fun(&name, inputs, sort));
        name
    }

    /// Generate a fresh synth-fun function of the given sort
    pub fn fresh_synth_fun(
        &mut self,
        prefix: impl AsRef<str>,
        inputs: impl IntoIterator<Item=(impl Into<Ident>, Sort)>,
        sort: Sort,
    ) -> Ident {
        let name = self.fresh_ident(prefix);
        self.commands.push(CommandX::synth_fun(&name, inputs, sort));
        name
    }

    pub fn to_commands(&self) -> &Vec<Command> {
        &self.commands
    }
}

pub enum CheckSatResult {
    Sat,
    Unsat,
    Unknown
}

// TODO
pub type SynthModel = String;

pub enum CheckSynthResult {
    Infeasible,
    Fail,
    Synthesized(SynthModel),
}

impl<T: AsRef<str>> From<T> for Ident {
    fn from(value: T) -> Ident {
        Ident(value.as_ref().into())
    }
}

impl From<&Ident> for Ident {
    fn from(id: &Ident) -> Ident {
        id.clone()
    }
}

impl TermX {
    pub fn int(i: u64) -> Term {
        Rc::new(TermX::Int(i))
    }

    pub fn bool(b: bool) -> Term {
        Rc::new(TermX::Bool(b))
    }

    pub fn var(id: impl Into<Ident>) -> Term {
        Rc::new(TermX::Var(id.into()))
    }

    pub fn app(id: impl Into<Ident>, args: impl IntoIterator<Item=impl Borrow<Term>>) -> Term {
        Rc::new(TermX::App(TermX::var(id), args.into_iter().map(|a| a.borrow().clone()).collect()))
    }

    pub fn app_term(term: impl Borrow<Term>, args: impl IntoIterator<Item=impl Borrow<Term>>) -> Term {
        Rc::new(TermX::App(term.borrow().clone(), args.into_iter().map(|a| a.borrow().clone()).collect()))
    }

    pub fn add(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("+", [a.borrow(), b.borrow()])
    }

    pub fn mul(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("*", [a.borrow(), b.borrow()])
    }

    pub fn and(conj: impl IntoIterator<Item=impl Borrow<Term>>) -> Term {
        let args: Vec<_> = conj.into_iter().collect();
        if args.len() != 0 {
            TermX::app("and", args)
        } else {
            TermX::bool(true)
        }
    }

    pub fn or(conj: impl IntoIterator<Item=impl Borrow<Term>>) -> Term {
        let args: Vec<_> = conj.into_iter().collect();
        if args.len() != 0 {
            TermX::app("or", args)
        } else {
            TermX::bool(false)
        }
    }

    pub fn not(a: impl Borrow<Term>) -> Term {
        TermX::app("not", [a.borrow()])
    }

    pub fn implies(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("=>", [a.borrow(), b.borrow()])
    }

    pub fn eq(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("=", [a.borrow(), b.borrow()])
    }

    pub fn lt(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("<", [a.borrow(), b.borrow()])
    }

    pub fn le(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("<=", [a.borrow(), b.borrow()])
    }

    pub fn ge(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app(">=", [a.borrow(), b.borrow()])
    }

    pub fn gt(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app(">", [a.borrow(), b.borrow()])
    }
    
    pub fn neg(a: impl Borrow<Term>) -> Term {
        TermX::app("-", [a.borrow()])
    }

    pub fn ite(c: impl Borrow<Term>, t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        TermX::app("ite", [c.borrow(), t1.borrow(), t2.borrow()])
    }

    pub fn forall(vars: impl IntoIterator<Item=(impl Into<Ident>, Sort)>, body: impl Borrow<Term>) -> Term {
        Rc::new(TermX::Quant(
            QuantKind::Forall,
            vars.into_iter()
                .map(|(name, sort)| SortedVar { name: name.into(), sort: sort })
                .collect(),
            body.borrow().clone(),
        ))
    }

    pub fn exists(vars: impl IntoIterator<Item=(impl Into<Ident>, Sort)>, body: impl Borrow<Term>) -> Term {
        Rc::new(TermX::Quant(
            QuantKind::Exists,
            vars.into_iter()
                .map(|(name, sort)| SortedVar { name: name.into(), sort: sort })
                .collect(),
            body.borrow().clone(),
        ))
    }
}

impl CommandX {
    pub fn check_sat() -> Command {
        Rc::new(CommandX::CheckSat)
    }

    pub fn check_synth() -> Command {
        Rc::new(CommandX::CheckSynth)
    }

    pub fn get_model() -> Command {
        Rc::new(CommandX::GetModel)
    }

    pub fn exit() -> Command {
        Rc::new(CommandX::Exit)
    }

    pub fn push() -> Command {
        Rc::new(CommandX::Push)
    }

    pub fn pop() -> Command {
        Rc::new(CommandX::Pop)
    }

    pub fn declare_const(id: impl Into<Ident>, sort: Sort) -> Command {
        Rc::new(CommandX::DeclareConst(Rc::new(VarDeclX { name: id.into(), sort: sort })))
    }

    pub fn declare_var(id: impl Into<Ident>, sort: Sort) -> Command {
        Rc::new(CommandX::DeclareVar(Rc::new(VarDeclX { name: id.into(), sort: sort })))
    }

    pub fn declare_fun(id: impl Into<Ident>, inputs: impl IntoIterator<Item=Sort>, sort: Sort) -> Command {
        Rc::new(CommandX::DeclareFun(Rc::new(FunDeclX { name: id.into(), inputs: inputs.into_iter().collect(), sort: sort })))
    }

    pub fn synth_fun(id: impl Into<Ident>, inputs: impl IntoIterator<Item=(impl Into<Ident>, Sort)>, sort: Sort) -> Command {
        Rc::new(CommandX::SynthFun(Rc::new(SynthFunDeclX {
            name: id.into(),
            inputs: inputs.into_iter()
                .map(|(v, s)| SortedVar { name: v.into(), sort: s })
                .collect(),
            sort: sort,
        })))
    }

    pub fn assert(term: impl Borrow<Term>) -> Command {
        Rc::new(CommandX::Assert(term.borrow().clone()))
    }

    pub fn constraint(term: impl Borrow<Term>) -> Command {
        Rc::new(CommandX::Constraint(term.borrow().clone()))
    }

    pub fn set_logic(logic: impl Into<String>) -> Command {
        Rc::new(CommandX::SetLogic(logic.into()))
    }

    pub fn set_option(option: impl IntoIterator<Item=impl Into<String>>) -> Command {
        Rc::new(CommandX::SetOption(option.into_iter().map(|s| s.into()).collect()))
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        self.close().expect("fail to close solver process");
    }
}

impl Solver {
    const WAIT_TIMEOUT: u64 = 5;

    pub fn new<T: AsRef<OsStr>>(cmd: T, args: &[T]) -> io::Result<Solver> {
        let mut process = process::Command::new(cmd)
            .args(args)
            .stdin(process::Stdio::piped())
            .stdout(process::Stdio::piped())
            .spawn()?;

        let stdin = process.stdin.take().ok_or(io::Error::other("failed to take solver process stdin"))?;
        let stdout = process.stdout.take().ok_or(io::Error::other("failed to take solver process stdin"))?;

        Ok(Solver {
            process: process,
            stdin: stdin,
            stdout: BufReader::new(stdout),
        })
    }

    /// Close a solver process first by sending (exit)
    /// Then kill it if it fails to respond in WAIT_TIMEOUT seconds
    pub fn close(&mut self) -> io::Result<process::ExitStatus> {
        self.send_command(CommandX::exit())?;
        
        // Wait for Solver::WAIT_TIMEOUT seconds before killing the process
        match self.process.wait_timeout(Duration::from_secs(Solver::WAIT_TIMEOUT))? {
            Some(status) => Ok(status),
            None => {
                self.process.kill()?;
                self.process.wait()
            }
        }
    }

    pub fn send_command(&mut self, cmd: impl Borrow<Command>) -> io::Result<()> {
        // eprintln!("{}", cmd.borrow());
        writeln!(self.stdin, "{}", cmd.borrow())
    }

    /// Send a command then wait to read output from the solver
    /// The output is expected to be a single S-expression
    pub fn send_command_with_output(&mut self, cmd: impl Borrow<Command>) -> io::Result<String> {
        self.send_command(cmd)?;

        let mut output = String::new();
        let mut num_open_paren = 0;

        loop {
            let mut buf = String::new();
            if self.stdout.read_line(&mut buf)? == 0 {
                break
            }

            output.push_str(&buf);

            for c in buf.chars() {
                if c == '(' {
                    num_open_paren += 1;
                } else if c == ')' {
                    if num_open_paren == 0 {
                        return Err(io::Error::other("unmatched closing parenthesis"));
                    }
                    num_open_paren -= 1;
                }
            }

            if num_open_paren == 0 {
                break
            }
        }

        Ok(output)
    }

    pub fn set_option(&mut self, option: impl IntoIterator<Item=impl Into<String>>) -> io::Result<()> {
        self.send_command(CommandX::set_option(option))
    }

    pub fn set_logic(&mut self, logic: impl Into<String>) -> io::Result<()> {
        self.send_command(CommandX::set_logic(logic))
    }

    pub fn assert(&mut self, term: impl Borrow<Term>) -> io::Result<()> {
        self.send_command(CommandX::assert(term))
    }

    pub fn constraint(&mut self, term: impl Borrow<Term>) -> io::Result<()> {
        self.send_command(CommandX::constraint(term))
    }

    pub fn push(&mut self) -> io::Result<()> {
        self.send_command(CommandX::push())
    }

    pub fn pop(&mut self) -> io::Result<()> {
        self.send_command(CommandX::pop())
    }

    pub fn check_synth(&mut self) -> io::Result<CheckSynthResult> {
        let output = self.send_command_with_output(CommandX::check_synth())?;

        match output.trim() {
            "infeasible" => Ok(CheckSynthResult::Infeasible),
            "fail" => Ok(CheckSynthResult::Fail),
            _ => Ok(CheckSynthResult::Synthesized(output.trim().to_string())),
        }
    }

    pub fn check_sat(&mut self) -> io::Result<CheckSatResult> {
        let output = self.send_command_with_output(CommandX::check_sat())?;

        match output.trim() {
            "sat" => Ok(CheckSatResult::Sat),
            "unsat" => Ok(CheckSatResult::Unsat),
            "unknown" => Ok(CheckSatResult::Unknown),
            _ => Err(io::Error::other(format!("unexpected solver check-sat output: {}", output))),
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: Handle special characters and escaping (see SMTLIB standard 3.1 Lexicon)
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "Int"),
            Sort::Bool => write!(f, "Bool"),
            Sort::BitVec(width) => write!(f, "(_ BitVec {})", width),
        }
    }
}

impl fmt::Display for SortedVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.name, self.sort)
    }
}

impl fmt::Display for TermX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermX::Var(v) => write!(f, "{}", v),
            TermX::Int(i) => write!(f, "{}", i),
            TermX::Bool(b) => write!(f, "{}", b),
            TermX::App(id, args) => {
                write!(f, "({}", id)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
            TermX::Quant(q, vs, t) => {
                match q {
                    QuantKind::Forall => write!(f, "(forall ("),
                    QuantKind::Exists => write!(f, "(exists ("),
                }?;

                for (pos, v) in vs.iter().enumerate() {
                    if pos == 0 {
                        write!(f, "{}", v)?;
                    } else {
                        write!(f, " {}", v)?;
                    }
                }
                write!(f, ") {}", t)?;
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for VarDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.name, self.sort)
    }
}

impl fmt::Display for FunDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} (", self.name)?;
        for (pos, sort) in self.inputs.iter().enumerate() {
            if pos == 0 {
                write!(f, "{}", sort)?;
            } else {
                write!(f, " {}", sort)?;
            }
        }
        write!(f, ") {}", self.sort)
    }
}

impl fmt::Display for SynthFunDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} (", self.name)?;
        for (pos, var) in self.inputs.iter().enumerate() {
            if pos == 0 {
                write!(f, "({} {})", var.name, var.sort)?;
            } else {
                write!(f, " ({} {})", var.name, var.sort)?;
            }
        }
        write!(f, ") {}", self.sort)
    }
}

impl fmt::Display for CommandX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CommandX::Push => write!(f, "(push)"),
            CommandX::Pop => write!(f, "(pop)"),
            CommandX::DeclareConst(decl) => write!(f, "(declare-const {})", decl),
            CommandX::DeclareFun(decl) => write!(f, "(declare-fun {})", decl),
            CommandX::Assert(t) => write!(f, "(assert {})", t),
            CommandX::CheckSat => write!(f, "(check-sat)"),
            CommandX::GetModel => write!(f, "(get-model)"),
            CommandX::Exit => write!(f, "(exit)"),
            CommandX::SetOption(options) => write!(f, "(set-option {})", options.join(" ")),
            CommandX::SetLogic(logic) => write!(f, "(set-logic {})", logic),
            CommandX::DeclareVar(decl) => write!(f, "(declare-var {})", decl),
            CommandX::SynthFun(decl) => write!(f, "(synth-fun {})", decl),
            CommandX::Constraint(t) => write!(f, "(constraint {})", t),
            CommandX::CheckSynth => write!(f, "(check-synth)"),
        }
    }
}

impl fmt::Display for CheckSatResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CheckSatResult::Sat => write!(f, "sat"),
            CheckSatResult::Unsat => write!(f, "unsat"),
            CheckSatResult::Unknown => write!(f, "unknown"),
        }
    }
}
