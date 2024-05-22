use std::borrow::Borrow;
use std::ffi::OsStr;
use std::io::BufRead;
use std::rc::Rc;
use std::fmt;
use std::process;
use std::io;
use std::io::{Write, BufReader};
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
    App(Ident, Vec<Term>),
    Quant(QuantKind, Vec<SortedVar>, Term),
}

pub type Command = Rc<CommandX>;
#[derive(Debug)]
pub enum CommandX {
    Push,
    Pop,
    DeclareConst(Ident, Sort),
    DeclareFun(Ident, Vec<Sort>, Sort),
    Assert(Term),
    CheckSat,
    GetModel,
    Exit,
    SetOption(Vec<String>),
    SetLogic(String),
}

pub struct Solver {
    process: process::Child,
    stdin: process::ChildStdin,
    stdout: BufReader<process::ChildStdout>,
}

pub enum SatResult {
    Sat,
    Unsat,
    Unknown
}

impl<T: AsRef<str>> From<T> for Ident {
    fn from(value: T) -> Ident {
        Ident(value.as_ref().into())
    }
}

impl TermX {
    pub fn int(i: u64) -> Term {
        Rc::new(TermX::Int(i))
    }

    pub fn bool(b: bool) -> Term {
        Rc::new(TermX::Bool(b))
    }

    pub fn var<S: AsRef<str>>(id: S) -> Term {
        Rc::new(TermX::Var(Ident::from(id)))
    }

    pub fn app<S: AsRef<str>, T: Borrow<Term>, I: IntoIterator<Item=T>>(id: S, args: I) -> Term {
        Rc::new(TermX::App(Ident::from(id), args.into_iter().map(|a| a.borrow().clone()).collect()))
    }

    pub fn add(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("+", [a.borrow(), b.borrow()])
    }

    pub fn lt(a: impl Borrow<Term>, b: impl Borrow<Term>) -> Term {
        TermX::app("<", [a.borrow(), b.borrow()])
    }
    
}

impl CommandX {
    pub fn check_sat() -> Command {
        Rc::new(CommandX::CheckSat)
    }

    pub fn get_model() -> Command {
        Rc::new(CommandX::GetModel)
    }

    pub fn exit() -> Command {
        Rc::new(CommandX::Exit)
    }

    pub fn declare_const<S: AsRef<str>>(id: S, sort: Sort) -> Command {
        Rc::new(CommandX::DeclareConst(Ident::from(id), sort))
    }

    pub fn assert(term: impl Borrow<Term>) -> Command {
        Rc::new(CommandX::Assert(term.borrow().clone()))
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
        writeln!(self.stdin, "{}", cmd.borrow())
    }

    /// Send a command then wait to read output from the solver
    /// The output is expected to be a single S-expression
    pub fn send_command_with_output(&mut self, cmd: impl Borrow<Command>) -> io::Result<String> {
        writeln!(self.stdin, "{}", cmd.borrow())?;

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

    pub fn assert(&mut self, term: impl Borrow<Term>) -> io::Result<()> {
        self.send_command(CommandX::assert(term))
    }

    pub fn check_sat(&mut self) -> io::Result<SatResult> {
        let output = self.send_command_with_output(CommandX::check_sat())?;

        match output.trim() {
            "sat" => Ok(SatResult::Sat),
            "unsat" => Ok(SatResult::Unsat),
            "unknown" => Ok(SatResult::Unknown),
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

impl fmt::Display for CommandX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CommandX::Push => write!(f, "(push)"),
            CommandX::Pop => write!(f, "(pop)"),
            CommandX::DeclareConst(id, sort) => write!(f, "(declare-const {} {})", id, sort),
            CommandX::DeclareFun(id, arg_sorts, sort) => {
                write!(f, "(declare-fun {} (", id)?;
                for (pos, sort) in arg_sorts.iter().enumerate() {
                    if pos == 0 {
                        write!(f, "{}", sort)?;
                    } else {
                        write!(f, " {}", sort)?;
                    }
                }
                write!(f, ") {})", sort)
            }
            CommandX::Assert(t) => write!(f, "(assert {})", t),
            CommandX::CheckSat => write!(f, "(check-sat)"),
            CommandX::GetModel => write!(f, "(get-model)"),
            CommandX::Exit => write!(f, "(exit)"),
            CommandX::SetOption(options) => write!(f, "(set-option {})", options.join(" ")),
            CommandX::SetLogic(logic) => write!(f, "(set-logic {})", logic),
        }
    }
}

impl fmt::Display for SatResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SatResult::Sat => write!(f, "sat"),
            SatResult::Unsat => write!(f, "unsat"),
            SatResult::Unknown => write!(f, "unknown"),
        }
    }
}
