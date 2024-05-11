use std::rc::Rc;
use std::fmt;

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
    SetOption(Vec<String>),
    SetLogic(String),
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
            Sort::Int => write!(f, "int"),
            Sort::Bool => write!(f, "bool"),
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
            CommandX::SetOption(options) => write!(f, "(set-option {})", options.join(" ")),
            CommandX::SetLogic(logic) => write!(f, "(set-logic {})", logic),
        }
    }
}
