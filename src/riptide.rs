use std::{borrow::Borrow, rc::Rc};
use std::{fmt, io};

use im::HashMap;
use indexmap::{IndexMap, IndexSet};
use serde::{Deserialize, Serialize};

use crate::ast::{BaseType, ConstDeclX};
use crate::span::Spanned;
use crate::{
    BitVecWidth, ChanDeclX, ChanName, Ctx, MutDeclX, MutReferenceIndex, MutReferenceTypeX,
    MutReferenceX, MutTypeX, PermDeclX, PermVar, PermissionX, Proc, ProcDeclX, ProcName, ProcParam,
    ProcParamX, ProcResource, ProcResourceX, ProcX, Term, TermType, TermTypeX, TermX, Var,
};

pub type ChannelId = u32;
pub type OperatorId = u32;
pub type PortIndex = u32;
pub type ConstValue = i32;

#[derive(Serialize, Deserialize, Debug)]
struct RawFunArg {
    name: String,
    #[serde(rename = "type")]
    typ: String,
    noalias: Option<bool>,
}

#[derive(Serialize, Deserialize, Debug)]
struct RawFunInfo {
    name: String,
    args: Vec<RawFunArg>,
    #[serde(rename = "return_type")]
    return_typ: String,
}

#[derive(Serialize, Deserialize, Debug)]
struct RawInput {
    #[serde(rename = "ID")]
    id: Option<OperatorId>,
    #[serde(rename = "oport")]
    port: Option<PortIndex>,
    value: Option<ConstValue>,
    name: Option<String>,
    #[serde(rename = "type")]
    kind: String, // data, xdata, const
    hold: bool,
}

#[derive(Serialize, Deserialize, Debug)]
struct RawVertex {
    #[serde(rename = "ID")]
    id: OperatorId,

    inputs: Vec<Vec<RawInput>>,

    op: String,
    pred: Option<String>,
    #[serde(rename = "type")]
    kind: Option<String>,
}

#[derive(Serialize, Deserialize, Debug)]
struct RawGraph {
    #[serde(rename = "function")]
    info: RawFunInfo,
    vertices: Vec<RawVertex>,
}

pub type ParamName = Rc<str>;

pub type ParamType = Rc<ParamTypeX>;
#[derive(Debug)]
pub enum ParamTypeX {
    Int(u32),
    Pointer(ParamType),
}

pub type Parameter = Rc<ParameterX>;
#[derive(Debug)]
pub struct ParameterX {
    pub name: ParamName,
    pub typ: ParamType,

    /// True if the parameter can alias with another parameter (pointers only)
    pub alias: bool,
}

#[derive(Debug)]
pub struct Port(OperatorId, PortIndex);

pub type Channel = Rc<ChannelX>;
#[derive(Debug)]
pub enum ChannelX {
    Async {
        id: ChannelId,
        src: Port,
        dest: Port,
    },
    Const {
        id: ChannelId,
        value: ConstValue,
        hold: bool,
    },
    Param {
        id: ChannelId,
        param: Parameter,
        hold: bool,
    },
}

impl ChannelX {
    pub fn id(&self) -> ChannelId {
        match self {
            ChannelX::Async { id, .. } => *id,
            ChannelX::Const { id, .. } => *id,
            ChannelX::Param { id, .. } => *id,
        }
    }

    pub fn is_hold(&self) -> bool {
        match self {
            ChannelX::Async { .. } => false,
            ChannelX::Const { hold, .. } => *hold,
            ChannelX::Param { hold, .. } => *hold,
        }
    }

    pub fn is_constant(&self) -> bool {
        match self {
            ChannelX::Async { .. } => false,
            ChannelX::Const { .. } => true,
            ChannelX::Param { .. } => true,
        }
    }
}

#[derive(Debug)]
pub enum OperatorKind {
    Id,
    Add,
    Sub,
    Mul,
    ULT,
    UGT,
    ULE,
    UGE,
    SLT,
    SGT,
    SLE,
    SGE,
    SHL,
    ASHR,
    LSHR,
    And,
    Or,
    Xor,
    Eq,
    Select,
    GEP,
    Stream(bool),
    Carry(bool),
    Merge,
    Inv(bool),
    Steer(bool),
    Ld,
    LdSync,
    St,
    StSync,
}

pub type Operator = Rc<OperatorX>;
#[derive(Debug)]
pub struct OperatorX {
    pub id: OperatorId,
    pub kind: OperatorKind,
    pub inputs: Vec<Channel>,
    pub outputs: IndexMap<PortIndex, Vec<Channel>>,
}

#[derive(Debug)]
pub struct Graph {
    pub params: IndexMap<ParamName, Parameter>,
    pub chans: Vec<Channel>,
    pub ops: Vec<Operator>,
}

impl ParamTypeX {
    fn from_str(s: impl AsRef<str>) -> Result<ParamType, String> {
        match s.as_ref() {
            "i32" => Ok(Rc::new(ParamTypeX::Int(32))),
            "i32*" => Ok(Rc::new(ParamTypeX::Pointer(Rc::new(ParamTypeX::Int(32))))),
            _ => Err(format!("unsupported parameter type `{}`", s.as_ref())),
        }
    }
}

impl OperatorKind {
    fn from_raw(raw: &RawVertex) -> Result<OperatorKind, String> {
        match raw.op.as_str() {
            "ARITH_CFG_OP_ID" => Ok(OperatorKind::Id),
            "ARITH_CFG_OP_ADD" => Ok(OperatorKind::Add),
            "ARITH_CFG_OP_SUB" => Ok(OperatorKind::Sub),
            "MUL_CFG_OP_MUL" => Ok(OperatorKind::Mul),
            "ARITH_CFG_OP_ULT" => Ok(OperatorKind::ULT),
            "ARITH_CFG_OP_UGT" => Ok(OperatorKind::UGT),
            "ARITH_CFG_OP_ULE" => Ok(OperatorKind::ULE),
            "ARITH_CFG_OP_UGE" => Ok(OperatorKind::UGE),
            "ARITH_CFG_OP_SLT" => Ok(OperatorKind::SLT),
            "ARITH_CFG_OP_SGT" => Ok(OperatorKind::SGT),
            "ARITH_CFG_OP_SLE" => Ok(OperatorKind::SLE),
            "ARITH_CFG_OP_SGE" => Ok(OperatorKind::SGE),
            "ARITH_CFG_OP_SHL" => Ok(OperatorKind::SHL),
            "ARITH_CFG_OP_ASHR" => Ok(OperatorKind::ASHR),
            "ARITH_CFG_OP_LSHR" => Ok(OperatorKind::LSHR),
            "ARITH_CFG_OP_AND" => Ok(OperatorKind::And),
            "ARITH_CFG_OP_OR" => Ok(OperatorKind::Or),
            "ARITH_CFG_OP_XOR" => Ok(OperatorKind::Xor),
            "ARITH_CFG_OP_EQ" => Ok(OperatorKind::Eq),
            "CF_CFG_OP_SELECT" => Ok(OperatorKind::Select),
            "ARITH_CFG_OP_GEP" => Ok(OperatorKind::GEP),
            "STREAM_CFG_OP_STREAM" => match &raw.pred {
                Some(pred) if pred == "STREAM_CFG_PRED_TRUE" => Ok(OperatorKind::Stream(true)),
                Some(pred) if pred == "STREAM_CFG_PRED_FALSE" => Ok(OperatorKind::Stream(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for stream", pred)),
                None => Err(format!("predicate not specified for stream")),
            },
            "CF_CFG_OP_CARRY" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Carry(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Carry(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for carry", pred)),
                None => Err(format!("predicate not specified for carry")),
            },
            "CF_CFG_OP_MERGE" => Ok(OperatorKind::Merge),
            "CF_CFG_OP_INVARIANT" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Inv(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Inv(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for invariant", pred)),
                None => Err(format!("predicate not specified for invariant")),
            },
            "CF_CFG_OP_STEER" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Steer(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Steer(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for steer", pred)),
                None => Err(format!("predicate not specified for steer")),
            },
            "MEM_CFG_OP_LOAD" => match raw.inputs.len() {
                2 => Ok(OperatorKind::Ld),
                3 => Ok(OperatorKind::LdSync),
                _ => Err(format!(
                    "load operator expected to have either 2 or 3 inputs, got {}",
                    raw.inputs.len()
                )),
            },
            "MEM_CFG_OP_STORE" => match raw.inputs.len() {
                3 => Ok(OperatorKind::St),
                4 => Ok(OperatorKind::StSync),
                _ => Err(format!(
                    "store operator expected to have either 3 or 4 inputs, got {}",
                    raw.inputs.len()
                )),
            },
            _ => Err(format!("unsupported operator `{}`", raw.op)),
        }
    }
}

impl OperatorX {
    pub fn ports(&self) -> impl Iterator<Item = &PortIndex> {
        self.outputs.keys()
    }

    pub fn outputs(&self, port: PortIndex) -> impl Iterator<Item = &Channel> {
        self.outputs.get(&port).map_or([].iter(), |v| v.iter())
    }
}

pub struct TranslationOptions {
    pub word_width: BitVecWidth,
}

/// Returns Proc
macro_rules! riptide_proc {
    (($opts:expr, $op:expr)) => {};

    // Use an abitrary process as continuation
    (($opts:expr, $op:expr) cont $cont:expr;) => {
        $cont
    };

    // Process call
    (($opts:expr, $op:expr) call $name:expr $(,$args:expr)*;) => {
        ProcX::call(&$name, vec![$($args),*] as Vec<Term>)
    };

    // Receive from port
    (($opts:expr, $op:expr) recv $name:ident <= port $port:expr; $($rest:tt)*) => {
        Graph::recv_from_input($opts, $op, $port, stringify!($name), riptide_proc!(($opts, $op) $($rest)*))
    };

    // Send to port
    (($opts:expr, $op:expr) send $term:expr => port $port:expr; $($rest:tt)*) => {
        Graph::send_to_outputs($op, $port, $term, riptide_proc!(($opts, $op) $($rest)*))
    };

    // Read
    (($opts:expr, $op:expr) read $name:ident <= $mut_ref:expr; $($rest:tt)*) => {
        ProcX::read($mut_ref, stringify!($name), riptide_proc!(($opts, $op) $($rest)*))
    };

    // Write
    (($opts:expr, $op:expr) write $term:expr => $mut_ref:expr; $($rest:tt)*) => {
        ProcX::write($mut_ref, $term, riptide_proc!(($opts, $op) $($rest)*))
    };

    // If-then-else
    (($opts:expr, $op:expr) if ($term:expr) { $($left:tt)* } else { $($right:tt)* }) => {
        ProcX::ite($term, riptide_proc!(($opts, $op) $($left)*), riptide_proc!(($opts, $op) $($right)*))
    };
}

/// Returns ProcDecl
macro_rules! riptide {
    (($opts:expr, $op:expr) proc $name:expr $(,$params:expr)*; $res:expr => $($rest:tt)*) => {
        ProcDeclX::new(
            &$name,
            vec![$($params),*] as Vec<ProcParam>,
            $res,
            riptide_proc! { ($opts, $op) $($rest)* }
        )
    };
}

macro_rules! arith_op_translation {
    // Binary operator reading from port 0 and 1
    // applying a binary function TermX::$fn
    // and then sending the output to port 0
    ($opts:expr, $op:expr, $ctx:expr, $name:expr, $res:expr, $fn:ident) => {
        $ctx.add_proc(&riptide! {
            ($opts, $op)
            proc $name; $res =>
                recv a <= port 0;
                recv b <= port 1;
                send TermX::$fn(TermX::var("a"), TermX::var("b")) => port 0;
                call $name;
        })?
    };
}

macro_rules! pred_op_translation {
    // Binary predicate operator reading from port 0 and 1
    // applying a binary function TermX::$fn
    // and then sending the output (1 if the result is non-zero, 0 otherwise) to port 0
    ($opts:expr, $op:expr, $ctx:expr, $name:expr, $res:expr, $fn:ident) => {
        $ctx.add_proc(&riptide! {
            ($opts, $op)
            proc $name; $res =>
                recv a <= port 0;
                recv b <= port 1;
                if (TermX::$fn(TermX::var("a"), TermX::var("b"))) {
                    send TermX::bit_vec(1, $opts.word_width) => port 0;
                    call $name;
                } else {
                    send TermX::bit_vec(0, $opts.word_width) => port 0;
                    call $name;
                }
        })?
    };
}

impl Graph {
    pub fn from_reader(reader: impl io::Read) -> io::Result<Graph> {
        Graph::from_raw(&serde_json::from_reader(reader)?).map_err(|msg| io::Error::other(msg))
    }

    fn from_raw(raw: &RawGraph) -> Result<Graph, String> {
        let mut params = IndexMap::new();
        for arg in &raw.info.args {
            let name: ParamName = arg.name.as_str().into();
            params.insert(
                name.clone(),
                Rc::new(ParameterX {
                    name: name,
                    typ: ParamTypeX::from_str(&arg.typ)?,
                    alias: arg.noalias == Some(false),
                }),
            );
        }

        // Generate channels
        let mut chans = Vec::new();
        let mut inputs = HashMap::new();
        let mut outputs = HashMap::new();
        let mut chan_id = 0;
        for (vert_id, vert) in raw.vertices.iter().enumerate() {
            if vert_id != vert.id as usize {
                return Err(format!(
                    "vertex id does not match with order in the vertices list"
                ));
            }

            inputs.insert(vert.id, Vec::new());

            for (input_port, input) in vert.inputs.iter().enumerate() {
                if input.len() != 1 {
                    return Err(format!("unsupported multiple inputs to the same port"));
                }
                let input = &input[0];

                let chan = match input.kind.as_str() {
                    // Linear channels between two operators
                    "data" => {
                        if let (Some(src_id), Some(src_port)) = (input.id, input.port) {
                            let chan = Rc::new(ChannelX::Async {
                                id: chan_id,
                                src: Port(src_id, src_port),
                                dest: Port(vert.id, input_port as PortIndex),
                            });

                            if !outputs.contains_key(&src_id) {
                                outputs.insert(src_id, IndexMap::new());
                            }

                            if !outputs[&src_id].contains_key(&src_port) {
                                outputs[&src_id].insert(src_port, Vec::new());
                            }

                            outputs[&src_id][&src_port].push(chan.clone());
                            chan
                        } else {
                            return Err(format!("id or port not specified for data channel"));
                        }
                    }
                    // Constant channel
                    "const" => Rc::new(ChannelX::Const {
                        id: chan_id,
                        value: input
                            .value
                            .ok_or(format!("value not available for constant channel"))?,
                        hold: input.hold,
                    }),
                    // Similar to constant channels but use a parameter
                    "xdata" => {
                        let name = input
                            .name
                            .as_ref()
                            .ok_or(format!("param name not available"))?;
                        Rc::new(ChannelX::Param {
                            id: chan_id,
                            param: params
                                .get(name.as_str().into())
                                .ok_or(format!("parameter `{}` does not exist", name))?
                                .clone(),
                            hold: input.hold,
                        })
                    }
                    _ => return Err(format!("unsupported input type {}", input.kind)),
                };

                chans.push(chan.clone());
                inputs[&vert.id].push(chan);

                chan_id += 1;
            }
        }

        // Generate operators
        let mut ops = Vec::new();
        for vert in &raw.vertices {
            ops.push(Rc::new(OperatorX {
                id: vert.id,
                kind: OperatorKind::from_raw(vert)?,
                inputs: inputs.remove(&vert.id).unwrap(),
                outputs: outputs.remove(&vert.id).unwrap_or(IndexMap::new()),
            }));
        }

        Ok(Graph { params, chans, ops })
    }

    fn channel_name(chan: &Channel) -> ChanName {
        format!("C{}", chan.id()).into()
    }

    fn proc_name(op: &Operator) -> ProcName {
        format!("{}{}", op.kind, op.id).into()
    }

    fn param_name(param: &Parameter) -> Rc<str> {
        format!("param_{}", param.name).into()
    }

    fn join_term_types(
        t1: Option<&TermType>,
        t2: Option<&TermType>,
    ) -> Result<Option<TermType>, String> {
        if let (Some(t1), Some(t2)) = (t1, t2) {
            match (t1.as_ref(), t2.as_ref()) {
                (TermTypeX::Base(b1), TermTypeX::Base(b2)) if b1 == b2 => Ok(Some(t1.clone())),
                (TermTypeX::Ref(refs1), TermTypeX::Ref(refs2)) => {
                    let mut refs = IndexSet::new();
                    for ref_type in refs1 {
                        refs.insert(ref_type);
                    }
                    for ref_type in refs2 {
                        refs.insert(ref_type);
                    }
                    Ok(Some(TermTypeX::mut_ref(refs.into_iter())))
                }
                _ => Err(format!("unable to join types {} and {}", t1, t2)),
            }
        } else if let Some(t1) = t1 {
            Ok(Some(t1.clone()))
        } else if let Some(t2) = t2 {
            Ok(Some(t2.clone()))
        } else {
            Ok(None)
        }
    }

    fn const_channel_to_term(word_width: BitVecWidth, chan: &Channel) -> Term {
        match chan.borrow() {
            ChannelX::Const { value, .. } => {
                if *value >= 0 {
                    TermX::bit_vec(*value as u64, word_width)
                } else {
                    TermX::bit_vec(u64::MAX - ((-*value) as u64), word_width)
                }
            }
            ChannelX::Param { param, .. } => match param.typ.as_ref() {
                ParamTypeX::Int(..) => TermX::constant(Self::param_name(param)),
                ParamTypeX::Pointer(..) => {
                    if param.alias {
                        // &mem[param_{name}..]
                        TermX::reference(MutReferenceX::slice(
                            MutReferenceX::base("mem"),
                            Some(&TermX::constant(Self::param_name(param))),
                            None,
                        ))
                    } else {
                        TermX::reference(MutReferenceX::base(Self::param_name(param)))
                    }
                }
            },
            _ => unreachable!(),
        }
    }

    fn recv_from_input(
        opts: &TranslationOptions,
        op: &Operator,
        port: usize,
        var: impl Into<Var>,
        k: impl Borrow<Proc>,
    ) -> Proc {
        let chan = &op.inputs[port];

        if chan.is_hold() {
            // If channel is a hold constant, we simply substitute the value in
            let term = Self::const_channel_to_term(opts.word_width, chan);
            ProcX::substitute(k, &mut IndexMap::from([(var.into(), term.clone())]))
        } else {
            // Else we do a receive
            ProcX::recv(Self::channel_name(chan), var, k)
        }
    }

    fn send_to_outputs(
        op: &Operator,
        port: PortIndex,
        term: impl Borrow<Term>,
        k: impl Borrow<Proc>,
    ) -> Proc {
        let mut proc = k.borrow().clone();
        for output in op.outputs(port) {
            proc = ProcX::send(Self::channel_name(output), term.borrow().clone(), proc);
        }
        proc
    }

    fn gen_io_resources(op: &Operator) -> Vec<ProcResource> {
        let mut res = Vec::new();
        for input in &op.inputs {
            res.push(ProcResourceX::input(Self::channel_name(input)));
        }
        for port in op.outputs.keys() {
            for output in op.outputs(*port) {
                res.push(ProcResourceX::output(Self::channel_name(output)));
            }
        }
        res
    }

    fn add_fresh_perm_var(
        ctx: &mut Ctx,
        param_typs: impl IntoIterator<Item = BaseType>,
    ) -> Result<PermVar, String> {
        let perm_var: PermVar = format!("p{}", ctx.perms.len()).into();
        ctx.add_perm(&PermDeclX::new(&perm_var, param_typs))?;
        Ok(perm_var)
    }

    fn infer_channel_types_from_constants(
        &self,
        opts: &TranslationOptions,
        chan_types: &mut IndexMap<ChannelId, TermType>,
    ) {
        for chan in &self.chans {
            match chan.borrow() {
                ChannelX::Const { id, .. } => {
                    // bv<word width>
                    chan_types.insert(*id, TermTypeX::bit_vec(opts.word_width));
                }
                ChannelX::Param { id, param, .. } => {
                    match param.typ.as_ref() {
                        ParamTypeX::Int(width) => {
                            // bv<width>
                            chan_types.insert(*id, TermTypeX::bit_vec(*width));
                        }
                        ParamTypeX::Pointer(base) => match base.borrow() {
                            ParamTypeX::Int(..) => {
                                if param.alias {
                                    // &mem[*..]
                                    chan_types.insert(
                                        *id,
                                        TermTypeX::mut_ref([MutReferenceTypeX::offset(
                                            MutReferenceTypeX::base("mem"),
                                            MutReferenceIndex::Unknown,
                                        )]),
                                    );
                                } else {
                                    // &param_<name>
                                    chan_types.insert(
                                        *id,
                                        TermTypeX::mut_ref([MutReferenceTypeX::base(
                                            Self::param_name(param),
                                        )]),
                                    );
                                }
                            }
                            ParamTypeX::Pointer(..) => unimplemented!("nested pointer"),
                        },
                    };
                }

                // Otherwise we need to infer from the operator using the channel
                _ => {}
            };
        }
    }

    /// Propagate inferred types to other channels
    fn propagate_inferred_type(
        &self,
        opts: &TranslationOptions,
        chan_types: &mut IndexMap<ChannelId, TermType>,
    ) -> Result<bool, String> {
        let mut changed = false;

        let mut update_chan_typ =
            |chan_types: &mut IndexMap<_, _>, chan: &Channel, typ: &TermType| {
                if !chan_types.contains_key(&chan.id()) {
                    chan_types.insert(chan.id(), typ.clone());
                    // println!("channel {}: {}", chan.id(), typ);
                    changed = true;
                } else if &chan_types[&chan.id()] != typ {
                    chan_types.insert(chan.id(), typ.clone());
                    // println!("channel {}: {}", chan.id(), typ);
                    changed = true;
                }
            };

        for op in &self.ops {
            match op.kind {
                OperatorKind::Add
                | OperatorKind::Sub
                | OperatorKind::Mul
                | OperatorKind::ULT
                | OperatorKind::UGT
                | OperatorKind::ULE
                | OperatorKind::UGE
                | OperatorKind::SLT
                | OperatorKind::SGT
                | OperatorKind::SLE
                | OperatorKind::SGE
                | OperatorKind::SHL
                | OperatorKind::ASHR
                | OperatorKind::LSHR
                | OperatorKind::And
                | OperatorKind::Or
                | OperatorKind::Xor
                | OperatorKind::Eq
                | OperatorKind::Ld
                | OperatorKind::LdSync
                | OperatorKind::St
                | OperatorKind::StSync
                | OperatorKind::Stream(..) =>
                // Always output bv<word_width>
                {
                    for port in op.ports() {
                        for output in op.outputs(*port) {
                            update_chan_typ(
                                chan_types,
                                output,
                                &TermTypeX::bit_vec(opts.word_width),
                            );
                        }
                    }
                }

                OperatorKind::GEP =>
                // Always output references
                {
                    if let Some(input) = op.inputs.get(0) {
                        if let Some(typ) = chan_types.get(&input.id()) {
                            let ref_type = match typ.as_ref() {
                                TermTypeX::Base(_) => {
                                    return Err(format!("base type {} passed into GEP", typ))
                                }
                                TermTypeX::Ref(refs) => {
                                    TermTypeX::mut_ref(refs.iter().map(|r| match r.as_ref() {
                                        MutReferenceTypeX::Base(..) => {
                                            MutReferenceTypeX::offset(r, MutReferenceIndex::Unknown)
                                        }
                                        MutReferenceTypeX::Index(..) => {
                                            MutReferenceTypeX::offset(r, MutReferenceIndex::Unknown)
                                        }
                                        MutReferenceTypeX::Offset(m, ..) => {
                                            MutReferenceTypeX::offset(m, MutReferenceIndex::Unknown)
                                        }
                                    }))
                                }
                            };

                            // Propagate type to outputs
                            for output in op.outputs(0) {
                                update_chan_typ(chan_types, output, &ref_type);
                            }
                        }
                    }
                }

                OperatorKind::Select | OperatorKind::Carry(..) | OperatorKind::Merge =>
                // Output of Merge is the join of input types
                {
                    if let (Some(input1), Some(input2)) = (op.inputs.get(1), op.inputs.get(2)) {
                        if let Some(typ) = Self::join_term_types(
                            chan_types.get(&input1.id()),
                            chan_types.get(&input2.id()),
                        )? {
                            // println!("merged type: {} {}", op.id, typ);
                            for output in op.outputs(0) {
                                update_chan_typ(chan_types, output, &typ);
                            }
                        }
                    }
                }

                OperatorKind::Id => {
                    // Inv is polymorphic on the type of the first input
                    if let Some(input) = op.inputs.get(0) {
                        if let Some(typ) = chan_types.get(&input.id()) {
                            let typ = typ.clone();
                            // Propagate type to outputs
                            for output in op.outputs(0) {
                                update_chan_typ(chan_types, output, &typ);
                            }
                        }
                    }
                }

                OperatorKind::Inv(..) | OperatorKind::Steer(..) => {
                    // Steer is polymorphic on the type of the first input
                    if let Some(input) = op.inputs.get(1) {
                        if let Some(typ) = chan_types.get(&input.id()) {
                            let typ = typ.clone();
                            // Propagate type to outputs
                            for output in op.outputs(0) {
                                update_chan_typ(chan_types, output, &typ);
                            }
                        }
                    }
                }
            }
        }

        Ok(changed)
    }

    /// Generate RipTide function arguments as mutables and constants
    fn gen_function_arguments(
        &self,
        opts: &TranslationOptions,
        ctx: &mut Ctx,
    ) -> Result<(), String> {
        let mut has_alias = false;

        // i32 => constants
        // restrict i32* => mutables
        // alias i32* => merged into one mutable
        for param in self.params.values() {
            match param.typ.borrow() {
                ParamTypeX::Int(width) => {
                    if *width != opts.word_width {
                        return Err(format!(
                            "parameter `{}` has a different width {} from the word width {}",
                            param.name, width, opts.word_width
                        ));
                    }
                    ctx.add_const(&Spanned::new(ConstDeclX {
                        name: Self::param_name(param).into(),
                        typ: BaseType::BitVec(*width),
                    }))?;
                }
                ParamTypeX::Pointer(base) => match base.borrow() {
                    ParamTypeX::Int(width) => {
                        if !param.alias {
                            ctx.add_mut(&Spanned::new(MutDeclX {
                                name: Self::param_name(param).into(),
                                typ: MutTypeX::array(
                                    BaseType::BitVec(opts.word_width),
                                    MutTypeX::base(BaseType::BitVec(*width)),
                                ),
                            }))?;
                        } else {
                            if *width != opts.word_width {
                                return Err(format!("parameter `{}` points to a different width {} from the word width {}", param.name, width, opts.word_width));
                            }
                            has_alias = true;

                            // Add a constant pointer into the memory
                            ctx.add_const(&Spanned::new(ConstDeclX {
                                name: Self::param_name(param).into(),
                                typ: BaseType::BitVec(opts.word_width),
                            }))?;
                        }
                    }
                    ParamTypeX::Pointer(..) => unimplemented!("nested pointer"),
                },
            }
        }

        // All pointers that could be aliasing are put into
        // a "mem: [[bv32]]" mutable
        if has_alias {
            ctx.add_mut(&Spanned::new(MutDeclX {
                name: "mem".into(),
                typ: MutTypeX::array(
                    BaseType::BitVec(opts.word_width),
                    MutTypeX::base(BaseType::BitVec(opts.word_width)),
                ),
            }))?;
        }

        Ok(())
    }

    fn gen_channels(&self, opts: &TranslationOptions, ctx: &mut Ctx) -> Result<(), String> {
        let mut chan_types = IndexMap::new();

        // Infer types of constant channels
        Self::infer_channel_types_from_constants(&self, opts, &mut chan_types);

        // Do a "dataflow analysis" to propagate type information until convergence
        while Self::propagate_inferred_type(&self, opts, &mut chan_types)? {}

        // Generate channels
        for chan in &self.chans {
            if !chan_types.contains_key(&chan.id()) {
                return Err(format!("unable to infer the type of channel {:?}", chan));
            }

            let chan_type = &chan_types[&chan.id()];

            let perm_var = Self::add_fresh_perm_var(
                ctx,
                match chan_type.borrow() {
                    TermTypeX::Base(b @ BaseType::BitVec(..)) => vec![b.clone()],
                    _ => vec![],
                },
            )?;

            // chan c<id>: <type> | p(c<id>) (if type is bv)
            // chan c<id>: <type> | p() (otherwise)
            ctx.add_chan(&Spanned::new(ChanDeclX {
                name: Self::channel_name(chan),
                typ: chan_type.clone(),
                perm: PermissionX::var(
                    &perm_var,
                    match chan_type.borrow() {
                        TermTypeX::Base(BaseType::BitVec(..)) => {
                            vec![TermX::var(&Self::channel_name(chan))]
                        }
                        _ => vec![],
                    },
                ),
            }))?;
        }

        Ok(())
    }

    /// Generate an entry process (and potentially some auxiliary processes)
    /// for the given operator, and return the entry process name
    pub fn gen_operator(
        &self,
        op: &Operator,
        opts: &TranslationOptions,
        ctx: &mut Ctx,
    ) -> Result<ProcName, String> {
        let name = Self::proc_name(op);
        let perm_var = Self::add_fresh_perm_var(ctx, [])?;

        let mut res = vec![ProcResourceX::perm(PermissionX::var(
            &perm_var,
            [] as [Term; 0],
        ))];
        res.extend(Self::gen_io_resources(op));

        match op.kind {
            OperatorKind::Id => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv a <= port 0;
                    send TermX::var("a") => port 0;
                    call name;
            })?,

            OperatorKind::Add => arith_op_translation!(opts, op, ctx, name, res, bvadd),
            OperatorKind::Sub => arith_op_translation!(opts, op, ctx, name, res, bvsub),
            OperatorKind::Mul => arith_op_translation!(opts, op, ctx, name, res, bvmul),

            OperatorKind::ULT => pred_op_translation!(opts, op, ctx, name, res, bvult),
            OperatorKind::UGT => pred_op_translation!(opts, op, ctx, name, res, bvugt),
            OperatorKind::ULE => pred_op_translation!(opts, op, ctx, name, res, bvule),
            OperatorKind::UGE => pred_op_translation!(opts, op, ctx, name, res, bvuge),
            OperatorKind::SLT => pred_op_translation!(opts, op, ctx, name, res, bvslt),
            OperatorKind::SGT => pred_op_translation!(opts, op, ctx, name, res, bvsgt),
            OperatorKind::SLE => pred_op_translation!(opts, op, ctx, name, res, bvsle),
            OperatorKind::SGE => pred_op_translation!(opts, op, ctx, name, res, bvsge),

            OperatorKind::SHL => arith_op_translation!(opts, op, ctx, name, res, bvshl),
            OperatorKind::ASHR => arith_op_translation!(opts, op, ctx, name, res, bvashr),
            OperatorKind::LSHR => arith_op_translation!(opts, op, ctx, name, res, bvlshr),

            OperatorKind::And => arith_op_translation!(opts, op, ctx, name, res, bvand),
            OperatorKind::Or => arith_op_translation!(opts, op, ctx, name, res, bvor),
            OperatorKind::Xor => arith_op_translation!(opts, op, ctx, name, res, bvxor),

            OperatorKind::Eq => pred_op_translation!(opts, op, ctx, name, res, eq),

            OperatorKind::Select => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv d <= port 0;
                    recv a <= port 1;
                    recv b <= port 2;
                    if (TermX::not(TermX::eq(
                        TermX::var("d"),
                        TermX::bit_vec(0, opts.word_width),
                    ))) {
                        send TermX::var("a") => port 0;
                        call name;
                    } else {
                        send TermX::var("b") => port 0;
                        call name;
                    }
            })?,

            OperatorKind::GEP => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv r <= port 0;
                    recv i <= port 1;
                    // *r[i..]
                    send TermX::reference(MutReferenceX::slice(
                        MutReferenceX::deref(TermX::var("r")),
                        Some(&TermX::var("i")),
                        None,
                    )) => port 0;
                    call name;
            })?,

            OperatorKind::Ld => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv r <= port 0;
                    recv i <= port 1;
                    read x <= MutReferenceX::index(
                        MutReferenceX::deref(TermX::var("r")),
                        TermX::var("i"),
                    );
                    send TermX::var("x") => port 0;
                    call name;
            })?,

            OperatorKind::LdSync => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv r <= port 0;
                    recv i <= port 1;
                    recv s <= port 2;
                    read x <= MutReferenceX::index(
                        MutReferenceX::deref(TermX::var("r")),
                        TermX::var("i"),
                    );
                    send TermX::var("x") => port 0;
                    call name;
            })?,

            OperatorKind::St => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv r <= port 0;
                    recv i <= port 1;
                    recv x <= port 2;
                    write TermX::var("x") => MutReferenceX::index(
                        MutReferenceX::deref(TermX::var("r")),
                        TermX::var("i"),
                    );
                    send TermX::bit_vec(0, opts.word_width) => port 0;
                    call name;
            })?,

            OperatorKind::StSync => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv r <= port 0;
                    recv i <= port 1;
                    recv x <= port 2;
                    recv s <= port 3;
                    write TermX::var("x") => MutReferenceX::index(
                        MutReferenceX::deref(TermX::var("r")),
                        TermX::var("i"),
                    );
                    send TermX::bit_vec(0, opts.word_width) => port 0;
                    call name;
            })?,

            OperatorKind::Steer(pred) => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv d <= port 0;
                    recv x <= port 1;
                    if (if pred {
                        TermX::not(TermX::eq(
                            TermX::var("d"),
                            TermX::bit_vec(0, opts.word_width),
                        ))
                    } else {
                        TermX::eq(TermX::var("d"), TermX::bit_vec(0, opts.word_width))
                    }) {
                        send TermX::var("x") => port 0;
                        call name;
                    } else {
                        call name;
                    }
            })?,

            OperatorKind::Inv(pred) => {
                let state1: ProcName = name.clone();
                let state2: ProcName = format!("{}Loop", name).into();

                ctx.add_proc(&riptide! {
                    (opts, op)
                    proc state1; res =>
                        recv a <= port 1;
                        send TermX::var("a") => port 0;
                        call state1;
                })?;

                // Generate a new permission var for the second state
                let inv_type = ctx.chans[&Self::channel_name(&op.inputs[1])].typ.clone();

                let mut res = match inv_type.as_ref() {
                    TermTypeX::Base(base) => {
                        let perm_var = Self::add_fresh_perm_var(ctx, [base.clone()])?;
                        vec![ProcResourceX::perm(PermissionX::var(
                            &perm_var,
                            [TermX::var("a")],
                        ))]
                    }
                    TermTypeX::Ref(..) => {
                        // TODO: reference dependency not supported
                        let perm_var = Self::add_fresh_perm_var(ctx, [])?;
                        vec![ProcResourceX::perm(PermissionX::var(
                            &perm_var,
                            [] as [Term; 0],
                        ))]
                    }
                };
                res.extend(Self::gen_io_resources(op));

                ctx.add_proc(&riptide! {
                    (opts, op)
                    proc state2, ProcParamX::new("a", inv_type); res =>
                        recv d <= port 0;
                        if (if pred {
                            TermX::not(TermX::eq(
                                TermX::var("d"),
                                TermX::bit_vec(0, opts.word_width),
                            ))
                        } else {
                            TermX::eq(TermX::var("d"), TermX::bit_vec(0, opts.word_width))
                        }) {
                            send TermX::var("a") => port 0;
                            call state2, TermX::var("a");
                        } else {
                            call state1;
                        }
                })?;
            }

            OperatorKind::Stream(pred) => {
                let state1: ProcName = name.clone();
                let state2: ProcName = format!("{}Loop", name).into();

                ctx.add_proc(&riptide! {
                    (opts, op)
                    proc state1; res =>
                        recv start <= port 0;
                        recv bound <= port 1;
                        recv step <= port 2;
                        call state2, TermX::var("start"), TermX::var("bound"), TermX::var("step");
                })?;

                // Generate a new permission var for the second state
                let perm_var = Self::add_fresh_perm_var(
                    ctx,
                    [
                        BaseType::BitVec(opts.word_width),
                        BaseType::BitVec(opts.word_width),
                        BaseType::BitVec(opts.word_width),
                    ],
                )?;

                let mut res = vec![
                    // p(start, bound, step)
                    ProcResourceX::perm(PermissionX::var(
                        &perm_var,
                        [TermX::var("start"), TermX::var("bound"), TermX::var("step")],
                    )),
                ];
                res.extend(Self::gen_io_resources(op));

                ctx.add_proc(&riptide! {
                    (opts, op)
                    proc state2,
                        ProcParamX::new("start", TermTypeX::bit_vec(opts.word_width)),
                        ProcParamX::new("bound", TermTypeX::bit_vec(opts.word_width)),
                        ProcParamX::new("step", TermTypeX::bit_vec(opts.word_width)); res =>
                        if (TermX::bvslt(TermX::var("start"), TermX::var("bound"))) {
                            send TermX::var("start") => port 0;
                            send TermX::bit_vec(if pred { 1 } else { 0 }, opts.word_width) => port 1;
                            call state2,
                                TermX::bvadd(TermX::var("start"), TermX::var("step")),
                                TermX::var("bound"),
                                TermX::var("step");
                        } else {
                            send TermX::bit_vec(if pred { 0 } else { 1 }, opts.word_width) => port 1;
                            call state1;
                        }
                })?;
            }

            OperatorKind::Carry(pred) => {
                let state1: ProcName = name.clone();
                let state2: ProcName = format!("{}Loop", name).into();

                ctx.add_proc(&riptide! {
                    (opts, op)
                    proc state1; res =>
                        recv a <= port 1;
                        send TermX::var("a") => port 0;
                        call state2;
                })?;

                // Generate a new permission var for the second state
                let perm_var = Self::add_fresh_perm_var(ctx, [])?;

                let mut res = vec![ProcResourceX::perm(PermissionX::var(
                    &perm_var,
                    [] as [Term; 0],
                ))];
                res.extend(Self::gen_io_resources(op));

                ctx.add_proc(&riptide! {
                    (opts, op)
                    proc state2; res =>
                        recv d <= port 0;
                        if (if pred {
                            TermX::not(TermX::eq(
                                TermX::var("d"),
                                TermX::bit_vec(0, opts.word_width),
                            ))
                        } else {
                            TermX::eq(TermX::var("d"), TermX::bit_vec(0, opts.word_width))
                        }) {
                            recv b <= port 2;
                            send TermX::var("b") => port 0;
                            call state2;
                        } else {
                            call state1;
                        }
                })?;
            }

            OperatorKind::Merge => ctx.add_proc(&riptide! {
                (opts, op)
                proc name; res =>
                    recv d <= port 0;
                    if (TermX::not(TermX::eq(
                        TermX::var("d"),
                        TermX::bit_vec(0, opts.word_width),
                    ))) {
                        recv a <= port 1;
                        send TermX::var("a") => port 0;
                        call name;
                    } else {
                        recv b <= port 2;
                        send TermX::var("b") => port 0;
                        call name;
                    }
            })?,
        }

        Ok(name)
    }

    pub fn to_program(&self, opts: &TranslationOptions) -> Result<Ctx, String> {
        let mut ctx = Ctx::new();

        self.gen_function_arguments(opts, &mut ctx)?;
        self.gen_channels(opts, &mut ctx)?;

        // Generate entry point process
        // which would push all constant, non-hold values
        let mut entry_proc = ProcX::skip();

        for chan in &self.chans {
            if chan.is_constant() && !chan.is_hold() {
                entry_proc = ProcX::send(
                    Self::channel_name(chan),
                    Self::const_channel_to_term(opts.word_width, chan),
                    entry_proc,
                );
            }
        }

        // Generate each operator
        for op in &self.ops {
            let name = self.gen_operator(op, opts, &mut ctx)?;
            entry_proc = ProcX::par(ProcX::call(name, [] as [Term; 0]), entry_proc);
        }

        // Finally, generate an entry process `Program`
        ctx.add_proc(&ProcDeclX::new_all_res(
            "Program",
            [] as [ProcParam; 0],
            entry_proc,
        ))?;

        Ok(ctx)
    }
}

impl fmt::Display for OperatorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            OperatorKind::Id => write!(f, "Id"),
            OperatorKind::Add => write!(f, "Add"),
            OperatorKind::Sub => write!(f, "Sub"),
            OperatorKind::Mul => write!(f, "Mul"),
            OperatorKind::ULT => write!(f, "ULT"),
            OperatorKind::UGT => write!(f, "UGT"),
            OperatorKind::ULE => write!(f, "ULE"),
            OperatorKind::UGE => write!(f, "UGE"),
            OperatorKind::SLT => write!(f, "SLT"),
            OperatorKind::SGT => write!(f, "SGT"),
            OperatorKind::SLE => write!(f, "SLE"),
            OperatorKind::SGE => write!(f, "SGE"),
            OperatorKind::SHL => write!(f, "SHL"),
            OperatorKind::ASHR => write!(f, "ASHR"),
            OperatorKind::LSHR => write!(f, "LSHR"),
            OperatorKind::And => write!(f, "And"),
            OperatorKind::Or => write!(f, "Or"),
            OperatorKind::Xor => write!(f, "Xor"),
            OperatorKind::Eq => write!(f, "Eq"),
            OperatorKind::Select => write!(f, "Select"),
            OperatorKind::GEP => write!(f, "GEP"),
            OperatorKind::Stream(pred) => write!(f, "Stream{}", if *pred { "T" } else { "F" }),
            OperatorKind::Carry(pred) => write!(f, "Carry{}", if *pred { "T" } else { "F" }),
            OperatorKind::Merge => write!(f, "Merge"),
            OperatorKind::Inv(pred) => write!(f, "Inv{}", if *pred { "T" } else { "F" }),
            OperatorKind::Steer(pred) => write!(f, "Steer{}", if *pred { "T" } else { "F" }),
            OperatorKind::Ld => write!(f, "Ld"),
            OperatorKind::LdSync => write!(f, "LdSync"),
            OperatorKind::St => write!(f, "St"),
            OperatorKind::StSync => write!(f, "StSync"),
        }
    }
}
