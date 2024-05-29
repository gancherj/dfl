use std::{borrow::Borrow, rc::Rc};
use std::{fmt, io};

use im::HashMap;
use indexmap::IndexMap;
use serde::{Serialize, Deserialize};

use crate::ast::{Program, ConstDeclX, BaseType};
use crate::span::Spanned;
use crate::{BitVecWidth, ChanDeclX, ChanName, Decl, MutDeclX, MutName, MutReferenceIndex, MutReferenceTypeX, MutReferenceX, MutTypeX, PermDeclX, PermVar, PermissionX, Proc, ProcDeclX, ProcName, ProcParam, ProcResource, ProcResourceX, ProcX, Term, TermType, TermTypeX, TermX, Var};

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
    Async { id: ChannelId, src: Port, dest: Port },
    Const { id: ChannelId, value: ConstValue, hold: bool },
    Param { id: ChannelId, param: Parameter, hold: bool },
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
    Add,
    Ult,
    Carry(bool),
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
            _ => Err(format!("unsupported parameter type `{}`", s.as_ref()))
        }
    }
}

impl OperatorKind {
    fn from_raw(raw: &RawVertex) -> Result<OperatorKind, String> {
        match raw.op.as_str() {
            "ARITH_CFG_OP_ADD" => Ok(OperatorKind::Add),
            "ARITH_CFG_OP_ULT" => Ok(OperatorKind::Ult),
            "CF_CFG_OP_CARRY" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Carry(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Carry(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for carry", pred)),
                None => Err(format!("predicate not specified for carry"))
            }
            "CF_CFG_OP_INVARIANT" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Inv(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Inv(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for invariant", pred)),
                None => Err(format!("predicate not specified for invariant"))
            }
            "CF_CFG_OP_STEER" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Steer(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Steer(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for steer", pred)),
                None => Err(format!("predicate not specified for steer"))
            }
            "MEM_CFG_OP_LOAD" => match raw.inputs.len() {
                2 => Ok(OperatorKind::Ld),
                3 => Ok(OperatorKind::LdSync),
                _ => Err(format!("load operator expected to have either 2 or 3 inputs, got {}", raw.inputs.len()))
            }
            "MEM_CFG_OP_STORE" => match raw.inputs.len() {
                3 => Ok(OperatorKind::St),
                4 => Ok(OperatorKind::StSync),
                _ => Err(format!("store operator expected to have either 3 or 4 inputs, got {}", raw.inputs.len()))
            }
            _ => Err(format!("unsupported operator `{}`", raw.op)),
        }
    }
}

impl OperatorX {
    pub fn outputs(&self, port: PortIndex) -> impl Iterator<Item=&Channel> {
        self.outputs.get(&port).map_or([].iter(), |v| v.iter())
    }
}

impl Graph {
    pub fn from_reader(reader: impl io::Read) -> io::Result<Graph> {
        Graph::from_raw(&serde_json::from_reader(reader)?).map_err(|msg| io::Error::other(msg))
    }

    fn from_raw(raw: &RawGraph) -> Result<Graph, String> {
        let mut params = IndexMap::new();
        for arg in &raw.info.args {
            let name: ParamName = arg.name.as_str().into();
            params.insert(name.clone(), Rc::new(ParameterX {
                name: name,
                typ: ParamTypeX::from_str(&arg.typ)?,
                alias: arg.noalias == Some(false),
            }));
        }

        // Generate channels
        let mut chans = Vec::new();
        let mut inputs = HashMap::new();
        let mut outputs = HashMap::new();
        let mut chan_id = 0;
        for (vert_id, vert) in raw.vertices.iter().enumerate() {
            if vert_id != vert.id as usize {
                return Err(format!("vertex id does not match with order in the vertices list"));
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
                    "const" =>
                        Rc::new(ChannelX::Const {
                            id: chan_id,
                            value: input.value.ok_or(format!("value not available for constant channel"))?,
                            hold: input.hold,
                        }),
                    // Similar to constant channels but use a parameter
                    "xdata" => {
                        let name = input.name.as_ref().ok_or(format!("param name not available"))?;
                        Rc::new(ChannelX::Param {
                            id: chan_id,
                            param: params.get(name.as_str().into())
                                .ok_or(format!("parameter `{}` does not exist", name))?.clone(),
                            hold: input.hold,
                        })
                    },
                    _ => return Err(format!("unsupported input type {}", input.kind))
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

    fn join_term_types(t1: &TermType, t2: &TermType) -> Result<TermType, String> {
        match (t1.as_ref(), t2.as_ref()) {
            (TermTypeX::Base(b1), TermTypeX::Base(b2)) if b1 == b2 => Ok(t1.clone()),
            (TermTypeX::Ref(refs1), TermTypeX::Ref(refs2)) =>
                Ok(TermTypeX::mut_ref(refs1.iter().chain(refs2))),
            _ => Err(format!("unable to join types {} and {}", t1, t2)),
        }
    }

    fn const_channel_to_term(word_width: BitVecWidth, chan: &Channel) -> Term {
        match chan.borrow() {
            ChannelX::Const { value, .. } =>
                if *value >= 0 {
                    TermX::bit_vec(*value as u64, word_width)
                } else {
                    TermX::bit_vec(u64::MAX - ((-*value) as u64), word_width)
                }
            ChannelX::Param { param, .. } =>
                match param.typ.as_ref() {
                    ParamTypeX::Int(..) => TermX::constant(Self::param_name(param)),
                    ParamTypeX::Pointer(..) =>
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
            _ => unreachable!()
        }
    }

    fn recv_from_input(word_width: BitVecWidth, op: &Operator, port: usize, var: impl Into<Var>, k: impl Borrow<Proc>) -> Proc {
        let chan = &op.inputs[port];

        if chan.is_hold() {
            // If channel is a hold constant, we simply substitute the value in
            let term = Self::const_channel_to_term(word_width, chan);
            ProcX::substitute(k, &mut IndexMap::from([(var.into(), term.clone())]))
        } else {
            // Else we do a receive
            ProcX::recv(Self::channel_name(chan), var, k)
        }
    }

    fn send_to_outputs(op: &Operator, port: PortIndex, term: impl Borrow<Term>, k: impl Borrow<Proc>) -> Proc {
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

    pub fn to_program(&self, word_width: BitVecWidth) -> Result<Program, String> {
        let mut consts = Vec::new();
        let mut muts = Vec::new();
        let mut perms = Vec::new();
        let mut chans = Vec::new();
        let mut procs = Vec::new();

        let mut has_alias = false;

        // Generate function arguments
        for param in self.params.values() {
            match param.typ.borrow() {
                ParamTypeX::Int(width) => {
                    if *width != word_width {
                        return Err(format!("parameter `{}` has a different width {} from the word width {}", param.name, width, word_width));
                    }
                    consts.push(Spanned::new(ConstDeclX {
                        name: Self::param_name(param).into(),
                        typ: BaseType::BitVec(*width),
                    }));
                }
                ParamTypeX::Pointer(base) =>
                    match base.borrow() {
                        ParamTypeX::Int(width) => {
                            if !param.alias {
                                muts.push(Spanned::new(MutDeclX {
                                    name: Self::param_name(param).into(),
                                    typ: MutTypeX::array(
                                        BaseType::BitVec(word_width),
                                        MutTypeX::base(BaseType::BitVec(*width)),
                                    ),
                                }));
                            } else {
                                if *width != word_width {
                                    return Err(format!("parameter `{}` points to a different width {} from the word width {}", param.name, width, word_width));
                                }
                                has_alias = true;

                                // Add a constant pointer into the memory
                                consts.push(Spanned::new(ConstDeclX {
                                    name: Self::param_name(param).into(),
                                    typ: BaseType::BitVec(word_width),
                                }));
                            }
                        },
                        ParamTypeX::Pointer(..) => unimplemented!("nested pointer"),
                    }
            }
        }

        // All pointers that could be aliasing are put into
        // a "mem: [[bv32]]" mutable
        if has_alias {
            muts.push(Spanned::new(MutDeclX {
                name: "mem".into(),
                typ: MutTypeX::array(
                    BaseType::BitVec(word_width),
                    MutTypeX::base(BaseType::BitVec(word_width)),
                ),
            }));
        }

        // Infer types of constant channels
        let mut chan_types = IndexMap::new();
        for chan in &self.chans {
            match chan.borrow() {
                ChannelX::Const { id, .. } => {
                    // bv<word width>
                    chan_types.insert(*id, TermTypeX::bit_vec(word_width));
                }
                ChannelX::Param { id, param, .. } => {
                    match param.typ.as_ref() {
                        ParamTypeX::Int(width) => {
                            // bv<width>
                            chan_types.insert(*id, TermTypeX::bit_vec(*width));
                        }
                        ParamTypeX::Pointer(base) =>
                            match base.borrow() {
                                ParamTypeX::Int(..) =>
                                    if param.alias {
                                        // &mem[*..]
                                        chan_types.insert(*id, TermTypeX::mut_ref([
                                            MutReferenceTypeX::offset(
                                                MutReferenceTypeX::base("mem"),
                                                MutReferenceIndex::Unknown,
                                            )
                                        ]));
                                    } else {
                                        // &param_<name>
                                        chan_types.insert(*id, TermTypeX::mut_ref([
                                            MutReferenceTypeX::base(Self::param_name(param)),
                                        ]));
                                    }
                                ParamTypeX::Pointer(..) => unimplemented!("nested pointer"),
                            }
                    };
                }

                // Otherwise we need to infer from the operator using the channel
                _ => {}
            };
        }

        // Do a "dataflow analysis" to propagate type information until convergence
        loop {
            let mut changed = false;
            for op in &self.ops {
                match op.kind {
                    OperatorKind::Add | OperatorKind::Ult |
                    OperatorKind::Ld | OperatorKind::LdSync |
                    OperatorKind::St | OperatorKind::StSync =>
                        // Always output bv<word_width>
                        for output in op.outputs(0) {
                            if !chan_types.contains_key(&output.id()) {
                                chan_types.insert(output.id(), TermTypeX::bit_vec(word_width));
                                // println!("channel {}: {}", output.id(), TermTypeX::bit_vec(word_width));
                                changed = true;
                            }
                        }

                    OperatorKind::Carry(..) =>
                        // Output of Carry is the join of input types
                        // TODO: consider self loops
                        if let (Some(input1), Some(input2)) = (op.inputs.get(1), op.inputs.get(2)) {
                            if chan_types.contains_key(&input1.id()) && chan_types.contains_key(&input2.id()) {
                                let typ = Self::join_term_types(&chan_types[&input1.id()], &chan_types[&input2.id()])?;
                                for output in op.outputs(0) {
                                    if !chan_types.contains_key(&output.id()) {
                                        chan_types.insert(output.id(), typ.clone());
                                        // println!("channel {}: {}", output.id(), typ);
                                        changed = true;
                                    }
                                }
                            }
                        }

                    OperatorKind::Inv(..) => {
                        // Inv is polymorphic on the type of the first input
                        if let Some(input) = op.inputs.get(1) {
                            if chan_types.contains_key(&input.id()) {
                                // Propagate type to outputs
                                for output in op.outputs(0) {
                                    if !chan_types.contains_key(&output.id()) {
                                        chan_types.insert(output.id(), chan_types[&input.id()].clone());
                                        // println!("channel {}: {}", output.id(), chan_types[&input.id()].clone());
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }

                    OperatorKind::Steer(..) => {
                        // Steer is polymorphic on the type of the first input
                        if let Some(input) = op.inputs.get(1) {
                            if chan_types.contains_key(&input.id()) {
                                // Propagate type to outputs
                                for output in op.outputs(0) {
                                    if !chan_types.contains_key(&output.id()) {
                                        chan_types.insert(output.id(), chan_types[&input.id()].clone());
                                        // println!("channel {}: {}", output.id(), chan_types[&input.id()].clone());
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if !changed {
                break;
            }
        }

        // Generate channels
        for chan in &self.chans {
            if !chan_types.contains_key(&chan.id()) {
                return Err(format!("unable to infer the type of channel {:?}", chan));
            }

            let chan_type = &chan_types[&chan.id()];

            let perm_var: PermVar = format!("p{}", perms.len()).into();
            perms.push(Spanned::new(PermDeclX {
                name: perm_var.clone(),
                param_typs: match chan_type.borrow() {
                    TermTypeX::Base(b@BaseType::BitVec(..)) => vec![b.clone()],
                    _ => vec![],
                },
            }));

            // chan c<id>: <type> | p(c<id>) (if type is bv)
            // chan c<id>: <type> | p() (otherwise)
            chans.push(Spanned::new(ChanDeclX {
                name: Self::channel_name(chan),
                typ: chan_type.clone(),
                perm: PermissionX::var(perm_var, match chan_type.borrow() {
                    TermTypeX::Base(BaseType::BitVec(..)) => vec![TermX::var(&Self::channel_name(chan))],
                    _ => vec![],
                }),
            }))
        }

        // Generate entry point process
        // which would push all constant, non-hold values
        let mut entry_proc = ProcX::skip();

        for chan in &self.chans {
            if chan.is_constant() && !chan.is_hold() {
                entry_proc = ProcX::send(Self::channel_name(chan), Self::const_channel_to_term(word_width, chan), entry_proc);
            }
        }

        // Generate concrete processes
        for op in &self.ops {
            let name = Self::proc_name(op);

            let perm_var: PermVar = format!("p{}", perms.len()).into();
            perms.push(Spanned::new(PermDeclX {
                name: perm_var.clone(),
                param_typs: vec![],
            }));

            let mut res = vec![ProcResourceX::perm(PermissionX::var(perm_var, [] as [Term; 0]))];
            res.extend(Self::gen_io_resources(op));

            let recurse = ProcX::call(name.clone(), [] as [Term; 0]);

            entry_proc = ProcX::par(recurse.clone(), entry_proc);

            match op.kind {
                OperatorKind::Add =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "a",
                            Self::recv_from_input(word_width, op, 1, "b",
                            Self::send_to_outputs(op, 0, TermX::bvadd(TermX::var("a"), TermX::var("b")),
                            recurse))),
                    })),

                OperatorKind::Ult =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "a",
                            Self::recv_from_input(word_width, op, 1, "b",
                            ProcX::ite(
                                TermX::bvult(TermX::var("a"), TermX::var("b")),
                                Self::send_to_outputs(op, 0, TermX::bit_vec(1, word_width),
                                    recurse.clone()),
                                Self::send_to_outputs(op, 0, TermX::bit_vec(0, word_width),
                                    recurse.clone()),
                            ))),
                    })),

                OperatorKind::Ld =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "r",
                            Self::recv_from_input(word_width, op, 1, "i",
                            ProcX::read(MutReferenceX::index(MutReferenceX::deref(TermX::var("r")), TermX::var("i")), "v",
                            Self::send_to_outputs(op, 0, TermX::var("v"),
                            recurse)))),
                    })),

                OperatorKind::LdSync =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "r",
                            Self::recv_from_input(word_width, op, 1, "i",
                            Self::recv_from_input(word_width, op, 2, "s",
                            ProcX::read(MutReferenceX::index(MutReferenceX::deref(TermX::var("r")), TermX::var("i")), "v",
                            Self::send_to_outputs(op, 0, TermX::var("v"),
                            recurse))))),
                    })),

                OperatorKind::St =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "r",
                            Self::recv_from_input(word_width, op, 1, "i",
                            Self::recv_from_input(word_width, op, 2, "v",
                            ProcX::write(MutReferenceX::index(MutReferenceX::deref(TermX::var("r")), TermX::var("i")), TermX::var("v"),
                            Self::send_to_outputs(op, 0, TermX::bit_vec(0, word_width),
                            recurse.clone()))))),
                    })),

                OperatorKind::StSync =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "r",
                            Self::recv_from_input(word_width, op, 1, "i",
                            Self::recv_from_input(word_width, op, 2, "v",
                            Self::recv_from_input(word_width, op, 3, "s",
                            ProcX::write(MutReferenceX::index(MutReferenceX::deref(TermX::var("r")), TermX::var("i")), TermX::var("v"),
                            Self::send_to_outputs(op, 0, TermX::bit_vec(0, word_width),
                            recurse)))))),
                    })),

                OperatorKind::Steer(pred) =>
                    procs.push(Spanned::new(ProcDeclX {
                        name: name.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "d",
                            Self::recv_from_input(word_width, op, 1, "v",
                            ProcX::ite(
                                if pred {
                                    TermX::not(TermX::eq(TermX::var("d"), TermX::bit_vec(0, word_width)))
                                } else {
                                    TermX::eq(TermX::var("d"), TermX::bit_vec(0, word_width))
                                },
                                Self::send_to_outputs(op, 0, TermX::var("v"),
                                    recurse.clone()),
                                recurse.clone(),
                            ))),
                    })),

                OperatorKind::Inv(pred) => {
                    let state1: ProcName = name.clone();
                    let state2: ProcName = format!("{}Loop", name).into();

                    let inv_type = &chan_types[&op.inputs[1].id()];

                    procs.push(Spanned::new(ProcDeclX {
                        name: state1.clone(), params: vec![], res: res.clone(), all_res: false,
                        body: Self::recv_from_input(word_width, op, 1, "a",
                            Self::send_to_outputs(op, 0, TermX::var("a"),
                            ProcX::call(state2.clone(), [TermX::var("a")]))),
                    }));

                    procs.push(Spanned::new(ProcDeclX {
                        name: state2.clone(),
                        params: vec![ProcParam { name: "a".into(), typ: inv_type.clone() }],
                        res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "d",
                            ProcX::ite(
                                if pred {
                                    TermX::not(TermX::eq(TermX::var("d"), TermX::bit_vec(0, word_width)))
                                } else {
                                    TermX::eq(TermX::var("d"), TermX::bit_vec(0, word_width))
                                },
                                Self::send_to_outputs(op, 0, TermX::var("a"),
                                    ProcX::call(state2.clone(), [TermX::var("a")])),
                                ProcX::call(state1.clone(), [] as [Term; 0]),
                            )),
                    }));
                }

                OperatorKind::Carry(pred) => {
                    let state1: ProcName = name.clone();
                    let state2: ProcName = format!("{}Loop", name).into();

                    procs.push(Spanned::new(ProcDeclX {
                        name: state1.clone(), params: vec![], res: res.clone(), all_res: false,
                        body: Self::recv_from_input(word_width, op, 1, "a",
                            Self::send_to_outputs(op, 0, TermX::var("a"),
                            ProcX::call(state2.clone(), [] as [Term; 0]))),
                    }));

                    procs.push(Spanned::new(ProcDeclX {
                        name: state2.clone(), params: vec![], res, all_res: false,
                        body: Self::recv_from_input(word_width, op, 0, "d",
                            ProcX::ite(
                                if pred {
                                    TermX::not(TermX::eq(TermX::var("d"), TermX::bit_vec(0, word_width)))
                                } else {
                                    TermX::eq(TermX::var("d"), TermX::bit_vec(0, word_width))
                                },
                                Self::recv_from_input(word_width, op, 2, "b",
                                    Self::send_to_outputs(op, 0, TermX::var("b"),
                                    ProcX::call(state2.clone(), [] as [Term; 0]))),
                                ProcX::call(state1.clone(), [] as [Term; 0]),
                            )),
                    }));
                }
                    
            }
        }

        // Finally, generate an entry process `Program`
        procs.push(Spanned::new(ProcDeclX {
            name: "Program".into(),
            params: vec![],
            res: vec![],
            all_res: true,
            body: entry_proc,
        }));

        Ok(Program {
            decls: consts.into_iter().map(|d| Decl::Const(d))
                .chain(muts.into_iter().map(|d| Decl::Mut(d)))
                .chain(perms.into_iter().map(|d| Decl::Perm(d)))
                .chain(chans.into_iter().map(|d| Decl::Chan(d)))
                .chain(procs.into_iter().map(|d| Decl::Proc(d)))
                .collect(),
        })
    }
}

impl fmt::Display for OperatorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            OperatorKind::Add => write!(f, "Add"),
            OperatorKind::Ult => write!(f, "Ult"),
            OperatorKind::Carry(pred) => write!(f, "Carry{}", if *pred { "T" } else { "F" }),
            OperatorKind::Inv(pred) => write!(f, "Inv{}", if *pred { "T" } else { "F" }),
            OperatorKind::Steer(pred) => write!(f, "Steer{}", if *pred { "T" } else { "F" }),
            OperatorKind::Ld => write!(f, "Ld"),
            OperatorKind::LdSync => write!(f, "LdSync"),
            OperatorKind::St => write!(f, "St"),
            OperatorKind::StSync => write!(f, "StSync"),
        }
    }
}
