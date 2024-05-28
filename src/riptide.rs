use std::{borrow::Borrow, rc::Rc};
use std::io;

use im::HashMap;
use indexmap::IndexMap;
use serde::{Serialize, Deserialize};

use crate::ast::{Program, ConstDeclX, BaseType};
use crate::span::Spanned;
use crate::{BitVecWidth, Decl, MutDeclX, MutTypeX};

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

#[derive(Debug)]
pub enum OperatorKind {
    Add,
    Ult,
    Carry(bool),
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
            "CF_CFG_OP_STEER" => match &raw.pred {
                Some(pred) if pred == "CF_CFG_PRED_TRUE" => Ok(OperatorKind::Carry(true)),
                Some(pred) if pred == "CF_CFG_PRED_FALSE" => Ok(OperatorKind::Carry(false)),
                Some(pred) => Err(format!("unknown predicate `{}` for carry", pred)),
                None => Err(format!("predicate not specified for carry"))
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

    pub fn to_program(&self, word_width: BitVecWidth) -> Program {
        let mut consts = Vec::new();
        let mut muts = Vec::new();

        let mut has_alias = false;

        // Generate function arguments
        for param in self.params.values() {
            match param.typ.borrow() {
                ParamTypeX::Int(width) => {
                    consts.push(Spanned::new(ConstDeclX {
                        name: format!("param_{}", param.name).into(),
                        typ: BaseType::BitVec(*width),
                    }));
                }
                ParamTypeX::Pointer(base) =>
                    match base.borrow() {
                        ParamTypeX::Int(width) => {
                            if !param.alias {
                                muts.push(Spanned::new(MutDeclX {
                                    name: format!("param_{}", param.name).into(),
                                    typ: MutTypeX::array(
                                        BaseType::BitVec(word_width),
                                        MutTypeX::base(BaseType::BitVec(*width)),
                                    ),
                                }));
                            } else {
                                assert!(*width == word_width); // not supported otherwise
                                has_alias = true;

                                // Add a constant pointer into the memory
                                consts.push(Spanned::new(ConstDeclX {
                                    name: format!("param_{}", param.name).into(),
                                    typ: BaseType::BitVec(word_width),
                                }));
                            }
                        },
                        _ => unimplemented!("nested pointer")
                    }
            }
        }

        if has_alias {
            muts.push(Spanned::new(MutDeclX {
                name: "mem".into(),
                typ: MutTypeX::array(
                    BaseType::BitVec(word_width),
                    MutTypeX::base(BaseType::BitVec(word_width)),
                ),
            }));
        }

        // Infer base types of channels
        // by propagating type information

        // Generate channels

        // Generate concrete processes

        Program {
            decls: consts.into_iter().map(|d| Decl::Const(d))
                .chain(muts.into_iter().map(|d: Rc<Spanned<MutDeclX>>| Decl::Mut(d)))
                .collect(),
        }
    }
}
