use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LlhdSort {
    LlhdTy,
    LlhdVecTy,
    LlhdPureDfg,
    LlhdPureVec,
}

impl LlhdSort {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::LlhdTy => "LLHDTy",
            Self::LlhdVecTy => "LLHDVecTy",
            Self::LlhdPureDfg => "LLHDPureDFG",
            Self::LlhdPureVec => "LLHDPureVec",
        }
    }
}

impl fmt::Display for LlhdSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LlhdPureOp {
    ValueRef,
    ConstInt,
    ConstTime,
    Alias,
    ArrayUniform,
    Array,
    Struct,
    Not,
    Neg,
    Add,
    Sub,
    And,
    Or,
    Xor,
    Smul,
    Sdiv,
    Smod,
    Srem,
    Umul,
    Udiv,
    Umod,
    Urem,
    Eq,
    Neq,
    Slt,
    Sgt,
    Sle,
    Sge,
    Ult,
    Ugt,
    Ule,
    Uge,
    Shl,
    Shr,
    Mux,
    Sig,
    Prb,
    InsField,
    InsSlice,
    ExtField,
    ExtSlice,
    RootDfg,
    PureDef,
}

impl LlhdPureOp {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ValueRef => "ValueRef",
            Self::ConstInt => "ConstInt",
            Self::ConstTime => "ConstTime",
            Self::Alias => "Alias",
            Self::ArrayUniform => "ArrayUniform",
            Self::Array => "Array",
            Self::Struct => "Struct",
            Self::Not => "Not",
            Self::Neg => "Neg",
            Self::Add => "Add",
            Self::Sub => "Sub",
            Self::And => "And",
            Self::Or => "Or",
            Self::Xor => "Xor",
            Self::Smul => "Smul",
            Self::Sdiv => "Sdiv",
            Self::Smod => "Smod",
            Self::Srem => "Srem",
            Self::Umul => "Umul",
            Self::Udiv => "Udiv",
            Self::Umod => "Umod",
            Self::Urem => "Urem",
            Self::Eq => "Eq",
            Self::Neq => "Neq",
            Self::Slt => "Slt",
            Self::Sgt => "Sgt",
            Self::Sle => "Sle",
            Self::Sge => "Sge",
            Self::Ult => "Ult",
            Self::Ugt => "Ugt",
            Self::Ule => "Ule",
            Self::Uge => "Uge",
            Self::Shl => "Shl",
            Self::Shr => "Shr",
            Self::Mux => "Mux",
            Self::Sig => "Sig",
            Self::Prb => "Prb",
            Self::InsField => "InsField",
            Self::InsSlice => "InsSlice",
            Self::ExtField => "ExtField",
            Self::ExtSlice => "ExtSlice",
            Self::RootDfg => "RootDFG",
            Self::PureDef => "PureDef",
        }
    }
}

impl fmt::Display for LlhdPureOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
