use super::ast::{expr_atom, expr_i64, expr_string, parse_expr_string, parse_usize};
use anyhow::{bail, Result};
use egglog::ast::Expr;
use llhd::ir::{Opcode, RegMode, UnitKind, UnitName};

pub(crate) fn unit_kind_atom(kind: UnitKind) -> &'static str {
    match kind {
        UnitKind::Function => "function",
        UnitKind::Process => "process",
        UnitKind::Entity => "entity",
    }
}

pub(crate) fn parse_unit_kind(atom: &str) -> Result<UnitKind> {
    match atom {
        "function" => Ok(UnitKind::Function),
        "process" => Ok(UnitKind::Process),
        "entity" => Ok(UnitKind::Entity),
        other => bail!("unknown unit kind {}", other),
    }
}

pub(crate) fn opcode_atom(opcode: Opcode) -> &'static str {
    match opcode {
        Opcode::ConstInt => "ConstInt",
        Opcode::ConstTime => "ConstTime",
        Opcode::Alias => "Alias",
        Opcode::ArrayUniform => "ArrayUniform",
        Opcode::Array => "Array",
        Opcode::Struct => "Struct",
        Opcode::Not => "Not",
        Opcode::Neg => "Neg",
        Opcode::Add => "Add",
        Opcode::Sub => "Sub",
        Opcode::And => "And",
        Opcode::Or => "Or",
        Opcode::Xor => "Xor",
        Opcode::Smul => "Smul",
        Opcode::Sdiv => "Sdiv",
        Opcode::Smod => "Smod",
        Opcode::Srem => "Srem",
        Opcode::Umul => "Umul",
        Opcode::Udiv => "Udiv",
        Opcode::Umod => "Umod",
        Opcode::Urem => "Urem",
        Opcode::Eq => "Eq",
        Opcode::Neq => "Neq",
        Opcode::Slt => "Slt",
        Opcode::Sgt => "Sgt",
        Opcode::Sle => "Sle",
        Opcode::Sge => "Sge",
        Opcode::Ult => "Ult",
        Opcode::Ugt => "Ugt",
        Opcode::Ule => "Ule",
        Opcode::Uge => "Uge",
        Opcode::Shl => "Shl",
        Opcode::Shr => "Shr",
        Opcode::Mux => "Mux",
        Opcode::Reg => "Reg",
        Opcode::InsField => "InsField",
        Opcode::InsSlice => "InsSlice",
        Opcode::ExtField => "ExtField",
        Opcode::ExtSlice => "ExtSlice",
        Opcode::Con => "Con",
        Opcode::Del => "Del",
        Opcode::Call => "Call",
        Opcode::Inst => "Inst",
        Opcode::Sig => "Sig",
        Opcode::Prb => "Prb",
        Opcode::Drv => "Drv",
        Opcode::DrvCond => "DrvCond",
        Opcode::Var => "Var",
        Opcode::Ld => "Ld",
        Opcode::St => "St",
        Opcode::Halt => "Halt",
        Opcode::Ret => "Ret",
        Opcode::RetValue => "RetValue",
        Opcode::Phi => "Phi",
        Opcode::Br => "Br",
        Opcode::BrCond => "BrCond",
        Opcode::Wait => "Wait",
        Opcode::WaitTime => "WaitTime",
    }
}

pub(crate) fn parse_opcode(atom: &str) -> Result<Opcode> {
    Ok(match atom {
        "ConstInt" => Opcode::ConstInt,
        "ConstTime" => Opcode::ConstTime,
        "Alias" => Opcode::Alias,
        "ArrayUniform" => Opcode::ArrayUniform,
        "Array" => Opcode::Array,
        "Struct" => Opcode::Struct,
        "Not" => Opcode::Not,
        "Neg" => Opcode::Neg,
        "Add" => Opcode::Add,
        "Sub" => Opcode::Sub,
        "And" => Opcode::And,
        "Or" => Opcode::Or,
        "Xor" => Opcode::Xor,
        "Smul" => Opcode::Smul,
        "Sdiv" => Opcode::Sdiv,
        "Smod" => Opcode::Smod,
        "Srem" => Opcode::Srem,
        "Umul" => Opcode::Umul,
        "Udiv" => Opcode::Udiv,
        "Umod" => Opcode::Umod,
        "Urem" => Opcode::Urem,
        "Eq" => Opcode::Eq,
        "Neq" => Opcode::Neq,
        "Slt" => Opcode::Slt,
        "Sgt" => Opcode::Sgt,
        "Sle" => Opcode::Sle,
        "Sge" => Opcode::Sge,
        "Ult" => Opcode::Ult,
        "Ugt" => Opcode::Ugt,
        "Ule" => Opcode::Ule,
        "Uge" => Opcode::Uge,
        "Shl" => Opcode::Shl,
        "Shr" => Opcode::Shr,
        "Mux" => Opcode::Mux,
        "Reg" => Opcode::Reg,
        "InsField" => Opcode::InsField,
        "InsSlice" => Opcode::InsSlice,
        "ExtField" => Opcode::ExtField,
        "ExtSlice" => Opcode::ExtSlice,
        "Con" => Opcode::Con,
        "Del" => Opcode::Del,
        "Call" => Opcode::Call,
        "Inst" => Opcode::Inst,
        "Sig" => Opcode::Sig,
        "Prb" => Opcode::Prb,
        "Drv" => Opcode::Drv,
        "DrvCond" => Opcode::DrvCond,
        "Var" => Opcode::Var,
        "Ld" => Opcode::Ld,
        "St" => Opcode::St,
        "Halt" => Opcode::Halt,
        "Ret" => Opcode::Ret,
        "RetValue" => Opcode::RetValue,
        "Phi" => Opcode::Phi,
        "Br" => Opcode::Br,
        "BrCond" => Opcode::BrCond,
        "Wait" => Opcode::Wait,
        "WaitTime" => Opcode::WaitTime,
        other => bail!("unknown opcode {}", other),
    })
}

pub(crate) fn reg_mode_atom(mode: RegMode) -> String {
    match mode {
        RegMode::Low => "Low".into(),
        RegMode::High => "High".into(),
        RegMode::Rise => "Rise".into(),
        RegMode::Fall => "Fall".into(),
        RegMode::Both => "Both".into(),
    }
}

pub(crate) fn parse_reg_mode(atom: &str) -> Result<RegMode> {
    Ok(match atom {
        "Low" => RegMode::Low,
        "High" => RegMode::High,
        "Rise" => RegMode::Rise,
        "Fall" => RegMode::Fall,
        "Both" => RegMode::Both,
        other => bail!("unknown reg mode {}", other),
    })
}

pub(crate) fn unit_name_terms(name: &UnitName) -> (Expr, Expr) {
    match name {
        UnitName::Anonymous(id) => (expr_atom("anon"), expr_i64(i64::from(*id))),
        UnitName::Local(name) => (expr_atom("local"), expr_string(name.clone())),
        UnitName::Global(name) => (expr_atom("global"), expr_string(name.clone())),
    }
}

pub(crate) fn parse_unit_name(tag: &str, value: &Expr) -> Result<UnitName> {
    match tag {
        "anon" => Ok(UnitName::Anonymous(parse_usize(value)? as u32)),
        "local" => Ok(UnitName::Local(parse_expr_string(value)?)),
        "global" => Ok(UnitName::Global(parse_expr_string(value)?)),
        other => bail!("unknown unit name tag {}", other),
    }
}
