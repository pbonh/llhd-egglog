use super::ast::{
    expr_call_parts, parse_expr_atom, parse_expr_list, parse_expr_string, parse_usize,
};
use super::names::{parse_opcode, parse_reg_mode, parse_unit_kind, parse_unit_name};
use super::types::{parse_optional_type, parse_type, parse_type_list, signature_from_parts};
use anyhow::{anyhow, bail, Context, Result};
use egglog::ast::{Action, Command, Expr, Literal, Parser};
use llhd::ir::{Opcode, RegMode, Signature, UnitKind, UnitName};
use llhd::ty::Type;
use num::{BigInt, BigUint};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArgDir {
    Input,
    Output,
}

#[derive(Debug, Clone)]
pub(crate) struct ArgValueEntry {
    pub(crate) dir: ArgDir,
    pub(crate) index: usize,
    pub(crate) value_id: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct ParsedInst {
    pub(crate) inst_id: usize,
    pub(crate) block_id: usize,
    pub(crate) opcode: Opcode,
    pub(crate) result: Option<usize>,
    pub(crate) ty: Type,
    pub(crate) args: Vec<ParsedValue>,
    pub(crate) blocks: Vec<usize>,
    pub(crate) imms: Vec<usize>,
}

#[derive(Debug, Clone)]
pub(crate) struct PureDefEntry {
    pub(crate) inst_id: usize,
    pub(crate) value_id: usize,
    pub(crate) block_id: usize,
    pub(crate) ty: Type,
    pub(crate) term: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParsedValue {
    Invalid,
    Id(usize),
}

#[derive(Debug, Clone)]
pub(crate) struct ConstIntInfo {
    pub(crate) width: usize,
    pub(crate) value: BigUint,
}

#[derive(Debug, Clone)]
pub(crate) struct ConstTimeInfo {
    pub(crate) num: BigInt,
    pub(crate) den: BigInt,
    pub(crate) delta: usize,
    pub(crate) epsilon: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct CallInfo {
    pub(crate) ext_id: usize,
    pub(crate) ins: u16,
}

#[derive(Debug, Clone)]
pub(crate) struct ParsedExtUnit {
    pub(crate) name: UnitName,
    pub(crate) sig: Signature,
}

#[derive(Debug, Clone)]
pub(crate) struct ParsedUnit {
    pub(crate) kind: UnitKind,
    pub(crate) name: UnitName,
    pub(crate) sig: Signature,
}

#[derive(Debug, Default)]
pub(crate) struct ParsedProgram {
    pub(crate) unit: Option<ParsedUnit>,
    pub(crate) arg_values: Vec<ArgValueEntry>,
    pub(crate) ext_units: HashMap<usize, ParsedExtUnit>,
    pub(crate) block_order: Vec<usize>,
    pub(crate) insts: Vec<ParsedInst>,
    pub(crate) pure_defs: Vec<PureDefEntry>,
    pub(crate) const_ints: HashMap<usize, ConstIntInfo>,
    pub(crate) const_times: HashMap<usize, ConstTimeInfo>,
    pub(crate) call_info: HashMap<usize, CallInfo>,
    pub(crate) reg_modes: HashMap<usize, Vec<RegMode>>,
}

pub(crate) fn parse_egglog_program(program: &str) -> Result<Vec<Command>> {
    let mut parser = Parser::default();
    parser
        .get_program_from_string(None, program)
        .map_err(|err| anyhow!("{err}"))
}

pub(crate) fn parse_commands(commands: &[Command]) -> Result<ParsedProgram> {
    let mut parsed = ParsedProgram::default();
    for command in commands {
        let expr = match command {
            Command::Action(Action::Expr(_, expr)) => expr,
            Command::Action(Action::Let(_, _, _)) => continue,
            other => bail!("unsupported command: {other}"),
        };
        let (head, rest) = expr_call_parts(expr)?;
        match head {
            "Unit" => {
                let (kind, name, sig) = parse_unit_entry(rest)?;
                parsed.unit = Some(ParsedUnit { kind, name, sig });
            }
            "ArgValue" => parsed.arg_values.push(parse_arg_value(rest)?),
            "ExtUnit" => {
                let (id, ext) = parse_ext_unit(rest)?;
                parsed.ext_units.insert(id, ext);
            }
            "BlockOrder" => {
                if rest.len() != 1 {
                    bail!("BlockOrder entry expects list field");
                }
                parsed.block_order = parse_usize_list(&rest[0])?;
            }
            "Inst" => parsed.insts.push(parse_inst(rest)?),
            "PureDef" => parsed.pure_defs.push(parse_pure_def(rest)?),
            "ConstInt" => {
                let (inst_id, info) = parse_const_int(rest)?;
                parsed.const_ints.insert(inst_id, info);
            }
            "ConstTime" => {
                let (inst_id, info) = parse_const_time(rest)?;
                parsed.const_times.insert(inst_id, info);
            }
            "CallInfo" => {
                let info = parse_call_info(rest)?;
                parsed.call_info.insert(info.0, info.1);
            }
            "RegModes" => {
                let (inst_id, modes) = parse_reg_modes(rest)?;
                parsed.reg_modes.insert(inst_id, modes);
            }
            "SkBlock" | "SkBlockArg" | "SkEffect" | "SkTermBr" | "SkTermBrCond" | "SkTermWait"
            | "SkTermWaitTime" | "SkTermRet" | "SkTermRetValue" | "SkTermHalt" => {
                // Skeleton entries are parsed but not required for reconstruction.
            }
            "RootDFG" => {
                // Pure DFG roots are ignored during reconstruction.
            }
            other => bail!("unknown term {}", other),
        }
    }
    Ok(parsed)
}

fn parse_unit_entry(items: &[Expr]) -> Result<(UnitKind, UnitName, Signature)> {
    if items.len() != 6 {
        bail!("Unit entry expects 6 fields");
    }
    let kind = parse_unit_kind(&parse_expr_atom(&items[0])?)?;
    let name_tag = parse_expr_atom(&items[1])?;
    let name = parse_unit_name(&name_tag, &items[2])?;
    let inputs = parse_type_list(&items[3])?;
    let outputs = parse_type_list(&items[4])?;
    let ret = parse_optional_type(&items[5])?;
    Ok((kind, name, signature_from_parts(inputs, outputs, ret)))
}

fn parse_arg_value(items: &[Expr]) -> Result<ArgValueEntry> {
    if items.len() != 3 {
        bail!("ArgValue entry expects 3 fields");
    }
    let dir = match parse_expr_atom(&items[0])?.as_str() {
        "input" => ArgDir::Input,
        "output" => ArgDir::Output,
        other => bail!("unknown ArgValue dir {}", other),
    };
    Ok(ArgValueEntry {
        dir,
        index: parse_usize(&items[1])?,
        value_id: parse_usize(&items[2])?,
    })
}

fn parse_ext_unit(items: &[Expr]) -> Result<(usize, ParsedExtUnit)> {
    if items.len() != 6 {
        bail!("ExtUnit entry expects 6 fields");
    }
    let id = parse_usize(&items[0])?;
    let name_tag = parse_expr_atom(&items[1])?;
    let name = parse_unit_name(&name_tag, &items[2])?;
    let inputs = parse_type_list(&items[3])?;
    let outputs = parse_type_list(&items[4])?;
    let ret = parse_optional_type(&items[5])?;
    let sig = signature_from_parts(inputs, outputs, ret);
    Ok((id, ParsedExtUnit { name, sig }))
}

fn parse_pure_def(items: &[Expr]) -> Result<PureDefEntry> {
    if items.len() != 5 {
        bail!("PureDef entry expects 5 fields");
    }
    let inst_id = parse_usize(&items[0])?;
    let value_id = parse_usize(&items[1])?;
    let block_id = parse_usize(&items[2])?;
    let ty = parse_type(&items[3])?;
    let term = items[4].clone();
    Ok(PureDefEntry {
        inst_id,
        value_id,
        block_id,
        ty,
        term,
    })
}

fn parse_inst(items: &[Expr]) -> Result<ParsedInst> {
    if items.len() != 8 {
        bail!("Inst entry expects 8 fields");
    }
    let inst_id = parse_usize(&items[0])?;
    let block_id = parse_usize(&items[1])?;
    let opcode = parse_opcode(&parse_expr_atom(&items[2])?)?;
    let result = parse_optional_usize(&items[3])?;
    let ty = parse_type(&items[4])?;
    let args = parse_value_list(&items[5])?;
    let blocks = parse_usize_list(&items[6])?;
    let imms = parse_usize_list(&items[7])?;
    Ok(ParsedInst {
        inst_id,
        block_id,
        opcode,
        result,
        ty,
        args,
        blocks,
        imms,
    })
}

fn parse_const_int(items: &[Expr]) -> Result<(usize, ConstIntInfo)> {
    if items.len() != 3 {
        bail!("ConstInt entry expects 3 fields");
    }
    let inst_id = parse_usize(&items[0])?;
    let width = parse_usize(&items[1])?;
    let value_str = parse_expr_string(&items[2])?;
    let value = BigUint::parse_bytes(value_str.as_bytes(), 10)
        .ok_or_else(|| anyhow!("invalid ConstInt value"))?;
    Ok((inst_id, ConstIntInfo { width, value }))
}

fn parse_const_time(items: &[Expr]) -> Result<(usize, ConstTimeInfo)> {
    if items.len() != 5 {
        bail!("ConstTime entry expects 5 fields");
    }
    let inst_id = parse_usize(&items[0])?;
    let num = parse_bigint(parse_expr_string(&items[1])?)?;
    let den = parse_bigint(parse_expr_string(&items[2])?)?;
    let delta = parse_usize(&items[3])?;
    let epsilon = parse_usize(&items[4])?;
    Ok((
        inst_id,
        ConstTimeInfo {
            num,
            den,
            delta,
            epsilon,
        },
    ))
}

fn parse_call_info(items: &[Expr]) -> Result<(usize, CallInfo)> {
    if items.len() != 3 {
        bail!("CallInfo entry expects 3 fields");
    }
    let inst_id = parse_usize(&items[0])?;
    let ext_id = parse_usize(&items[1])?;
    let ins = parse_usize(&items[2])?;
    Ok((
        inst_id,
        CallInfo {
            ext_id,
            ins: ins as u16,
        },
    ))
}

fn parse_reg_modes(items: &[Expr]) -> Result<(usize, Vec<RegMode>)> {
    if items.len() != 2 {
        bail!("RegModes entry expects 2 fields");
    }
    let inst_id = parse_usize(&items[0])?;
    let modes = parse_expr_list(&items[1])?
        .iter()
        .map(|term| parse_reg_mode(&parse_expr_atom(term)?))
        .collect::<Result<Vec<_>>>()?;
    Ok((inst_id, modes))
}

fn parse_value_list(expr: &Expr) -> Result<Vec<ParsedValue>> {
    let items = parse_expr_list(expr)?;
    items
        .iter()
        .map(|item| match item {
            Expr::Var(_, atom) if atom == "invalid" => Ok(ParsedValue::Invalid),
            Expr::Var(_, atom) => Ok(ParsedValue::Id(
                atom.parse::<usize>().context("invalid value id")?,
            )),
            Expr::Lit(_, Literal::Int(value)) => {
                if *value < 0 {
                    bail!("invalid value id");
                }
                Ok(ParsedValue::Id(
                    usize::try_from(*value).context("invalid value id")?,
                ))
            }
            _ => bail!("invalid value id"),
        })
        .collect()
}

fn parse_usize_list(expr: &Expr) -> Result<Vec<usize>> {
    let items = parse_expr_list(expr)?;
    items.iter().map(parse_usize).collect()
}

fn parse_optional_usize(expr: &Expr) -> Result<Option<usize>> {
    match expr {
        Expr::Var(_, atom) if atom == "none" => Ok(None),
        Expr::Var(_, atom) => Ok(Some(atom.parse::<usize>().context("invalid usize")?)),
        Expr::Lit(_, Literal::Int(value)) => {
            if *value < 0 {
                bail!("invalid usize");
            }
            Ok(Some(usize::try_from(*value).context("invalid usize")?))
        }
        _ => bail!("invalid optional usize"),
    }
}

fn parse_bigint(value: String) -> Result<BigInt> {
    value.parse::<BigInt>().context("invalid bigint")
}
