use super::ast::{
    expr_call_parts, parse_expr_int, parse_expr_list, parse_expr_string, parse_usize,
};
use super::parse::{parse_commands, parse_egglog_program, ArgDir, ParsedValue};
use anyhow::{anyhow, bail, Result};
use egglog::ast::Expr;
use llhd::ir::{Block, ExtUnit, InstData, Opcode, RegMode, UnitBuilder, UnitData, Value};
use llhd::table::TableKey;
use llhd::ty::{Type, TypeKind};
use llhd::value::{IntValue, TimeValue};
use num::{BigInt, BigRational, BigUint, Zero};
use std::collections::HashMap;

/// Deserialize a unit from an egglog-style program.
pub fn unit_from_egglog_program(program: &str) -> Result<UnitData> {
    let commands = parse_egglog_program(program)?;
    unit_from_egglog_commands(&commands)
}

/// Deserialize a unit from egglog commands.
pub fn unit_from_egglog_commands(commands: &[::egglog::ast::Command]) -> Result<UnitData> {
    let parsed = parse_commands(commands)?;
    let unit = parsed.unit.ok_or_else(|| anyhow!("missing Unit entry"))?;

    let mut data = UnitData::new(unit.kind, unit.name, unit.sig);
    let mut builder = UnitBuilder::new_anonymous(&mut data);
    if builder.is_entity() {
        if let Some(entry) = builder.first_block() {
            builder.delete_block(entry);
        }
    }
    let sig = builder.sig().clone();

    let mut input_values: Vec<Option<usize>> = vec![None; sig.inputs().count()];
    let mut output_values: Vec<Option<usize>> = vec![None; sig.outputs().count()];
    for entry in &parsed.arg_values {
        match entry.dir {
            ArgDir::Input => {
                if entry.index >= input_values.len() {
                    bail!("input arg index out of range");
                }
                input_values[entry.index] = Some(entry.value_id);
            }
            ArgDir::Output => {
                if entry.index >= output_values.len() {
                    bail!("output arg index out of range");
                }
                output_values[entry.index] = Some(entry.value_id);
            }
        }
    }

    let mut value_types: HashMap<usize, Type> = HashMap::new();
    for (idx, arg) in sig.inputs().enumerate() {
        let value_id = input_values
            .get(idx)
            .and_then(|value| *value)
            .ok_or_else(|| anyhow!("missing input arg value mapping"))?;
        value_types.insert(value_id, sig.arg_type(arg));
    }
    for (idx, arg) in sig.outputs().enumerate() {
        let value_id = output_values
            .get(idx)
            .and_then(|value| *value)
            .ok_or_else(|| anyhow!("missing output arg value mapping"))?;
        value_types.insert(value_id, sig.arg_type(arg));
    }
    for inst in &parsed.insts {
        if let Some(result) = inst.result {
            if let Some(existing) = value_types.get(&result) {
                if existing != &inst.ty {
                    bail!("value type mismatch for serialized value {}", result);
                }
            } else {
                value_types.insert(result, inst.ty.clone());
            }
        }
    }
    for pure_def in &parsed.pure_defs {
        if let Some(existing) = value_types.get(&pure_def.value_id) {
            if existing != &pure_def.ty {
                bail!("value type mismatch for pure value {}", pure_def.value_id);
            }
        } else {
            value_types.insert(pure_def.value_id, pure_def.ty.clone());
        }
    }

    let mut value_map: HashMap<usize, (Value, bool)> = HashMap::new();
    for (idx, arg) in sig.inputs().enumerate() {
        let value_id = input_values[idx].unwrap();
        value_map.insert(value_id, (builder.input_arg(idx), false));
        value_types.insert(value_id, sig.arg_type(arg));
    }
    for (idx, arg) in sig.outputs().enumerate() {
        let value_id = output_values[idx].unwrap();
        value_map.insert(value_id, (builder.output_arg(idx), false));
        value_types.insert(value_id, sig.arg_type(arg));
    }

    let mut ext_map = HashMap::new();
    for (id, ext) in &parsed.ext_units {
        let ext_unit = builder.add_extern(ext.name.clone(), ext.sig.clone());
        ext_map.insert(*id, ext_unit);
    }

    let mut block_map = HashMap::new();
    for block_id in &parsed.block_order {
        let bb = builder.block();
        block_map.insert(*block_id, bb);
    }

    enum InstEntry<'a> {
        Pure(&'a super::parse::PureDefEntry),
        Effect(&'a super::parse::ParsedInst),
    }

    let mut insts_by_block: HashMap<usize, Vec<InstEntry<'_>>> = HashMap::new();
    for pure_def in &parsed.pure_defs {
        insts_by_block
            .entry(pure_def.block_id)
            .or_default()
            .push(InstEntry::Pure(pure_def));
    }
    for inst in &parsed.insts {
        insts_by_block
            .entry(inst.block_id)
            .or_default()
            .push(InstEntry::Effect(inst));
    }

    for block_id in &parsed.block_order {
        let Some(bb) = block_map.get(block_id).copied() else {
            continue;
        };
        let Some(entries) = insts_by_block.get_mut(block_id) else {
            continue;
        };
        entries.sort_by_key(|entry| match entry {
            InstEntry::Pure(def) => def.inst_id,
            InstEntry::Effect(inst) => inst.inst_id,
        });
        for entry in entries.iter() {
            builder.append_to(bb);
            match entry {
                InstEntry::Pure(def) => {
                    let inst_data = build_pure_inst_data(
                        &def.term,
                        &def.ty,
                        &mut builder,
                        &value_types,
                        &mut value_map,
                    )?;
                    let created = builder.build_inst(inst_data, def.ty.clone());
                    let result = builder.inst_result(created);
                    let result_id = def.value_id;
                    match value_map.get(&result_id) {
                        None => {
                            value_map.insert(result_id, (result, false));
                        }
                        Some((existing, is_placeholder)) => {
                            if !*is_placeholder {
                                bail!("duplicate value definition for {}", result_id);
                            }
                            builder.replace_use(*existing, result);
                            builder.remove_placeholder(*existing);
                            value_map.insert(result_id, (result, false));
                        }
                    }
                }
                InstEntry::Effect(inst) => {
                    let args =
                        resolve_values(&mut builder, &value_types, &mut value_map, &inst.args)?;
                    let blocks = resolve_blocks(&block_map, &inst.blocks)?;
                    let imms = inst.imms.clone();
                    let inst_data = build_inst_data(
                        inst.opcode,
                        args,
                        blocks,
                        imms,
                        &parsed.const_ints,
                        &parsed.const_times,
                        &parsed.call_info,
                        &parsed.reg_modes,
                        &ext_map,
                        inst.inst_id,
                    )?;
                    let created = builder.build_inst(inst_data, inst.ty.clone());
                    if let Some(result_id) = inst.result {
                        let result = builder.inst_result(created);
                        match value_map.get(&result_id) {
                            None => {
                                value_map.insert(result_id, (result, false));
                            }
                            Some((existing, is_placeholder)) => {
                                if !*is_placeholder {
                                    bail!("duplicate value definition for {}", result_id);
                                }
                                builder.replace_use(*existing, result);
                                builder.remove_placeholder(*existing);
                                value_map.insert(result_id, (result, false));
                            }
                        }
                    }
                }
            }
        }
    }

    let unresolved: Vec<_> = value_map
        .iter()
        .filter_map(|(id, (_, placeholder))| (*placeholder).then_some(*id))
        .collect();
    if !unresolved.is_empty() {
        bail!("unresolved values: {:?}", unresolved);
    }

    let _ = builder.finish();
    Ok(data)
}

#[derive(Debug, Clone)]
enum PureTerm {
    ConstInt(String),
    ConstTime {
        num: String,
        den: String,
        delta: usize,
        epsilon: usize,
    },
    ArrayUniform {
        len: usize,
        arg: ParsedValue,
    },
    Array {
        args: Vec<ParsedValue>,
    },
    Struct {
        args: Vec<ParsedValue>,
    },
    Unary {
        opcode: Opcode,
        arg: ParsedValue,
    },
    Binary {
        opcode: Opcode,
        lhs: ParsedValue,
        rhs: ParsedValue,
    },
    Ternary {
        opcode: Opcode,
        a: ParsedValue,
        b: ParsedValue,
        c: ParsedValue,
    },
    InsExt {
        opcode: Opcode,
        a: ParsedValue,
        b: ParsedValue,
        imm0: usize,
        imm1: usize,
    },
}

fn build_pure_inst_data(
    term: &Expr,
    ty: &Type,
    builder: &mut UnitBuilder<'_>,
    value_types: &HashMap<usize, Type>,
    value_map: &mut HashMap<usize, (Value, bool)>,
) -> Result<InstData> {
    let term = parse_pure_term(term)?;
    Ok(match term {
        PureTerm::ConstInt(value) => {
            let width = match ty.as_ref() {
                TypeKind::IntType(bits) => *bits as usize,
                other => bail!("ConstInt expects int type, got {:?}", other),
            };
            let value = BigUint::parse_bytes(value.as_bytes(), 10)
                .ok_or_else(|| anyhow!("invalid ConstInt value"))?;
            InstData::ConstInt {
                opcode: Opcode::ConstInt,
                imm: IntValue::from_unsigned(width, value),
            }
        }
        PureTerm::ConstTime {
            num,
            den,
            delta,
            epsilon,
        } => {
            let num = num
                .parse::<BigInt>()
                .map_err(|_| anyhow!("invalid ConstTime numerator"))?;
            let den = den
                .parse::<BigInt>()
                .map_err(|_| anyhow!("invalid ConstTime denominator"))?;
            let den = if den.is_zero() { BigInt::from(1) } else { den };
            let time = BigRational::new(num, den);
            let imm = TimeValue::new(time, delta, epsilon);
            InstData::ConstTime {
                opcode: Opcode::ConstTime,
                imm,
            }
        }
        PureTerm::ArrayUniform { len, arg } => {
            let args = resolve_values(builder, value_types, value_map, &[arg])?;
            let arg = args
                .get(0)
                .copied()
                .ok_or_else(|| anyhow!("missing ArrayUniform arg"))?;
            InstData::Array {
                opcode: Opcode::ArrayUniform,
                imms: [len],
                args: [arg],
            }
        }
        PureTerm::Array { args } => {
            let args = resolve_values(builder, value_types, value_map, &args)?;
            InstData::Aggregate {
                opcode: Opcode::Array,
                args,
            }
        }
        PureTerm::Struct { args } => {
            let args = resolve_values(builder, value_types, value_map, &args)?;
            InstData::Aggregate {
                opcode: Opcode::Struct,
                args,
            }
        }
        PureTerm::Unary { opcode, arg } => {
            let args = resolve_values(builder, value_types, value_map, &[arg])?;
            let arg = args
                .get(0)
                .copied()
                .ok_or_else(|| anyhow!("missing unary arg"))?;
            InstData::Unary {
                opcode,
                args: [arg],
            }
        }
        PureTerm::Binary { opcode, lhs, rhs } => {
            let args = resolve_values(builder, value_types, value_map, &[lhs, rhs])?;
            let lhs = args
                .get(0)
                .copied()
                .ok_or_else(|| anyhow!("missing binary lhs"))?;
            let rhs = args
                .get(1)
                .copied()
                .ok_or_else(|| anyhow!("missing binary rhs"))?;
            InstData::Binary {
                opcode,
                args: [lhs, rhs],
            }
        }
        PureTerm::Ternary { opcode, a, b, c } => {
            let args = resolve_values(builder, value_types, value_map, &[a, b, c])?;
            let a = args
                .get(0)
                .copied()
                .ok_or_else(|| anyhow!("missing ternary arg0"))?;
            let b = args
                .get(1)
                .copied()
                .ok_or_else(|| anyhow!("missing ternary arg1"))?;
            let c = args
                .get(2)
                .copied()
                .ok_or_else(|| anyhow!("missing ternary arg2"))?;
            InstData::Ternary {
                opcode,
                args: [a, b, c],
            }
        }
        PureTerm::InsExt {
            opcode,
            a,
            b,
            imm0,
            imm1,
        } => {
            let args = resolve_values(builder, value_types, value_map, &[a, b])?;
            let a = args
                .get(0)
                .copied()
                .ok_or_else(|| anyhow!("missing InsExt arg0"))?;
            let b = args
                .get(1)
                .copied()
                .ok_or_else(|| anyhow!("missing InsExt arg1"))?;
            InstData::InsExt {
                opcode,
                args: [a, b],
                imms: [imm0, imm1],
            }
        }
    })
}

fn parse_pure_term(expr: &Expr) -> Result<PureTerm> {
    let (head, args) = expr_call_parts(expr)?;
    match head {
        "ConstInt" => {
            if args.len() != 1 {
                bail!("ConstInt expects 1 field");
            }
            Ok(PureTerm::ConstInt(parse_expr_string(&args[0])?))
        }
        "ConstTime" => {
            if args.len() != 4 {
                bail!("ConstTime expects 4 fields");
            }
            let num = parse_expr_string(&args[0])?;
            let den = parse_expr_string(&args[1])?;
            let delta = parse_usize(&args[2])?;
            let epsilon = parse_usize(&args[3])?;
            Ok(PureTerm::ConstTime {
                num,
                den,
                delta,
                epsilon,
            })
        }
        "ArrayUniform" => {
            if args.len() != 2 {
                bail!("ArrayUniform expects 2 fields");
            }
            let len = parse_usize(&args[0])?;
            let arg = parse_value_ref(&args[1])?;
            Ok(PureTerm::ArrayUniform { len, arg })
        }
        "Array" => {
            if args.len() != 1 {
                bail!("Array expects list field");
            }
            let args = parse_value_ref_list(&args[0])?;
            Ok(PureTerm::Array { args })
        }
        "Struct" => {
            if args.len() != 1 {
                bail!("Struct expects list field");
            }
            let args = parse_value_ref_list(&args[0])?;
            Ok(PureTerm::Struct { args })
        }
        "Alias" => parse_unary(Opcode::Alias, args),
        "Not" => parse_unary(Opcode::Not, args),
        "Neg" => parse_unary(Opcode::Neg, args),
        "Sig" => parse_unary(Opcode::Sig, args),
        "Prb" => parse_unary(Opcode::Prb, args),
        "Add" => parse_binary(Opcode::Add, args),
        "Sub" => parse_binary(Opcode::Sub, args),
        "And" => parse_binary(Opcode::And, args),
        "Or" => parse_binary(Opcode::Or, args),
        "Xor" => parse_binary(Opcode::Xor, args),
        "Smul" => parse_binary(Opcode::Smul, args),
        "Sdiv" => parse_binary(Opcode::Sdiv, args),
        "Smod" => parse_binary(Opcode::Smod, args),
        "Srem" => parse_binary(Opcode::Srem, args),
        "Umul" => parse_binary(Opcode::Umul, args),
        "Udiv" => parse_binary(Opcode::Udiv, args),
        "Umod" => parse_binary(Opcode::Umod, args),
        "Urem" => parse_binary(Opcode::Urem, args),
        "Eq" => parse_binary(Opcode::Eq, args),
        "Neq" => parse_binary(Opcode::Neq, args),
        "Slt" => parse_binary(Opcode::Slt, args),
        "Sgt" => parse_binary(Opcode::Sgt, args),
        "Sle" => parse_binary(Opcode::Sle, args),
        "Sge" => parse_binary(Opcode::Sge, args),
        "Ult" => parse_binary(Opcode::Ult, args),
        "Ugt" => parse_binary(Opcode::Ugt, args),
        "Ule" => parse_binary(Opcode::Ule, args),
        "Uge" => parse_binary(Opcode::Uge, args),
        "Mux" => parse_binary(Opcode::Mux, args),
        "Shl" => parse_ternary(Opcode::Shl, args),
        "Shr" => parse_ternary(Opcode::Shr, args),
        "InsField" => parse_ins_ext(Opcode::InsField, args),
        "InsSlice" => parse_ins_ext(Opcode::InsSlice, args),
        "ExtField" => parse_ins_ext(Opcode::ExtField, args),
        "ExtSlice" => parse_ins_ext(Opcode::ExtSlice, args),
        other => bail!("unknown pure DFG term {}", other),
    }
}

fn parse_value_ref(expr: &Expr) -> Result<ParsedValue> {
    let (head, args) = expr_call_parts(expr)?;
    if head != "ValueRef" {
        bail!("expected ValueRef term");
    }
    if args.len() != 1 {
        bail!("ValueRef expects 1 field");
    }
    let value = parse_expr_int(&args[0])?;
    if value < 0 {
        Ok(ParsedValue::Invalid)
    } else {
        Ok(ParsedValue::Id(value as usize))
    }
}

fn parse_value_ref_list(expr: &Expr) -> Result<Vec<ParsedValue>> {
    let items = parse_expr_list(expr)?;
    items.iter().map(parse_value_ref).collect()
}

fn parse_unary(opcode: Opcode, args: &[Expr]) -> Result<PureTerm> {
    if args.len() != 1 {
        bail!("unary term expects 1 field");
    }
    let arg = parse_value_ref(&args[0])?;
    Ok(PureTerm::Unary { opcode, arg })
}

fn parse_binary(opcode: Opcode, args: &[Expr]) -> Result<PureTerm> {
    if args.len() != 2 {
        bail!("binary term expects 2 fields");
    }
    let lhs = parse_value_ref(&args[0])?;
    let rhs = parse_value_ref(&args[1])?;
    Ok(PureTerm::Binary { opcode, lhs, rhs })
}

fn parse_ternary(opcode: Opcode, args: &[Expr]) -> Result<PureTerm> {
    if args.len() != 3 {
        bail!("ternary term expects 3 fields");
    }
    let a = parse_value_ref(&args[0])?;
    let b = parse_value_ref(&args[1])?;
    let c = parse_value_ref(&args[2])?;
    Ok(PureTerm::Ternary { opcode, a, b, c })
}

fn parse_ins_ext(opcode: Opcode, args: &[Expr]) -> Result<PureTerm> {
    if args.len() != 4 {
        bail!("InsExt term expects 4 fields");
    }
    let a = parse_value_ref(&args[0])?;
    let b = parse_value_ref(&args[1])?;
    let imm0 = parse_usize(&args[2])?;
    let imm1 = parse_usize(&args[3])?;
    Ok(PureTerm::InsExt {
        opcode,
        a,
        b,
        imm0,
        imm1,
    })
}

fn build_inst_data(
    opcode: Opcode,
    args: Vec<Value>,
    blocks: Vec<Block>,
    imms: Vec<usize>,
    const_ints: &HashMap<usize, super::parse::ConstIntInfo>,
    const_times: &HashMap<usize, super::parse::ConstTimeInfo>,
    call_info: &HashMap<usize, super::parse::CallInfo>,
    reg_modes: &HashMap<usize, Vec<RegMode>>,
    ext_map: &HashMap<usize, ExtUnit>,
    inst_id: usize,
) -> Result<InstData> {
    Ok(match opcode {
        Opcode::ConstInt => {
            let info = const_ints
                .get(&inst_id)
                .ok_or_else(|| anyhow!("missing ConstInt for inst {}", inst_id))?;
            InstData::ConstInt {
                opcode,
                imm: IntValue::from_unsigned(info.width, info.value.clone()),
            }
        }
        Opcode::ConstTime => {
            let info = const_times
                .get(&inst_id)
                .ok_or_else(|| anyhow!("missing ConstTime for inst {}", inst_id))?;
            let den = if info.den.is_zero() {
                BigInt::from(1)
            } else {
                info.den.clone()
            };
            let time = BigRational::new(info.num.clone(), den);
            InstData::ConstTime {
                opcode,
                imm: TimeValue::new(time, info.delta, info.epsilon),
            }
        }
        Opcode::ArrayUniform => InstData::Array {
            opcode,
            imms: [get_imm(&imms, 0, inst_id)?],
            args: [get_arg(&args, 0, inst_id)?],
        },
        Opcode::Array | Opcode::Struct => InstData::Aggregate { opcode, args },
        Opcode::Alias
        | Opcode::Not
        | Opcode::Neg
        | Opcode::Sig
        | Opcode::Prb
        | Opcode::Var
        | Opcode::Ld
        | Opcode::RetValue => InstData::Unary {
            opcode,
            args: [get_arg(&args, 0, inst_id)?],
        },
        Opcode::Add
        | Opcode::Sub
        | Opcode::And
        | Opcode::Or
        | Opcode::Xor
        | Opcode::Smul
        | Opcode::Sdiv
        | Opcode::Smod
        | Opcode::Srem
        | Opcode::Umul
        | Opcode::Udiv
        | Opcode::Umod
        | Opcode::Urem
        | Opcode::Eq
        | Opcode::Neq
        | Opcode::Slt
        | Opcode::Sgt
        | Opcode::Sle
        | Opcode::Sge
        | Opcode::Ult
        | Opcode::Ugt
        | Opcode::Ule
        | Opcode::Uge
        | Opcode::Mux
        | Opcode::Con
        | Opcode::St => InstData::Binary {
            opcode,
            args: [get_arg(&args, 0, inst_id)?, get_arg(&args, 1, inst_id)?],
        },
        Opcode::Shl | Opcode::Shr | Opcode::Del | Opcode::Drv => InstData::Ternary {
            opcode,
            args: [
                get_arg(&args, 0, inst_id)?,
                get_arg(&args, 1, inst_id)?,
                get_arg(&args, 2, inst_id)?,
            ],
        },
        Opcode::DrvCond => InstData::Quaternary {
            opcode,
            args: [
                get_arg(&args, 0, inst_id)?,
                get_arg(&args, 1, inst_id)?,
                get_arg(&args, 2, inst_id)?,
                get_arg(&args, 3, inst_id)?,
            ],
        },
        Opcode::InsField | Opcode::InsSlice | Opcode::ExtField | Opcode::ExtSlice => {
            let arg0 = get_arg(&args, 0, inst_id)?;
            let arg1 = args.get(1).copied().unwrap_or_else(Value::invalid);
            let imm0 = get_imm(&imms, 0, inst_id)?;
            let imm1 = match opcode {
                Opcode::InsField | Opcode::ExtField => 0,
                Opcode::InsSlice | Opcode::ExtSlice => get_imm(&imms, 1, inst_id)?,
                _ => 0,
            };
            InstData::InsExt {
                opcode,
                args: [arg0, arg1],
                imms: [imm0, imm1],
            }
        }
        Opcode::Call | Opcode::Inst => {
            let info = call_info
                .get(&inst_id)
                .ok_or_else(|| anyhow!("missing CallInfo for inst {}", inst_id))?;
            let ext = *ext_map
                .get(&info.ext_id)
                .ok_or_else(|| anyhow!("missing ext unit {}", info.ext_id))?;
            InstData::Call {
                opcode,
                unit: ext,
                ins: info.ins,
                args,
            }
        }
        Opcode::Reg => {
            let modes = reg_modes
                .get(&inst_id)
                .cloned()
                .ok_or_else(|| anyhow!("missing RegModes for inst {}", inst_id))?;
            InstData::Reg {
                opcode,
                args,
                modes,
            }
        }
        Opcode::Phi => InstData::Phi {
            opcode,
            args,
            bbs: blocks,
        },
        Opcode::Br => InstData::Jump {
            opcode,
            bbs: [get_block(&blocks, 0, inst_id)?],
        },
        Opcode::BrCond => InstData::Branch {
            opcode,
            args: [get_arg(&args, 0, inst_id)?],
            bbs: [
                get_block(&blocks, 0, inst_id)?,
                get_block(&blocks, 1, inst_id)?,
            ],
        },
        Opcode::Wait | Opcode::WaitTime => InstData::Wait {
            opcode,
            bbs: [get_block(&blocks, 0, inst_id)?],
            args,
        },
        Opcode::Halt | Opcode::Ret => InstData::Nullary { opcode },
    })
}

fn get_arg(args: &[Value], idx: usize, inst_id: usize) -> Result<Value> {
    args.get(idx)
        .copied()
        .ok_or_else(|| anyhow!("missing arg {} for inst {}", idx, inst_id))
}

fn get_block(blocks: &[Block], idx: usize, inst_id: usize) -> Result<Block> {
    blocks
        .get(idx)
        .copied()
        .ok_or_else(|| anyhow!("missing block {} for inst {}", idx, inst_id))
}

fn get_imm(imms: &[usize], idx: usize, inst_id: usize) -> Result<usize> {
    imms.get(idx)
        .copied()
        .ok_or_else(|| anyhow!("missing imm {} for inst {}", idx, inst_id))
}

fn resolve_values(
    builder: &mut UnitBuilder<'_>,
    value_types: &HashMap<usize, Type>,
    value_map: &mut HashMap<usize, (Value, bool)>,
    args: &[ParsedValue],
) -> Result<Vec<Value>> {
    let mut out = Vec::with_capacity(args.len());
    for arg in args {
        match arg {
            ParsedValue::Invalid => out.push(Value::invalid()),
            ParsedValue::Id(value_id) => {
                if let Some((value, _)) = value_map.get(value_id) {
                    out.push(*value);
                } else {
                    let ty = value_types
                        .get(value_id)
                        .ok_or_else(|| anyhow!("missing type for value {}", value_id))?;
                    let value = builder.add_placeholder(ty.clone());
                    value_map.insert(*value_id, (value, true));
                    out.push(value);
                }
            }
        }
    }
    Ok(out)
}

fn resolve_blocks(block_map: &HashMap<usize, Block>, blocks: &[usize]) -> Result<Vec<Block>> {
    blocks
        .iter()
        .map(|id| {
            block_map
                .get(id)
                .copied()
                .ok_or_else(|| anyhow!("missing block {}", id))
        })
        .collect()
}
