use crate::{
    is_pure_opcode, CfgSkeleton, EClassRef, UnitEGraph, CFG_SK_BLOCK, CFG_SK_BLOCK_ARG,
    CFG_SK_EFFECT, CFG_SK_TERM_BR, CFG_SK_TERM_BR_COND, CFG_SK_TERM_HALT, CFG_SK_TERM_RET,
    CFG_SK_TERM_RET_VALUE, CFG_SK_TERM_WAIT, CFG_SK_TERM_WAIT_TIME,
};
use anyhow::{anyhow, bail, Context, Result};
use egglog::ast::{Action, Command, Expr, Literal, Parser, RustSpan, Span};
use egglog_numeric_id::NumericId;
use llhd::ir::{
    Block, ExtUnit, Inst, InstData, Opcode, RegMode, Signature, Unit, UnitBuilder, UnitData,
    UnitKind, UnitName, Value, ValueData,
};
use llhd::table::TableKey;
use llhd::ty::{
    array_ty, enum_ty, func_ty, int_ty, pointer_ty, signal_ty, struct_ty, time_ty, void_ty, Type,
    TypeKind,
};
use llhd::value::{IntValue, TimeValue};
use num::{BigInt, BigRational, BigUint, Zero};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgDir {
    Input,
    Output,
}

#[derive(Debug, Clone)]
struct ArgValueEntry {
    dir: ArgDir,
    index: usize,
    value_id: usize,
}

#[derive(Debug, Clone)]
struct ParsedInst {
    inst_id: usize,
    block_id: usize,
    opcode: Opcode,
    result: Option<usize>,
    ty: Type,
    args: Vec<ParsedValue>,
    blocks: Vec<usize>,
    imms: Vec<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParsedValue {
    Invalid,
    Id(usize),
}

#[derive(Debug, Clone)]
struct ConstIntInfo {
    width: usize,
    value: BigUint,
}

#[derive(Debug, Clone)]
struct ConstTimeInfo {
    num: BigInt,
    den: BigInt,
    delta: usize,
    epsilon: usize,
}

#[derive(Debug, Clone)]
struct CallInfo {
    ext_id: usize,
    ins: u16,
}

#[derive(Debug, Clone)]
struct ParsedExtUnit {
    name: UnitName,
    sig: Signature,
}

#[derive(Debug, Clone)]
struct ParsedUnit {
    kind: UnitKind,
    name: UnitName,
    sig: Signature,
}

#[derive(Debug, Default)]
struct ParsedProgram {
    unit: Option<ParsedUnit>,
    arg_values: Vec<ArgValueEntry>,
    ext_units: HashMap<usize, ParsedExtUnit>,
    block_order: Vec<usize>,
    insts: Vec<ParsedInst>,
    const_ints: HashMap<usize, ConstIntInfo>,
    const_times: HashMap<usize, ConstTimeInfo>,
    call_info: HashMap<usize, CallInfo>,
    reg_modes: HashMap<usize, Vec<RegMode>>,
}

/// Serialize a unit into egglog commands.
pub fn unit_to_egglog_commands(unit: &Unit<'_>) -> Result<Vec<Command>> {
    let mut commands = Vec::new();
    let (name_tag, name_val) = unit_name_terms(unit.name());
    let inputs = types_list(
        unit.sig()
            .inputs()
            .map(|arg| unit.sig().arg_type(arg))
            .collect(),
    );
    let outputs = types_list(
        unit.sig()
            .outputs()
            .map(|arg| unit.sig().arg_type(arg))
            .collect(),
    );
    let ret = unit
        .sig()
        .has_return_type()
        .then(|| type_term(&unit.sig().return_type()))
        .unwrap_or_else(|| expr_atom("None"));
    let kind = expr_atom(unit_kind_atom(unit.kind()));
    commands.push(expr_command(expr_call(
        "Unit",
        vec![
            kind,
            name_tag,
            name_val,
            inputs.clone(),
            outputs.clone(),
            ret.clone(),
        ],
    )));

    for (index, value) in unit.input_args().enumerate() {
        commands.push(expr_command(expr_call(
            "ArgValue",
            vec![
                expr_atom("input"),
                expr_usize(index)?,
                expr_usize(value.index())?,
            ],
        )));
    }
    for (index, value) in unit.output_args().enumerate() {
        commands.push(expr_command(expr_call(
            "ArgValue",
            vec![
                expr_atom("output"),
                expr_usize(index)?,
                expr_usize(value.index())?,
            ],
        )));
    }

    for (ext, data) in unit.extern_units() {
        let (ext_tag, ext_name) = unit_name_terms(&data.name);
        let ext_inputs = types_list(
            data.sig
                .inputs()
                .map(|arg| data.sig.arg_type(arg))
                .collect(),
        );
        let ext_outputs = types_list(
            data.sig
                .outputs()
                .map(|arg| data.sig.arg_type(arg))
                .collect(),
        );
        let ext_ret = data
            .sig
            .has_return_type()
            .then(|| type_term(&data.sig.return_type()))
            .unwrap_or_else(|| expr_atom("None"));
        commands.push(expr_command(expr_call(
            "ExtUnit",
            vec![
                expr_usize(ext.index())?,
                ext_tag,
                ext_name,
                ext_inputs,
                ext_outputs,
                ext_ret,
            ],
        )));
    }

    let block_ids: Vec<_> = unit.blocks().map(|bb| bb.index()).collect();
    let block_order = expr_list(
        block_ids
            .iter()
            .map(|id| expr_usize(*id))
            .collect::<Result<Vec<_>>>()?,
    );
    commands.push(expr_command(expr_call("BlockOrder", vec![block_order])));

    for bb in unit.blocks() {
        for inst in unit.insts(bb) {
            let data = &unit[inst];
            let opcode = expr_atom(opcode_atom(data.opcode()));
            let result = unit
                .get_inst_result(inst)
                .map(|value| expr_usize(value.index()))
                .transpose()?
                .unwrap_or_else(|| expr_atom("none"));
            let ty = type_term(&unit.inst_type(inst));
            let args = values_list(
                data.args()
                    .iter()
                    .map(|arg| parsed_value_term(*arg))
                    .collect::<Result<Vec<_>>>()?,
            );
            let blocks = values_list(
                data.blocks()
                    .iter()
                    .map(|bb| expr_usize(bb.index()))
                    .collect::<Result<Vec<_>>>()?,
            );
            let imms = values_list(
                data.imms()
                    .iter()
                    .map(|imm| expr_usize(*imm))
                    .collect::<Result<Vec<_>>>()?,
            );
            commands.push(expr_command(expr_call(
                "Inst",
                vec![
                    expr_usize(inst.index())?,
                    expr_usize(bb.index())?,
                    opcode,
                    result,
                    ty,
                    args,
                    blocks,
                    imms,
                ],
            )));

            if let Some(imm) = data.get_const_int() {
                commands.push(expr_command(expr_call(
                    "ConstInt",
                    vec![
                        expr_usize(inst.index())?,
                        expr_usize(imm.width)?,
                        expr_string(imm.value.to_string()),
                    ],
                )));
            }
            if let Some(imm) = data.get_const_time() {
                let num = imm.time.numer().clone();
                let den = imm.time.denom().clone();
                commands.push(expr_command(expr_call(
                    "ConstTime",
                    vec![
                        expr_usize(inst.index())?,
                        expr_string(num.to_string()),
                        expr_string(den.to_string()),
                        expr_usize(imm.delta)?,
                        expr_usize(imm.epsilon)?,
                    ],
                )));
            }
            if let Some(ext) = data.get_ext_unit() {
                if matches!(data.opcode(), Opcode::Call | Opcode::Inst) {
                    let ins = data.input_args().len() as u16;
                    commands.push(expr_command(expr_call(
                        "CallInfo",
                        vec![
                            expr_usize(inst.index())?,
                            expr_usize(ext.index())?,
                            expr_usize(ins as usize)?,
                        ],
                    )));
                }
            }
            if data.opcode() == Opcode::Reg {
                let modes: Vec<_> = data
                    .mode_args()
                    .map(|mode| expr_atom(reg_mode_atom(mode)))
                    .collect();
                commands.push(expr_command(expr_call(
                    "RegModes",
                    vec![expr_usize(inst.index())?, expr_list(modes)],
                )));
            }
        }
    }

    if unit.is_entity() {
        commands.push(expr_command(expr_call(CFG_SK_BLOCK, vec![expr_usize(0)?])));
    } else {
        let mut egraph = UnitEGraph::build_from_unit(unit)?;
        let skeleton = CfgSkeleton::build_from_unit(unit, &mut egraph)?;
        for block in &skeleton.blocks {
            commands.push(expr_command(expr_call(
                CFG_SK_BLOCK,
                vec![expr_usize(block.block.index())?],
            )));
            for arg in &block.args {
                commands.push(expr_command(expr_call(
                    CFG_SK_BLOCK_ARG,
                    vec![
                        expr_usize(block.block.index())?,
                        expr_usize(arg.value.index())?,
                        expr_i64(eclass_id(arg.class) as i64),
                    ],
                )));
            }
            for stmt in &block.stmts {
                match stmt {
                    crate::cfg_skeleton::SkeletonStmt::Effect {
                        inst,
                        opcode,
                        args,
                        result,
                    } => {
                        let arg_list = values_list(
                            args.iter()
                                .map(|arg| expr_i64(eclass_id(*arg) as i64))
                                .collect::<Vec<_>>(),
                        );
                        let result = result
                            .map(|value| expr_i64(eclass_id(value) as i64))
                            .unwrap_or_else(|| expr_atom("none"));
                        commands.push(expr_command(expr_call(
                            CFG_SK_EFFECT,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_atom(opcode_atom(*opcode)),
                                result,
                                arg_list,
                            ],
                        )));
                    }
                }
            }
            if let Some(term) = &block.terminator {
                match term {
                    crate::cfg_skeleton::SkeletonTerminator::Br { inst, target, args } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_BR,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_usize(target.index())?,
                                values_list(
                                    args.iter()
                                        .map(|arg| expr_i64(eclass_id(*arg) as i64))
                                        .collect::<Vec<_>>(),
                                ),
                            ],
                        )));
                    }
                    crate::cfg_skeleton::SkeletonTerminator::BrCond {
                        inst,
                        cond,
                        then_target,
                        then_args,
                        else_target,
                        else_args,
                    } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_BR_COND,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_i64(eclass_id(*cond) as i64),
                                expr_usize(then_target.index())?,
                                values_list(
                                    then_args
                                        .iter()
                                        .map(|arg| expr_i64(eclass_id(*arg) as i64))
                                        .collect::<Vec<_>>(),
                                ),
                                expr_usize(else_target.index())?,
                                values_list(
                                    else_args
                                        .iter()
                                        .map(|arg| expr_i64(eclass_id(*arg) as i64))
                                        .collect::<Vec<_>>(),
                                ),
                            ],
                        )));
                    }
                    crate::cfg_skeleton::SkeletonTerminator::Wait { inst, target, args } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_WAIT,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_usize(target.index())?,
                                values_list(
                                    args.iter()
                                        .map(|arg| expr_i64(eclass_id(*arg) as i64))
                                        .collect::<Vec<_>>(),
                                ),
                            ],
                        )));
                    }
                    crate::cfg_skeleton::SkeletonTerminator::WaitTime {
                        inst,
                        time,
                        target,
                        args,
                    } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_WAIT_TIME,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_i64(eclass_id(*time) as i64),
                                expr_usize(target.index())?,
                                values_list(
                                    args.iter()
                                        .map(|arg| expr_i64(eclass_id(*arg) as i64))
                                        .collect::<Vec<_>>(),
                                ),
                            ],
                        )));
                    }
                    crate::cfg_skeleton::SkeletonTerminator::Ret { inst } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_RET,
                            vec![expr_usize(block.block.index())?, expr_usize(inst.index())?],
                        )));
                    }
                    crate::cfg_skeleton::SkeletonTerminator::RetValue { inst, value } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_RET_VALUE,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_i64(eclass_id(*value) as i64),
                            ],
                        )));
                    }
                    crate::cfg_skeleton::SkeletonTerminator::Halt { inst } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_HALT,
                            vec![expr_usize(block.block.index())?, expr_usize(inst.index())?],
                        )));
                    }
                }
            }
        }
    }

    append_pure_dfg_commands(unit, &mut commands)?;

    Ok(commands)
}

/// Serialize a unit into an egglog-style program.
pub fn unit_to_egglog_program(unit: &Unit<'_>) -> Result<String> {
    let commands = unit_to_egglog_commands(unit)?;
    Ok(commands
        .iter()
        .map(|cmd| cmd.to_string())
        .collect::<Vec<_>>()
        .join("\n"))
}

/// Dump a human-readable egglog program with schema notes.
#[cfg(feature = "egglog-debug")]
pub fn dump_egglog_debug(unit: &Unit<'_>, program: &str) -> String {
    let mut out = String::new();
    out.push_str("LLHD Egglog Debug Dump\n");
    out.push_str("======================\n\n");
    out.push_str(&format!("unit: {}\n", unit.name()));
    out.push_str(&format!("kind: {:?}\n", unit.kind()));
    out.push_str(&format!("signature: {}\n\n", unit.sig()));

    out.push_str("Schema (serialization terms)\n");
    out.push_str("-----------------------------\n");
    out.push_str("Unit(kind, name_tag, name_value, inputs, outputs, return)\n");
    out.push_str("ArgValue(dir, index, value_id)\n");
    out.push_str("ExtUnit(id, name_tag, name_value, inputs, outputs, return)\n");
    out.push_str("BlockOrder(block_id...)\n");
    out.push_str("Inst(inst_id, block_id, opcode, result, type, args, blocks, imms)\n");
    out.push_str("ConstInt(inst_id, width, value)\n");
    out.push_str("ConstTime(inst_id, num, den, delta, epsilon)\n");
    out.push_str("CallInfo(inst_id, ext_id, ins)\n");
    out.push_str("RegModes(inst_id, [modes...])\n\n");

    out.push_str("CFG skeleton schema\n");
    out.push_str("-------------------\n");
    let cfg_schema = crate::cfg_schema_program();
    out.push_str(cfg_schema);
    if !cfg_schema.ends_with('\n') {
        out.push('\n');
    }
    out.push('\n');

    out.push_str("Facts (egglog program)\n");
    out.push_str("----------------------\n");
    out.push_str(program);
    out.push('\n');
    out
}

/// Deserialize a unit from an egglog-style program.
pub fn unit_from_egglog_program(program: &str) -> Result<UnitData> {
    let commands = parse_egglog_program(program)?;
    unit_from_egglog_commands(&commands)
}

/// Deserialize a unit from egglog commands.
pub fn unit_from_egglog_commands(commands: &[Command]) -> Result<UnitData> {
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
    for (id, ext) in parsed.ext_units {
        let ext_unit = builder.add_extern(ext.name, ext.sig);
        ext_map.insert(id, ext_unit);
    }

    let mut block_map = HashMap::new();
    for block_id in parsed.block_order {
        let bb = builder.block();
        block_map.insert(block_id, bb);
    }

    for inst in parsed.insts {
        let bb = *block_map
            .get(&inst.block_id)
            .ok_or_else(|| anyhow!("missing block {}", inst.block_id))?;
        builder.append_to(bb);

        let args = resolve_values(&mut builder, &value_types, &mut value_map, &inst.args)?;
        let blocks = resolve_blocks(&block_map, &inst.blocks)?;
        let imms = inst.imms;
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

fn append_pure_dfg_commands(unit: &Unit<'_>, commands: &mut Vec<Command>) -> Result<()> {
    let roots = collect_pure_roots(unit);
    let pure_order = collect_pure_order(unit, &roots);
    let pure_set: HashMap<Value, ()> = pure_order.iter().map(|value| (*value, ())).collect();

    for value in &pure_order {
        let Some(inst) = def_inst(unit, *value) else {
            continue;
        };
        let data = &unit[inst];
        if !is_pure_opcode(data.opcode()) {
            continue;
        }
        let expr = pure_dfg_expr_for_inst(unit, inst, data, &pure_set)?;
        let name = pure_value_var(*value);
        commands.push(Command::Action(Action::Let(egglog::span!(), name, expr)));
    }

    for value in roots {
        let expr = if pure_set.contains_key(&value) {
            expr_var(&pure_value_var(value))
        } else {
            value_ref_expr(value)
        };
        commands.push(expr_command(expr_call("RootDFG", vec![expr])));
    }

    Ok(())
}

fn collect_pure_order(unit: &Unit<'_>, roots: &[Value]) -> Vec<Value> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Visit {
        Visiting,
        Visited,
    }

    let mut order = Vec::new();
    let mut state: HashMap<Value, Visit> = HashMap::new();

    for &root in roots {
        let Some(inst) = def_inst(unit, root) else {
            continue;
        };
        if !is_pure_opcode(unit[inst].opcode()) {
            continue;
        }

        let mut stack: Vec<(Value, usize)> = vec![(root, 0)];
        while let Some((value, idx)) = stack.pop() {
            if matches!(state.get(&value), Some(Visit::Visited)) {
                continue;
            }
            let Some(inst) = def_inst(unit, value) else {
                state.insert(value, Visit::Visited);
                order.push(value);
                continue;
            };
            if !is_pure_opcode(unit[inst].opcode()) {
                state.insert(value, Visit::Visited);
                continue;
            }

            if idx == 0 {
                if matches!(state.get(&value), Some(Visit::Visiting)) {
                    state.insert(value, Visit::Visited);
                    order.push(value);
                    continue;
                }
                state.insert(value, Visit::Visiting);
            }

            let args = unit[inst].args();
            if idx < args.len() {
                stack.push((value, idx + 1));
                let arg = args[idx];
                if let Some(arg_inst) = def_inst(unit, arg) {
                    if is_pure_opcode(unit[arg_inst].opcode()) {
                        stack.push((arg, 0));
                    }
                }
                continue;
            }

            state.insert(value, Visit::Visited);
            order.push(value);
        }
    }

    order
}

fn pure_dfg_expr_for_inst(
    unit: &Unit<'_>,
    inst: Inst,
    data: &InstData,
    pure_set: &HashMap<Value, ()>,
) -> Result<Expr> {
    let opcode = data.opcode();
    let expr = match data {
        InstData::ConstInt { imm, .. } => {
            op_term("ConstInt", vec![expr_string(imm.value.to_string())])
        }
        InstData::ConstTime { imm, .. } => op_term("ConstTime", vec![expr_string(imm.to_string())]),
        InstData::Array { args, imms, .. } if opcode == Opcode::ArrayUniform => {
            let len = imms.get(0).copied().unwrap_or(0);
            let arg = args.get(0).copied().unwrap_or_else(Value::invalid);
            op_term(
                "ArrayUniform",
                vec![expr_usize(len)?, value_ref_or_var(arg, pure_set)],
            )
        }
        InstData::Aggregate { args, .. } if opcode == Opcode::Array => {
            let elems = args
                .iter()
                .map(|arg| value_ref_or_var(*arg, pure_set))
                .collect();
            op_term("Array", vec![expr_list(elems)])
        }
        InstData::Aggregate { args, .. } if opcode == Opcode::Struct => {
            let elems = args
                .iter()
                .map(|arg| value_ref_or_var(*arg, pure_set))
                .collect();
            op_term("Struct", vec![expr_list(elems)])
        }
        InstData::Unary { args, .. } => {
            let arg = args.get(0).copied().unwrap_or_else(Value::invalid);
            let arg = value_ref_or_var(arg, pure_set);
            match opcode {
                Opcode::Alias => op_term("Alias", vec![arg]),
                Opcode::Not => op_term("Not", vec![arg]),
                Opcode::Neg => op_term("Neg", vec![arg]),
                Opcode::Sig => op_term("Sig", vec![arg]),
                Opcode::Prb => op_term("Prb", vec![arg]),
                _ => value_ref_expr_for_inst(unit, inst),
            }
        }
        InstData::Binary { args, .. } => {
            let lhs = args.get(0).copied().unwrap_or_else(Value::invalid);
            let rhs = args.get(1).copied().unwrap_or_else(Value::invalid);
            let lhs = value_ref_or_var(lhs, pure_set);
            let rhs = value_ref_or_var(rhs, pure_set);
            match opcode {
                Opcode::Add => op_term("Add", vec![lhs, rhs]),
                Opcode::Sub => op_term("Sub", vec![lhs, rhs]),
                Opcode::And => op_term("And", vec![lhs, rhs]),
                Opcode::Or => op_term("Or", vec![lhs, rhs]),
                Opcode::Xor => op_term("Xor", vec![lhs, rhs]),
                Opcode::Smul => op_term("Smul", vec![lhs, rhs]),
                Opcode::Sdiv => op_term("Sdiv", vec![lhs, rhs]),
                Opcode::Smod => op_term("Smod", vec![lhs, rhs]),
                Opcode::Srem => op_term("Srem", vec![lhs, rhs]),
                Opcode::Umul => op_term("Umul", vec![lhs, rhs]),
                Opcode::Udiv => op_term("Udiv", vec![lhs, rhs]),
                Opcode::Umod => op_term("Umod", vec![lhs, rhs]),
                Opcode::Urem => op_term("Urem", vec![lhs, rhs]),
                Opcode::Eq => op_term("Eq", vec![lhs, rhs]),
                Opcode::Neq => op_term("Neq", vec![lhs, rhs]),
                Opcode::Slt => op_term("Slt", vec![lhs, rhs]),
                Opcode::Sgt => op_term("Sgt", vec![lhs, rhs]),
                Opcode::Sle => op_term("Sle", vec![lhs, rhs]),
                Opcode::Sge => op_term("Sge", vec![lhs, rhs]),
                Opcode::Ult => op_term("Ult", vec![lhs, rhs]),
                Opcode::Ugt => op_term("Ugt", vec![lhs, rhs]),
                Opcode::Ule => op_term("Ule", vec![lhs, rhs]),
                Opcode::Uge => op_term("Uge", vec![lhs, rhs]),
                Opcode::Mux => op_term("Mux", vec![lhs, rhs]),
                _ => value_ref_expr_for_inst(unit, inst),
            }
        }
        InstData::Ternary { args, .. } => {
            let a = args.get(0).copied().unwrap_or_else(Value::invalid);
            let b = args.get(1).copied().unwrap_or_else(Value::invalid);
            let c = args.get(2).copied().unwrap_or_else(Value::invalid);
            let a = value_ref_or_var(a, pure_set);
            let b = value_ref_or_var(b, pure_set);
            let c = value_ref_or_var(c, pure_set);
            match opcode {
                Opcode::Shl => op_term("Shl", vec![a, b, c]),
                Opcode::Shr => op_term("Shr", vec![a, b, c]),
                _ => value_ref_expr_for_inst(unit, inst),
            }
        }
        InstData::InsExt { args, imms, .. }
            if opcode == Opcode::InsField
                || opcode == Opcode::InsSlice
                || opcode == Opcode::ExtField
                || opcode == Opcode::ExtSlice =>
        {
            let a = args.get(0).copied().unwrap_or_else(Value::invalid);
            let b = args.get(1).copied().unwrap_or_else(Value::invalid);
            let a = value_ref_or_var(a, pure_set);
            let b = value_ref_or_var(b, pure_set);
            let imm0 = imms.get(0).copied().unwrap_or(0);
            let imm1 = imms.get(1).copied().unwrap_or(0);
            let imm0 = expr_usize(imm0)?;
            let imm1 = expr_usize(imm1)?;
            match opcode {
                Opcode::InsField => op_term("InsField", vec![a, b, imm0, imm1]),
                Opcode::InsSlice => op_term("InsSlice", vec![a, b, imm0, imm1]),
                Opcode::ExtField => op_term("ExtField", vec![a, b, imm0, imm1]),
                Opcode::ExtSlice => op_term("ExtSlice", vec![a, b, imm0, imm1]),
                _ => value_ref_expr_for_inst(unit, inst),
            }
        }
        _ => value_ref_expr_for_inst(unit, inst),
    };

    Ok(expr)
}

fn pure_value_var(value: Value) -> String {
    format!("v{}", value.index())
}

fn value_ref_or_var(value: Value, pure_set: &HashMap<Value, ()>) -> Expr {
    if value.is_invalid() {
        value_ref_expr(value)
    } else if pure_set.contains_key(&value) {
        expr_var(&pure_value_var(value))
    } else {
        value_ref_expr(value)
    }
}

fn value_ref_expr(value: Value) -> Expr {
    if value.is_invalid() {
        op_term("ValueRef", vec![expr_i64(-1)])
    } else {
        op_term("ValueRef", vec![expr_i64(value.index() as i64)])
    }
}

fn value_ref_expr_for_inst(unit: &Unit<'_>, inst: Inst) -> Expr {
    match unit.get_inst_result(inst) {
        Some(value) => value_ref_expr(value),
        None => value_ref_expr(Value::invalid()),
    }
}

fn def_inst(unit: &Unit<'_>, value: Value) -> Option<Inst> {
    match &unit[value] {
        ValueData::Inst { inst, .. } => Some(*inst),
        _ => None,
    }
}

fn op_term(name: &str, args: Vec<Expr>) -> Expr {
    expr_call(name, args)
}

fn collect_pure_roots(unit: &Unit<'_>) -> Vec<Value> {
    let mut roots = Vec::new();
    let mut seen = HashMap::new();

    if unit.is_entity() {
        for value in unit.output_args() {
            if seen.insert(value, ()).is_none() {
                roots.push(value);
            }
        }
        return roots;
    }

    for inst in unit.all_insts() {
        let opcode = unit[inst].opcode();
        if is_pure_opcode(opcode) {
            continue;
        }
        for &arg in unit[inst].args() {
            if arg.is_invalid() {
                continue;
            }
            if seen.insert(arg, ()).is_none() {
                roots.push(arg);
            }
        }
    }

    roots.sort_by_key(|value| value.index());
    roots
}

fn build_inst_data(
    opcode: Opcode,
    args: Vec<Value>,
    blocks: Vec<Block>,
    imms: Vec<usize>,
    const_ints: &HashMap<usize, ConstIntInfo>,
    const_times: &HashMap<usize, ConstTimeInfo>,
    call_info: &HashMap<usize, CallInfo>,
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

fn parse_egglog_program(program: &str) -> Result<Vec<Command>> {
    let mut parser = Parser::default();
    parser
        .get_program_from_string(None, program)
        .map_err(|err| anyhow!("{err}"))
}

fn parse_commands(commands: &[Command]) -> Result<ParsedProgram> {
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
            CFG_SK_BLOCK
            | CFG_SK_BLOCK_ARG
            | CFG_SK_EFFECT
            | CFG_SK_TERM_BR
            | CFG_SK_TERM_BR_COND
            | CFG_SK_TERM_WAIT
            | CFG_SK_TERM_WAIT_TIME
            | CFG_SK_TERM_RET
            | CFG_SK_TERM_RET_VALUE
            | CFG_SK_TERM_HALT => {
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

fn parse_optional_type(expr: &Expr) -> Result<Option<Type>> {
    if let Expr::Var(_, atom) = expr {
        if atom == "None" {
            return Ok(None);
        }
    }
    Ok(Some(parse_type(expr)?))
}

fn parse_type_list(expr: &Expr) -> Result<Vec<Type>> {
    let items = parse_expr_list(expr)?;
    items.iter().map(parse_type).collect()
}

fn parse_type(expr: &Expr) -> Result<Type> {
    match expr {
        Expr::Var(_, atom) => match atom.as_str() {
            "Void" => Ok(void_ty()),
            "Time" => Ok(time_ty()),
            other => bail!("unknown type atom {}", other),
        },
        Expr::Call(_, head, rest) => match head.as_str() {
            "IntTy" => Ok(int_ty(parse_usize(single(rest, "IntTy")?)?)),
            "Enum" => Ok(enum_ty(parse_usize(single(rest, "Enum")?)?)),
            "Pointer" => Ok(pointer_ty(parse_type(single_term(rest, "Pointer")?)?)),
            "Signal" => Ok(signal_ty(parse_type(single_term(rest, "Signal")?)?)),
            "ArrayTy" => {
                if rest.len() != 2 {
                    bail!("ArrayTy expects 2 fields");
                }
                let len = parse_usize(&rest[0])?;
                let ty = parse_type(&rest[1])?;
                Ok(array_ty(len, ty))
            }
            "StructTy" => {
                if rest.len() != 1 {
                    bail!("StructTy expects list field");
                }
                let fields = parse_type_list(&rest[0])?;
                Ok(struct_ty(fields))
            }
            "FuncTy" => {
                if rest.len() != 2 {
                    bail!("FuncTy expects args list and return type");
                }
                let args = parse_type_list(&rest[0])?;
                let ret = parse_type(&rest[1])?;
                Ok(func_ty(args, ret))
            }
            "EntityTy" => {
                if rest.len() != 2 {
                    bail!("EntityTy expects inputs and outputs list");
                }
                let ins = parse_type_list(&rest[0])?;
                let outs = parse_type_list(&rest[1])?;
                Ok(llhd::ty::entity_ty(ins, outs))
            }
            other => bail!("unknown type form {}", other),
        },
        Expr::Lit(_, Literal::String(_)) => bail!("unexpected string in type"),
        Expr::Lit(_, Literal::Int(_)) => bail!("unexpected int in type"),
        Expr::Lit(_, Literal::Float(_)) => bail!("unexpected float in type"),
        Expr::Lit(_, Literal::Bool(_)) => bail!("unexpected bool in type"),
        Expr::Lit(_, Literal::Unit) => bail!("unexpected unit in type"),
    }
}

fn single<'a>(rest: &'a [Expr], name: &str) -> Result<&'a Expr> {
    if rest.len() != 1 {
        bail!("{} expects 1 field", name);
    }
    Ok(&rest[0])
}

fn single_term<'a>(rest: &'a [Expr], name: &str) -> Result<&'a Expr> {
    single(rest, name)
}

fn parse_unit_kind(atom: &str) -> Result<UnitKind> {
    match atom {
        "function" => Ok(UnitKind::Function),
        "process" => Ok(UnitKind::Process),
        "entity" => Ok(UnitKind::Entity),
        other => bail!("unknown unit kind {}", other),
    }
}

fn unit_kind_atom(kind: UnitKind) -> &'static str {
    match kind {
        UnitKind::Function => "function",
        UnitKind::Process => "process",
        UnitKind::Entity => "entity",
    }
}

fn opcode_atom(opcode: Opcode) -> &'static str {
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

fn parse_opcode(atom: &str) -> Result<Opcode> {
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

fn reg_mode_atom(mode: RegMode) -> String {
    match mode {
        RegMode::Low => "Low".into(),
        RegMode::High => "High".into(),
        RegMode::Rise => "Rise".into(),
        RegMode::Fall => "Fall".into(),
        RegMode::Both => "Both".into(),
    }
}

fn parse_reg_mode(atom: &str) -> Result<RegMode> {
    Ok(match atom {
        "Low" => RegMode::Low,
        "High" => RegMode::High,
        "Rise" => RegMode::Rise,
        "Fall" => RegMode::Fall,
        "Both" => RegMode::Both,
        other => bail!("unknown reg mode {}", other),
    })
}

fn unit_name_terms(name: &UnitName) -> (Expr, Expr) {
    match name {
        UnitName::Anonymous(id) => (expr_atom("anon"), expr_i64(i64::from(*id))),
        UnitName::Local(name) => (expr_atom("local"), expr_string(name.clone())),
        UnitName::Global(name) => (expr_atom("global"), expr_string(name.clone())),
    }
}

fn parse_unit_name(tag: &str, value: &Expr) -> Result<UnitName> {
    match tag {
        "anon" => Ok(UnitName::Anonymous(parse_usize(value)? as u32)),
        "local" => Ok(UnitName::Local(parse_expr_string(value)?)),
        "global" => Ok(UnitName::Global(parse_expr_string(value)?)),
        other => bail!("unknown unit name tag {}", other),
    }
}

fn type_term(ty: &Type) -> Expr {
    match ty.as_ref() {
        TypeKind::VoidType => expr_atom("Void"),
        TypeKind::TimeType => expr_atom("Time"),
        TypeKind::IntType(bits) => expr_call("IntTy", vec![expr_i64(*bits as i64)]),
        TypeKind::EnumType(states) => expr_call("Enum", vec![expr_i64(*states as i64)]),
        TypeKind::PointerType(inner) => expr_call("Pointer", vec![type_term(inner)]),
        TypeKind::SignalType(inner) => expr_call("Signal", vec![type_term(inner)]),
        TypeKind::ArrayType(len, inner) => {
            expr_call("ArrayTy", vec![expr_i64(*len as i64), type_term(inner)])
        }
        TypeKind::StructType(fields) => expr_call(
            "StructTy",
            vec![types_list(fields.iter().cloned().collect())],
        ),
        TypeKind::FuncType(args, ret) => {
            expr_call("FuncTy", vec![types_list(args.clone()), type_term(ret)])
        }
        TypeKind::EntityType(ins, outs) => expr_call(
            "EntityTy",
            vec![types_list(ins.clone()), types_list(outs.clone())],
        ),
    }
}

fn types_list(types: Vec<Type>) -> Expr {
    expr_list(types.iter().map(type_term).collect())
}

fn values_list(values: Vec<Expr>) -> Expr {
    expr_list(values)
}

fn parsed_value_term(value: Value) -> Result<Expr> {
    if value.is_invalid() {
        Ok(expr_atom("invalid"))
    } else {
        expr_usize(value.index())
    }
}

fn signature_from_parts(inputs: Vec<Type>, outputs: Vec<Type>, ret: Option<Type>) -> Signature {
    let mut sig = Signature::new();
    for ty in inputs {
        sig.add_input(ty);
    }
    for ty in outputs {
        sig.add_output(ty);
    }
    if let Some(ty) = ret {
        sig.set_return_type(ty);
    }
    sig
}

fn eclass_id(class: EClassRef) -> u32 {
    class.0.rep()
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

fn parse_usize(expr: &Expr) -> Result<usize> {
    let value = parse_expr_int(expr)?;
    if value < 0 {
        bail!("invalid usize");
    }
    usize::try_from(value).context("invalid usize")
}

fn parse_bigint(value: String) -> Result<BigInt> {
    value.parse::<BigInt>().context("invalid bigint")
}

fn parse_expr_atom(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Var(_, value) => Ok(value.clone()),
        _ => bail!("expected atom"),
    }
}

fn parse_expr_string(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Lit(_, Literal::String(value)) => Ok(value.clone()),
        Expr::Var(_, value) => Ok(value.clone()),
        _ => bail!("expected string"),
    }
}

fn parse_expr_int(expr: &Expr) -> Result<i64> {
    match expr {
        Expr::Lit(_, Literal::Int(value)) => Ok(*value),
        _ => bail!("expected integer"),
    }
}

fn parse_expr_list(expr: &Expr) -> Result<Vec<Expr>> {
    let (head, args) = expr_call_parts(expr)?;
    if head != "list" {
        bail!("expected list");
    }
    Ok(args.to_vec())
}

fn expr_call_parts(expr: &Expr) -> Result<(&str, &[Expr])> {
    match expr {
        Expr::Call(_, head, args) => Ok((head.as_str(), args.as_slice())),
        _ => bail!("expected call"),
    }
}

fn expr_atom(value: impl Into<String>) -> Expr {
    Expr::Var(egglog::span!(), value.into())
}

fn expr_var(value: &str) -> Expr {
    Expr::Var(egglog::span!(), value.to_string())
}

fn expr_string(value: String) -> Expr {
    Expr::Lit(egglog::span!(), Literal::String(value))
}

fn expr_i64(value: i64) -> Expr {
    Expr::Lit(egglog::span!(), Literal::Int(value))
}

fn expr_usize(value: usize) -> Result<Expr> {
    let value = i64::try_from(value).map_err(|_| anyhow!("value out of i64 range"))?;
    Ok(expr_i64(value))
}

fn expr_list(values: Vec<Expr>) -> Expr {
    expr_call("list", values)
}

fn expr_call(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call(egglog::span!(), name.to_string(), args)
}

fn expr_command(expr: Expr) -> Command {
    Command::Action(Action::Expr(egglog::span!(), expr))
}
