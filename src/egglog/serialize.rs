use super::ast::{
    expr_atom, expr_call, expr_command, expr_i64, expr_list, expr_string, expr_usize,
};
use super::names::{opcode_atom, reg_mode_atom, unit_kind_atom, unit_name_terms};
use super::program::LlhdEgglogProgram;
use super::pure_dfg::append_pure_dfg_commands;
use super::types::{type_term, types_list};
use crate::cfg::{CfgSkeleton, SkeletonStmt, SkeletonTerminator};
use crate::egraph::{is_pure_opcode, EClassRef, UnitEGraph};
use crate::schema::{
    CFG_SK_BLOCK, CFG_SK_BLOCK_ARG, CFG_SK_EFFECT, CFG_SK_TERM_BR, CFG_SK_TERM_BR_COND,
    CFG_SK_TERM_HALT, CFG_SK_TERM_RET, CFG_SK_TERM_RET_VALUE, CFG_SK_TERM_WAIT,
    CFG_SK_TERM_WAIT_TIME,
};
use anyhow::Result;
use egglog::ast::Command;
use egglog_numeric_id::NumericId;
use llhd::ir::{Opcode, Unit, Value};
use llhd::table::TableKey;

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
            if is_pure_opcode(data.opcode()) {
                continue;
            }
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
                    SkeletonStmt::Effect {
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
                    SkeletonTerminator::Br { inst, target, args } => {
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
                    SkeletonTerminator::BrCond {
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
                    SkeletonTerminator::Wait { inst, target, args } => {
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
                    SkeletonTerminator::WaitTime {
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
                    SkeletonTerminator::Ret { inst } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_RET,
                            vec![expr_usize(block.block.index())?, expr_usize(inst.index())?],
                        )));
                    }
                    SkeletonTerminator::RetValue { inst, value } => {
                        commands.push(expr_command(expr_call(
                            CFG_SK_TERM_RET_VALUE,
                            vec![
                                expr_usize(block.block.index())?,
                                expr_usize(inst.index())?,
                                expr_i64(eclass_id(*value) as i64),
                            ],
                        )));
                    }
                    SkeletonTerminator::Halt { inst } => {
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
    Ok(LlhdEgglogProgram::builder()
        .facts(commands)
        .build()
        .to_string())
}

fn values_list(values: Vec<::egglog::ast::Expr>) -> ::egglog::ast::Expr {
    expr_list(values)
}

fn parsed_value_term(value: Value) -> Result<::egglog::ast::Expr> {
    if value.is_invalid() {
        Ok(expr_atom("invalid"))
    } else {
        expr_usize(value.index())
    }
}

fn eclass_id(class: EClassRef) -> u32 {
    class.0.rep()
}
