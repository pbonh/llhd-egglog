use super::ast as egg_ast;
use super::types::type_term;
use crate::egraph::is_pure_opcode;
use anyhow::Result;
use egglog::ast::{Action, Command, Expr, RustSpan, Span};
use llhd::ir::{Inst, InstData, Opcode, Unit, Value, ValueData};
use llhd::table::TableKey;
use std::collections::HashMap;

pub(crate) fn append_pure_dfg_commands(unit: &Unit<'_>, commands: &mut Vec<Command>) -> Result<()> {
    let roots = collect_pure_roots(unit);
    let pure_order = collect_pure_order(unit, &roots);
    let pure_set: HashMap<Value, ()> = pure_order.iter().map(|value| (*value, ())).collect();
    let inst_blocks = collect_inst_blocks(unit);

    for value in &pure_order {
        let Some(inst) = def_inst(unit, *value) else {
            continue;
        };
        let data = &unit[inst];
        if !is_pure_opcode(data.opcode()) {
            continue;
        }
        let expr = pure_dfg_expr_for_inst_with(unit, inst, data, |value| {
            value_ref_or_var(value, &pure_set)
        })?;
        let name = pure_value_var(*value);
        commands.push(Command::Action(Action::Let(::egglog::span!(), name, expr)));
    }

    for bb in unit.blocks() {
        for inst in unit.insts(bb) {
            let data = &unit[inst];
            if !is_pure_opcode(data.opcode()) {
                continue;
            }
            let Some(result) = unit.get_inst_result(inst) else {
                continue;
            };
            let Some(block_id) = inst_blocks.get(&inst).copied() else {
                continue;
            };
            let inst_id = egg_ast::expr_usize(inst.index())?;
            let value_id = egg_ast::expr_usize(result.index())?;
            let block_id = egg_ast::expr_usize(block_id)?;
            let ty = type_term(&unit.inst_type(inst));
            let expr = pure_dfg_expr_for_inst_with(unit, inst, data, value_ref_expr)?;
            commands.push(egg_ast::expr_command(egg_ast::expr_call(
                "PureDef",
                vec![inst_id, value_id, block_id, ty, expr],
            )));
        }
    }

    for value in roots {
        let expr = if pure_set.contains_key(&value) {
            egg_ast::expr_var(&pure_value_var(value))
        } else {
            value_ref_expr(value)
        };
        commands.push(egg_ast::expr_command(egg_ast::expr_call(
            "RootDFG",
            vec![expr],
        )));
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

fn pure_dfg_expr_for_inst_with<F>(
    unit: &Unit<'_>,
    inst: Inst,
    data: &InstData,
    arg_expr: F,
) -> Result<Expr>
where
    F: Fn(Value) -> Expr,
{
    let opcode = data.opcode();
    let expr = match data {
        InstData::ConstInt { imm, .. } => op_term(
            "ConstInt",
            vec![egg_ast::expr_string(imm.value.to_string())],
        ),
        InstData::ConstTime { imm, .. } => {
            let num = imm.time.numer().clone();
            let den = imm.time.denom().clone();
            op_term(
                "ConstTime",
                vec![
                    egg_ast::expr_string(num.to_string()),
                    egg_ast::expr_string(den.to_string()),
                    egg_ast::expr_usize(imm.delta)?,
                    egg_ast::expr_usize(imm.epsilon)?,
                ],
            )
        }
        InstData::Array { args, imms, .. } if opcode == Opcode::ArrayUniform => {
            let len = imms.get(0).copied().unwrap_or(0);
            let arg = args.get(0).copied().unwrap_or_else(Value::invalid);
            op_term(
                "ArrayUniform",
                vec![egg_ast::expr_usize(len)?, arg_expr(arg)],
            )
        }
        InstData::Aggregate { args, .. } if opcode == Opcode::Array => {
            let elems = args.iter().map(|arg| arg_expr(*arg)).collect();
            op_term("Array", vec![egg_ast::expr_list(elems)])
        }
        InstData::Aggregate { args, .. } if opcode == Opcode::Struct => {
            let elems = args.iter().map(|arg| arg_expr(*arg)).collect();
            op_term("Struct", vec![egg_ast::expr_list(elems)])
        }
        InstData::Unary { args, .. } => {
            let arg = args.get(0).copied().unwrap_or_else(Value::invalid);
            let arg = arg_expr(arg);
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
            let lhs = arg_expr(lhs);
            let rhs = arg_expr(rhs);
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
            let a = arg_expr(a);
            let b = arg_expr(b);
            let c = arg_expr(c);
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
            let a = arg_expr(a);
            let b = arg_expr(b);
            let imm0 = imms.get(0).copied().unwrap_or(0);
            let imm1 = imms.get(1).copied().unwrap_or(0);
            let imm0 = egg_ast::expr_usize(imm0)?;
            let imm1 = egg_ast::expr_usize(imm1)?;
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
        egg_ast::expr_var(&pure_value_var(value))
    } else {
        value_ref_expr(value)
    }
}

fn value_ref_expr(value: Value) -> Expr {
    if value.is_invalid() {
        op_term("ValueRef", vec![egg_ast::expr_i64(-1)])
    } else {
        op_term("ValueRef", vec![egg_ast::expr_i64(value.index() as i64)])
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
    egg_ast::expr_call(name, args)
}

fn collect_inst_blocks(unit: &Unit<'_>) -> HashMap<Inst, usize> {
    let mut blocks = HashMap::new();
    for bb in unit.blocks() {
        for inst in unit.insts(bb) {
            blocks.insert(inst, bb.index());
        }
    }
    blocks
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
