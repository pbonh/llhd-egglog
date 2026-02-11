use llhd::ir::prelude::*;
use std::collections::{HashMap, HashSet};

pub(crate) fn insts_for_compare(unit: Unit<'_>, block: Block) -> Vec<Inst> {
    unit.insts(block)
        .filter(|&inst| !(unit.is_entity() && unit[inst].opcode().is_terminator()))
        .collect()
}

fn block_successors(unit: Unit<'_>, block: Block) -> Vec<Block> {
    let Some(term) = unit.last_inst(block) else {
        return Vec::new();
    };
    unit[term].blocks().to_vec()
}

fn inst_signature(unit: Unit<'_>, inst: Inst) -> String {
    let data = &unit[inst];
    let mut out = String::new();
    out.push_str(&format!("{:?}", data.opcode()));
    out.push_str(&format!("|ty:{}", unit.inst_type(inst)));
    out.push_str(&format!("|argc:{}", data.args().len()));
    out.push_str("|imms:");
    for imm in data.imms() {
        out.push_str(&format!("{}", imm));
        out.push(',');
    }
    if data.opcode() == Opcode::ConstInt {
        if let Some(imm) = data.get_const_int() {
            out.push_str(&format!("|cint:{}", imm.value));
        }
    }
    if data.opcode() == Opcode::ConstTime {
        if let Some(imm) = data.get_const_time() {
            out.push_str(&format!("|ctime:{}", imm));
        }
    }
    if let Some(ext) = data.get_ext_unit() {
        out.push_str(&format!("|ext:{}:{}", unit[ext].name, unit[ext].sig));
    }
    if data.opcode() == Opcode::Reg {
        out.push_str("|reg:");
        for trigger in data.triggers() {
            out.push_str(&format!("{:?}", trigger.mode));
            out.push(':');
            out.push_str(if trigger.gate.is_some() {
                "gate"
            } else {
                "nogate"
            });
            out.push(',');
        }
    }
    out
}

fn block_signature(unit: Unit<'_>, block: Block) -> String {
    let mut parts = Vec::new();
    for inst in insts_for_compare(unit, block) {
        parts.push(inst_signature(unit, inst));
    }
    parts.join("|")
}

fn block_order(unit: Unit<'_>) -> Vec<Block> {
    let mut visited = HashSet::new();
    let mut postorder = Vec::new();

    if let Some(entry) = unit.first_block() {
        let mut stack = vec![(entry, 0usize)];
        visited.insert(entry);
        while let Some((block, idx)) = stack.pop() {
            let succs = block_successors(unit, block);
            if idx < succs.len() {
                stack.push((block, idx + 1));
                let succ = succs[idx];
                if visited.insert(succ) {
                    stack.push((succ, 0));
                }
            } else {
                postorder.push(block);
            }
        }
    }

    postorder.reverse();

    let mut unreachable: Vec<_> = unit.blocks().filter(|b| !visited.contains(b)).collect();
    unreachable.sort_by_key(|block| block_signature(unit, *block));
    postorder.extend(unreachable);
    postorder
}

pub(crate) fn units_equivalent(left: Unit<'_>, right: Unit<'_>) -> Result<(), String> {
    if left.kind() != right.kind() {
        return Err(format!(
            "unit kind mismatch: left {:?}, right {:?}",
            left.kind(),
            right.kind()
        ));
    }
    if left.sig() != right.sig() {
        return Err("unit signature mismatch".to_string());
    }

    let left_blocks = block_order(left);
    let right_blocks = block_order(right);

    if left_blocks.len() != right_blocks.len() {
        return Err("block count mismatch".to_string());
    }

    let mut block_map: HashMap<Block, Block> = HashMap::new();
    for (left_block, right_block) in left_blocks.iter().zip(right_blocks.iter()) {
        block_map.insert(*left_block, *right_block);
    }

    let mut inst_pairs = Vec::new();
    for (left_block, right_block) in left_blocks.into_iter().zip(right_blocks.into_iter()) {
        let left_insts = insts_for_compare(left, left_block);
        let right_insts = insts_for_compare(right, right_block);
        if left_insts.len() != right_insts.len() {
            return Err("instruction count mismatch in block".to_string());
        }
        inst_pairs.extend(left_insts.into_iter().zip(right_insts.into_iter()));
    }

    let left_args: Vec<_> = left.args().collect();
    let right_args: Vec<_> = right.args().collect();
    if left_args.len() != right_args.len() {
        return Err("argument count mismatch".to_string());
    }

    let mut value_map: HashMap<Value, Value> = HashMap::new();
    for (left_value, right_value) in left_args.into_iter().zip(right_args.into_iter()) {
        value_map.insert(left_value, right_value);
    }

    for (left_inst, right_inst) in &inst_pairs {
        let left_has_result = left.has_result(*left_inst);
        let right_has_result = right.has_result(*right_inst);
        if left_has_result != right_has_result {
            return Err("result presence mismatch".to_string());
        }
        if left_has_result {
            value_map.insert(left.inst_result(*left_inst), right.inst_result(*right_inst));
        }
    }

    for (left_value, right_value) in value_map.iter() {
        if left_value.is_invalid() {
            continue;
        }
        if left.value_type(*left_value) != right.value_type(*right_value) {
            return Err("value type mismatch".to_string());
        }
    }

    for (left_inst, right_inst) in inst_pairs {
        let left_data = &left[left_inst];
        let right_data = &right[right_inst];

        if left_data.opcode() != right_data.opcode() {
            return Err(format!(
                "opcode mismatch: left {:?}, right {:?}",
                left_data.opcode(),
                right_data.opcode()
            ));
        }

        if left.inst_type(left_inst) != right.inst_type(right_inst) {
            return Err("instruction type mismatch".to_string());
        }

        let left_args = left_data.args();
        let right_args = right_data.args();
        if left_args.len() != right_args.len() {
            return Err("argument length mismatch".to_string());
        }
        for (left_arg, right_arg) in left_args.iter().zip(right_args.iter()) {
            if left_arg.is_invalid() {
                if !right_arg.is_invalid() {
                    return Err("invalid argument mismatch".to_string());
                }
                continue;
            }
            let mapped = value_map
                .get(left_arg)
                .ok_or_else(|| "missing value mapping".to_string())?;
            if mapped != right_arg {
                return Err("argument mapping mismatch".to_string());
            }
        }

        if left_data.imms() != right_data.imms() {
            return Err("immediate mismatch".to_string());
        }

        let left_blocks = left_data.blocks();
        let right_blocks = right_data.blocks();
        if left_blocks.len() != right_blocks.len() {
            return Err("block operand length mismatch".to_string());
        }
        for (left_block, right_block) in left_blocks.iter().zip(right_blocks.iter()) {
            let mapped = block_map
                .get(left_block)
                .ok_or_else(|| "missing block mapping".to_string())?;
            if mapped != right_block {
                return Err("block mapping mismatch".to_string());
            }
        }

        if left_data.opcode() == Opcode::ConstInt {
            if left_data.get_const_int() != right_data.get_const_int() {
                return Err("const int mismatch".to_string());
            }
        }
        if left_data.opcode() == Opcode::ConstTime {
            if left_data.get_const_time() != right_data.get_const_time() {
                return Err("const time mismatch".to_string());
            }
        }

        match (left_data.get_ext_unit(), right_data.get_ext_unit()) {
            (Some(left_ext), Some(right_ext)) => {
                if left[left_ext].name != right[right_ext].name
                    || left[left_ext].sig != right[right_ext].sig
                {
                    return Err("external unit mismatch".to_string());
                }
            }
            (None, None) => {}
            _ => return Err("external unit presence mismatch".to_string()),
        }

        if left_data.opcode() == Opcode::Reg {
            let left_triggers: Vec<_> = left_data.triggers().collect();
            let right_triggers: Vec<_> = right_data.triggers().collect();
            if left_triggers.len() != right_triggers.len() {
                return Err("register trigger count mismatch".to_string());
            }
            for (left_trigger, right_trigger) in left_triggers.into_iter().zip(right_triggers) {
                if left_trigger.mode != right_trigger.mode {
                    return Err("register trigger mode mismatch".to_string());
                }
                match (left_trigger.gate, right_trigger.gate) {
                    (Some(left_gate), Some(right_gate)) => {
                        let mapped = value_map
                            .get(&left_gate)
                            .ok_or_else(|| "missing value mapping".to_string())?;
                        if *mapped != right_gate {
                            return Err("register trigger gate mismatch".to_string());
                        }
                    }
                    (None, None) => {}
                    _ => return Err("register trigger gate presence mismatch".to_string()),
                }
            }
        }
    }

    Ok(())
}
