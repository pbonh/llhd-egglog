use super::parse::{parse_commands, parse_egglog_program, ArgDir, ParsedValue};
use anyhow::{anyhow, bail, Result};
use llhd::ir::{Block, ExtUnit, InstData, Opcode, RegMode, UnitBuilder, UnitData, Value};
use llhd::table::TableKey;
use llhd::ty::Type;
use llhd::value::{IntValue, TimeValue};
use num::{BigInt, BigRational, Zero};
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
