use super::skeleton::{BlockArg, CfgSkeleton, SkeletonBlock, SkeletonStmt, SkeletonTerminator};
use crate::egraph::{is_pure_opcode, EClassRef, UnitEGraph};
use anyhow::Result;
use llhd::ir::{Block, Inst, InstData, Opcode, Unit, Value};
use llhd::table::TableKey;
use std::collections::HashMap;

impl CfgSkeleton {
    /// Build a CFG skeleton from a unit and its e-graph mapping.
    pub fn build_from_unit(unit: &Unit<'_>, egraph: &mut UnitEGraph) -> Result<Self> {
        let phi_map = collect_phi_info(unit, egraph)?;
        let mut blocks = Vec::new();

        for bb in unit.blocks() {
            let phi_infos = phi_map.get(&bb).cloned().unwrap_or_default();
            let args = phi_infos
                .iter()
                .map(|phi| BlockArg {
                    value: phi.value,
                    class: phi.class,
                })
                .collect::<Vec<_>>();

            let mut stmts = Vec::new();
            let mut terminator = None;

            for inst in unit.insts(bb) {
                let opcode = unit[inst].opcode();
                if opcode == Opcode::Phi {
                    continue;
                }

                if opcode.is_terminator() {
                    terminator = Some(build_terminator(unit, egraph, inst, &phi_map, bb)?);
                    continue;
                }

                if !is_pure_opcode(opcode) {
                    let args = unit[inst]
                        .args()
                        .iter()
                        .map(|&arg| egraph.ensure_value_ref(unit, arg))
                        .collect::<Result<Vec<_>, _>>()?;
                    let result = unit
                        .get_inst_result(inst)
                        .map(|value| egraph.ensure_value_ref(unit, value))
                        .transpose()?;
                    stmts.push(SkeletonStmt::Effect {
                        inst,
                        opcode,
                        args,
                        result,
                    });
                }
            }

            blocks.push(SkeletonBlock {
                block: bb,
                args,
                stmts,
                terminator,
            });
        }

        Ok(Self { blocks })
    }
}

#[derive(Debug, Clone)]
struct PhiInfo {
    value: Value,
    class: EClassRef,
    incoming: HashMap<Block, EClassRef>,
}

fn collect_phi_info(
    unit: &Unit<'_>,
    egraph: &mut UnitEGraph,
) -> Result<HashMap<Block, Vec<PhiInfo>>> {
    let mut out: HashMap<Block, Vec<PhiInfo>> = HashMap::new();
    for bb in unit.blocks() {
        for inst in unit.insts(bb) {
            if unit[inst].opcode() != Opcode::Phi {
                continue;
            }
            let (args, bbs) = match &unit[inst] {
                InstData::Phi { args, bbs, .. } => (args, bbs),
                _ => continue,
            };
            let value = match unit.get_inst_result(inst) {
                Some(value) => value,
                None => continue,
            };
            let class = egraph.ensure_value_ref(unit, value)?;
            let mut incoming = HashMap::new();
            for (&arg, &pred) in args.iter().zip(bbs.iter()) {
                let arg_class = egraph.ensure_value_ref(unit, arg)?;
                incoming.insert(pred, arg_class);
            }
            out.entry(bb).or_default().push(PhiInfo {
                value,
                class,
                incoming,
            });
        }
    }
    Ok(out)
}

fn build_terminator(
    unit: &Unit<'_>,
    egraph: &mut UnitEGraph,
    inst: Inst,
    phi_map: &HashMap<Block, Vec<PhiInfo>>,
    pred: Block,
) -> Result<SkeletonTerminator> {
    let data = &unit[inst];
    let opcode = data.opcode();
    match data {
        InstData::Jump { bbs, .. } if opcode == Opcode::Br => Ok(SkeletonTerminator::Br {
            inst,
            target: bbs[0],
            args: phi_args_for_target(phi_map, bbs[0], pred),
        }),
        InstData::Branch { args, bbs, .. } if opcode == Opcode::BrCond => {
            let cond = egraph.ensure_value_ref(unit, args[0])?;
            Ok(SkeletonTerminator::BrCond {
                inst,
                cond,
                then_target: bbs[0],
                then_args: phi_args_for_target(phi_map, bbs[0], pred),
                else_target: bbs[1],
                else_args: phi_args_for_target(phi_map, bbs[1], pred),
            })
        }
        InstData::Wait { bbs, args, .. } if opcode == Opcode::Wait => {
            let args = args
                .iter()
                .map(|&arg| egraph.ensure_value_ref(unit, arg))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SkeletonTerminator::Wait {
                inst,
                target: bbs[0],
                args,
            })
        }
        InstData::Wait { bbs, args, .. } if opcode == Opcode::WaitTime => {
            let mut args_iter = args.iter();
            let time = args_iter.next().copied().unwrap_or_else(Value::invalid);
            let time = egraph.ensure_value_ref(unit, time)?;
            let rest = args_iter
                .map(|&arg| egraph.ensure_value_ref(unit, arg))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SkeletonTerminator::WaitTime {
                inst,
                time,
                target: bbs[0],
                args: rest,
            })
        }
        InstData::Nullary { .. } if opcode == Opcode::Ret => Ok(SkeletonTerminator::Ret { inst }),
        InstData::Unary { args, .. } if opcode == Opcode::RetValue => {
            let value = egraph.ensure_value_ref(unit, args[0])?;
            Ok(SkeletonTerminator::RetValue { inst, value })
        }
        InstData::Nullary { .. } if opcode == Opcode::Halt => Ok(SkeletonTerminator::Halt { inst }),
        _ => Ok(SkeletonTerminator::Halt { inst }),
    }
}

fn phi_args_for_target(
    phi_map: &HashMap<Block, Vec<PhiInfo>>,
    target: Block,
    pred: Block,
) -> Vec<EClassRef> {
    phi_map
        .get(&target)
        .map(|phis| {
            phis.iter()
                .map(|phi| phi.incoming.get(&pred).copied().unwrap_or(phi.class))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default()
}
