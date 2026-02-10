use crate::egraph::EClassRef;
use llhd::ir::{Block, Inst, Opcode, Unit, Value};
use std::fmt::Write;

/// A CFG skeleton for an LLHD unit, capturing control flow and side effects.
#[derive(Debug, Clone, Default)]
pub struct CfgSkeleton {
    /// Blocks in traversal order with reduced IR details.
    pub blocks: Vec<SkeletonBlock>,
}

/// A block entry with arguments, statements, and terminator.
#[derive(Debug, Clone)]
pub struct SkeletonBlock {
    /// The original block id.
    pub block: Block,
    /// Block arguments mapped to e-classes.
    pub args: Vec<BlockArg>,
    /// Effectful statements in this block.
    pub stmts: Vec<SkeletonStmt>,
    /// Terminator for the block, if any.
    pub terminator: Option<SkeletonTerminator>,
}

/// A single block argument and its e-class.
#[derive(Debug, Clone)]
pub struct BlockArg {
    /// The value for the argument.
    pub value: Value,
    /// The e-class representing the argument.
    pub class: EClassRef,
}

/// A reduced statement capturing side effects.
#[derive(Debug, Clone)]
pub enum SkeletonStmt {
    /// An effectful instruction with optional result class.
    Effect {
        /// The instruction id.
        inst: Inst,
        /// The opcode for the instruction.
        opcode: Opcode,
        /// Argument e-classes.
        args: Vec<EClassRef>,
        /// Result e-class, if any.
        result: Option<EClassRef>,
    },
}

/// A reduced terminator capturing control flow.
#[derive(Debug, Clone)]
pub enum SkeletonTerminator {
    /// Unconditional branch.
    Br {
        /// The branch instruction.
        inst: Inst,
        /// Target block.
        target: Block,
        /// Argument e-classes passed to the target.
        args: Vec<EClassRef>,
    },
    /// Conditional branch.
    BrCond {
        /// The branch instruction.
        inst: Inst,
        /// Condition e-class.
        cond: EClassRef,
        /// Then target block.
        then_target: Block,
        /// Argument e-classes for the then edge.
        then_args: Vec<EClassRef>,
        /// Else target block.
        else_target: Block,
        /// Argument e-classes for the else edge.
        else_args: Vec<EClassRef>,
    },
    /// Wait terminator with target block.
    Wait {
        /// The wait instruction.
        inst: Inst,
        /// Target block.
        target: Block,
        /// Argument e-classes passed to the target.
        args: Vec<EClassRef>,
    },
    /// Wait-for-time terminator with target block.
    WaitTime {
        /// The waittime instruction.
        inst: Inst,
        /// Time e-class.
        time: EClassRef,
        /// Target block.
        target: Block,
        /// Argument e-classes passed to the target.
        args: Vec<EClassRef>,
    },
    /// Return terminator with no value.
    Ret {
        /// The return instruction.
        inst: Inst,
    },
    /// Return terminator with a value.
    RetValue {
        /// The return instruction.
        inst: Inst,
        /// Returned value e-class.
        value: EClassRef,
    },
    /// Halt terminator.
    Halt {
        /// The halt instruction.
        inst: Inst,
    },
}

impl CfgSkeleton {
    /// Dump the CFG skeleton in human-readable form.
    pub fn dump(&self, unit: &Unit<'_>) -> String {
        let mut out = String::new();
        for block in &self.blocks {
            let _ = writeln!(out, "{}:", block.block.dump(unit));
            if !block.args.is_empty() {
                let args = block
                    .args
                    .iter()
                    .map(|arg| format!("{} => {}", arg.value.dump(unit), arg.class))
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(out, "  args: {}", args);
            }
            for stmt in &block.stmts {
                match stmt {
                    SkeletonStmt::Effect {
                        inst,
                        opcode,
                        args,
                        result,
                    } => {
                        let args = args
                            .iter()
                            .map(|arg| arg.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        if let Some(result) = result {
                            let _ = writeln!(
                                out,
                                "  {} [{}] ({}) => {}",
                                inst.dump(unit),
                                opcode,
                                args,
                                result
                            );
                        } else {
                            let _ = writeln!(out, "  {} [{}] ({})", inst.dump(unit), opcode, args);
                        }
                    }
                }
            }
            if let Some(term) = &block.terminator {
                let _ = writeln!(out, "  term: {}", term.dump(unit));
            }
        }
        out
    }
}

impl SkeletonTerminator {
    fn dump(&self, unit: &Unit<'_>) -> String {
        match self {
            SkeletonTerminator::Br { inst, target, args } => format!(
                "{} br {} ({})",
                inst.dump(unit),
                target.dump(unit),
                format_args(args)
            ),
            SkeletonTerminator::BrCond {
                inst,
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => format!(
                "{} brcond {} ? {}({}) : {}({})",
                inst.dump(unit),
                cond,
                then_target.dump(unit),
                format_args(then_args),
                else_target.dump(unit),
                format_args(else_args)
            ),
            SkeletonTerminator::Wait { inst, target, args } => format!(
                "{} wait {} ({})",
                inst.dump(unit),
                target.dump(unit),
                format_args(args)
            ),
            SkeletonTerminator::WaitTime {
                inst,
                time,
                target,
                args,
            } => format!(
                "{} waittime {} {} ({})",
                inst.dump(unit),
                time,
                target.dump(unit),
                format_args(args)
            ),
            SkeletonTerminator::Ret { inst } => format!("{} ret", inst.dump(unit)),
            SkeletonTerminator::RetValue { inst, value } => {
                format!("{} ret {}", inst.dump(unit), value)
            }
            SkeletonTerminator::Halt { inst } => format!("{} halt", inst.dump(unit)),
        }
    }
}

fn format_args(args: &[EClassRef]) -> String {
    args.iter()
        .map(|arg| arg.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}
