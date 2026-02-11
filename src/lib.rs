//! CFG skeleton and egglog e-graph helpers for LLHD.

mod cfg;
mod egglog;
mod egraph;
mod schema;

pub use crate::cfg::{BlockArg, CfgSkeleton, SkeletonBlock, SkeletonStmt, SkeletonTerminator};
pub use crate::egglog::{
    unit_from_egglog_commands, unit_from_egglog_program, unit_to_egglog_commands,
    unit_to_egglog_program,
};
pub use crate::egraph::{is_pure_opcode, EClassRef, UnitEGraph};
pub use crate::schema::{
    cfg_schema_program, pure_dfg_schema_program, LlhdCfgSchema, LlhdDfgSchema, VecValue,
    CFG_SK_BLOCK, CFG_SK_BLOCK_ARG, CFG_SK_EFFECT, CFG_SK_TERM_BR, CFG_SK_TERM_BR_COND,
    CFG_SK_TERM_HALT, CFG_SK_TERM_RET, CFG_SK_TERM_RET_VALUE, CFG_SK_TERM_WAIT,
    CFG_SK_TERM_WAIT_TIME,
};

#[cfg(feature = "egglog-debug")]
pub use crate::egglog::dump_egglog_debug;

use anyhow::Result;
use llhd::ir::Unit;

/// Combined CFG skeleton + e-graph data for a unit.
#[derive(Debug, Clone)]
pub struct UnitAnalysis {
    /// Reduced CFG skeleton.
    pub cfg_skeleton: CfgSkeleton,
    /// E-graph mapping for DFG values.
    pub egraph: UnitEGraph,
}

impl UnitAnalysis {
    /// Build both the CFG skeleton and e-graph for a unit.
    pub fn build_from_unit(unit: &Unit<'_>) -> Result<Self> {
        let mut egraph = UnitEGraph::build_from_unit(unit)?;
        let cfg_skeleton = CfgSkeleton::build_from_unit(unit, &mut egraph)?;
        Ok(Self {
            cfg_skeleton,
            egraph,
        })
    }
}
