//! CFG skeleton and egglog e-graph helpers for LLHD.

mod cfg_skeleton;
mod egglog_schema;
mod egglog_unit;
mod egraph;

pub use crate::cfg_skeleton::{
    BlockArg, CfgSkeleton, SkeletonBlock, SkeletonStmt, SkeletonTerminator,
};
pub use crate::egglog_schema::{
    cfg_schema_program, LlhdCfgSchema, LlhdDfgSchema, VecValue, CFG_SK_BLOCK, CFG_SK_BLOCK_ARG,
    CFG_SK_EFFECT, CFG_SK_TERM_BR, CFG_SK_TERM_BR_COND, CFG_SK_TERM_HALT, CFG_SK_TERM_RET,
    CFG_SK_TERM_RET_VALUE, CFG_SK_TERM_WAIT, CFG_SK_TERM_WAIT_TIME,
};
pub use crate::egglog_unit::{unit_from_egglog_program, unit_to_egglog_program};
pub use crate::egraph::{is_pure_opcode, EClassRef, UnitEGraph};

#[cfg(feature = "egglog-debug")]
pub use crate::egglog_unit::dump_egglog_debug;

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
