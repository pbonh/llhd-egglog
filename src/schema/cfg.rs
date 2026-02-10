use super::VecValue;
use egglog_bridge::{ColumnTy, DefaultVal, EGraph, FunctionConfig, FunctionId, MergeFn};

#[cfg(test)]
use std::fmt::Write;

/// Egglog table ids for the LLHD CFG skeleton schema.
#[derive(Debug, Clone)]
pub struct LlhdCfgSchema {
    /// Table id for CFG skeleton blocks.
    pub sk_block: FunctionId,
    /// Table id for CFG skeleton block arguments.
    pub sk_block_arg: FunctionId,
    /// Table id for CFG skeleton effectful statements.
    pub sk_effect: FunctionId,
    /// Table id for CFG skeleton branch terminators.
    pub sk_term_br: FunctionId,
    /// Table id for CFG skeleton conditional branch terminators.
    pub sk_term_br_cond: FunctionId,
    /// Table id for CFG skeleton wait terminators.
    pub sk_term_wait: FunctionId,
    /// Table id for CFG skeleton waittime terminators.
    pub sk_term_wait_time: FunctionId,
    /// Table id for CFG skeleton return terminators.
    pub sk_term_ret: FunctionId,
    /// Table id for CFG skeleton return-value terminators.
    pub sk_term_ret_value: FunctionId,
    /// Table id for CFG skeleton halt terminators.
    pub sk_term_halt: FunctionId,
}

impl LlhdCfgSchema {
    /// Register all LLHD CFG skeleton tables in the e-graph.
    pub fn register(egraph: &mut EGraph) -> Self {
        let int_base = egraph.base_values_mut().register_type::<i64>();
        let string_base = egraph.base_values_mut().register_type::<String>();
        let vec_base = egraph.base_values_mut().register_type::<VecValue>();

        let ctor = |egraph: &mut EGraph, name: &str, schema: Vec<ColumnTy>| {
            egraph.add_table(FunctionConfig {
                schema,
                default: DefaultVal::FreshId,
                merge: MergeFn::UnionId,
                name: name.into(),
                can_subsume: false,
            })
        };

        let table = |egraph: &mut EGraph, table: &CfgTable| {
            let schema = table
                .columns
                .iter()
                .map(|column| match column.ty {
                    CfgColumnTy::Id => ColumnTy::Id,
                    CfgColumnTy::Int => ColumnTy::Base(int_base),
                    CfgColumnTy::Atom => ColumnTy::Base(string_base),
                    CfgColumnTy::VecValue => ColumnTy::Base(vec_base),
                })
                .collect();
            ctor(egraph, table.name, schema)
        };

        Self {
            sk_block: table(egraph, &CFG_TABLES[0]),
            sk_block_arg: table(egraph, &CFG_TABLES[1]),
            sk_effect: table(egraph, &CFG_TABLES[2]),
            sk_term_br: table(egraph, &CFG_TABLES[3]),
            sk_term_br_cond: table(egraph, &CFG_TABLES[4]),
            sk_term_wait: table(egraph, &CFG_TABLES[5]),
            sk_term_wait_time: table(egraph, &CFG_TABLES[6]),
            sk_term_ret: table(egraph, &CFG_TABLES[7]),
            sk_term_ret_value: table(egraph, &CFG_TABLES[8]),
            sk_term_halt: table(egraph, &CFG_TABLES[9]),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CfgColumnTy {
    Id,
    Int,
    Atom,
    VecValue,
}

impl CfgColumnTy {
    #[cfg(test)]
    fn as_str(self) -> &'static str {
        match self {
            Self::Id => "Id",
            Self::Int => "i64",
            Self::Atom => "Atom",
            Self::VecValue => "VecValue",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CfgColumn {
    name: &'static str,
    ty: CfgColumnTy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CfgTable {
    name: &'static str,
    columns: &'static [CfgColumn],
}

/// Table name for CFG skeleton blocks.
pub const CFG_SK_BLOCK: &str = "SkBlock";
/// Table name for CFG skeleton block arguments.
pub const CFG_SK_BLOCK_ARG: &str = "SkBlockArg";
/// Table name for CFG skeleton effectful statements.
pub const CFG_SK_EFFECT: &str = "SkEffect";
/// Table name for CFG skeleton branch terminators.
pub const CFG_SK_TERM_BR: &str = "SkTermBr";
/// Table name for CFG skeleton conditional branch terminators.
pub const CFG_SK_TERM_BR_COND: &str = "SkTermBrCond";
/// Table name for CFG skeleton wait terminators.
pub const CFG_SK_TERM_WAIT: &str = "SkTermWait";
/// Table name for CFG skeleton waittime terminators.
pub const CFG_SK_TERM_WAIT_TIME: &str = "SkTermWaitTime";
/// Table name for CFG skeleton return terminators.
pub const CFG_SK_TERM_RET: &str = "SkTermRet";
/// Table name for CFG skeleton return-value terminators.
pub const CFG_SK_TERM_RET_VALUE: &str = "SkTermRetValue";
/// Table name for CFG skeleton halt terminators.
pub const CFG_SK_TERM_HALT: &str = "SkTermHalt";

const CFG_SK_BLOCK_COLUMNS: &[CfgColumn] = &[CfgColumn {
    name: "block",
    ty: CfgColumnTy::Int,
}];

const CFG_SK_BLOCK_ARG_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "value",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "class",
        ty: CfgColumnTy::Id,
    },
];

const CFG_SK_EFFECT_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "opcode",
        ty: CfgColumnTy::Atom,
    },
    CfgColumn {
        name: "result",
        ty: CfgColumnTy::Id,
    },
    CfgColumn {
        name: "args",
        ty: CfgColumnTy::VecValue,
    },
];

const CFG_SK_TERM_BR_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "target",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "args",
        ty: CfgColumnTy::VecValue,
    },
];

const CFG_SK_TERM_BR_COND_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "cond",
        ty: CfgColumnTy::Id,
    },
    CfgColumn {
        name: "then_target",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "then_args",
        ty: CfgColumnTy::VecValue,
    },
    CfgColumn {
        name: "else_target",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "else_args",
        ty: CfgColumnTy::VecValue,
    },
];

const CFG_SK_TERM_WAIT_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "target",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "args",
        ty: CfgColumnTy::VecValue,
    },
];

const CFG_SK_TERM_WAIT_TIME_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "time",
        ty: CfgColumnTy::Id,
    },
    CfgColumn {
        name: "target",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "args",
        ty: CfgColumnTy::VecValue,
    },
];

const CFG_SK_TERM_RET_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
];

const CFG_SK_TERM_RET_VALUE_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "value",
        ty: CfgColumnTy::Id,
    },
];

const CFG_SK_TERM_HALT_COLUMNS: &[CfgColumn] = &[
    CfgColumn {
        name: "block",
        ty: CfgColumnTy::Int,
    },
    CfgColumn {
        name: "inst",
        ty: CfgColumnTy::Int,
    },
];

const CFG_TABLES: &[CfgTable] = &[
    CfgTable {
        name: CFG_SK_BLOCK,
        columns: CFG_SK_BLOCK_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_BLOCK_ARG,
        columns: CFG_SK_BLOCK_ARG_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_EFFECT,
        columns: CFG_SK_EFFECT_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_BR,
        columns: CFG_SK_TERM_BR_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_BR_COND,
        columns: CFG_SK_TERM_BR_COND_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_WAIT,
        columns: CFG_SK_TERM_WAIT_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_WAIT_TIME,
        columns: CFG_SK_TERM_WAIT_TIME_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_RET,
        columns: CFG_SK_TERM_RET_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_RET_VALUE,
        columns: CFG_SK_TERM_RET_VALUE_COLUMNS,
    },
    CfgTable {
        name: CFG_SK_TERM_HALT,
        columns: CFG_SK_TERM_HALT_COLUMNS,
    },
];

/// Reference CFG schema as a readable egglog program string.
pub fn cfg_schema_program() -> &'static str {
    CFG_SCHEMA_PROGRAM
}

const CFG_SCHEMA_PROGRAM: &str = concat!(
    "(table SkBlock (block i64))\n",
    "(table SkBlockArg (block i64) (value i64) (class Id))\n",
    "(table SkEffect (block i64) (inst i64) (opcode Atom) (result Id) (args VecValue))\n",
    "(table SkTermBr (block i64) (inst i64) (target i64) (args VecValue))\n",
    "(table SkTermBrCond (block i64) (inst i64) (cond Id) (then_target i64) (then_args VecValue) (else_target i64) (else_args VecValue))\n",
    "(table SkTermWait (block i64) (inst i64) (target i64) (args VecValue))\n",
    "(table SkTermWaitTime (block i64) (inst i64) (time Id) (target i64) (args VecValue))\n",
    "(table SkTermRet (block i64) (inst i64))\n",
    "(table SkTermRetValue (block i64) (inst i64) (value Id))\n",
    "(table SkTermHalt (block i64) (inst i64))\n",
);

#[cfg(test)]
fn render_cfg_schema_program() -> String {
    let mut out = String::new();
    for table in CFG_TABLES {
        let _ = write!(out, "(table {}", table.name);
        for column in table.columns {
            let _ = write!(out, " ({} {})", column.name, column.ty.as_str());
        }
        out.push_str(")\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cfg_schema_matches_reference() {
        assert_eq!(render_cfg_schema_program(), cfg_schema_program());
    }
}
