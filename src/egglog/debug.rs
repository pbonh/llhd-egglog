use crate::schema::cfg_schema_program;
use llhd::ir::Unit;

/// Dump a human-readable egglog program with schema notes.
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
    let cfg_schema = cfg_schema_program();
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
