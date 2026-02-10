use llhd::ir::Opcode;

/// Return true for opcodes that are pure in the DFG.
pub fn is_pure_opcode(opcode: Opcode) -> bool {
    matches!(
        opcode,
        Opcode::ConstInt
            | Opcode::ConstTime
            | Opcode::Alias
            | Opcode::ArrayUniform
            | Opcode::Array
            | Opcode::Struct
            | Opcode::Not
            | Opcode::Neg
            | Opcode::Add
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
            | Opcode::Shl
            | Opcode::Shr
            | Opcode::Mux
            | Opcode::Sig
            | Opcode::Prb
            | Opcode::InsField
            | Opcode::InsSlice
            | Opcode::ExtField
            | Opcode::ExtSlice
    )
}
