use super::ast::{expr_atom, expr_call, expr_i64, expr_list, parse_expr_list, parse_usize};
use anyhow::{bail, Result};
use egglog::ast::Expr;
use llhd::ir::Signature;
use llhd::ty::{
    array_ty, enum_ty, func_ty, int_ty, pointer_ty, signal_ty, struct_ty, time_ty, void_ty, Type,
    TypeKind,
};

pub(crate) fn type_term(ty: &Type) -> Expr {
    match ty.as_ref() {
        TypeKind::VoidType => expr_atom("Void"),
        TypeKind::TimeType => expr_atom("Time"),
        TypeKind::IntType(bits) => expr_call("IntTy", vec![expr_i64(*bits as i64)]),
        TypeKind::EnumType(states) => expr_call("Enum", vec![expr_i64(*states as i64)]),
        TypeKind::PointerType(inner) => expr_call("Pointer", vec![type_term(inner)]),
        TypeKind::SignalType(inner) => expr_call("Signal", vec![type_term(inner)]),
        TypeKind::ArrayType(len, inner) => {
            expr_call("ArrayTy", vec![expr_i64(*len as i64), type_term(inner)])
        }
        TypeKind::StructType(fields) => expr_call(
            "StructTy",
            vec![types_list(fields.iter().cloned().collect())],
        ),
        TypeKind::FuncType(args, ret) => {
            expr_call("FuncTy", vec![types_list(args.clone()), type_term(ret)])
        }
        TypeKind::EntityType(ins, outs) => expr_call(
            "EntityTy",
            vec![types_list(ins.clone()), types_list(outs.clone())],
        ),
    }
}

pub(crate) fn types_list(types: Vec<Type>) -> Expr {
    expr_list(types.iter().map(type_term).collect())
}

pub(crate) fn parse_optional_type(expr: &Expr) -> Result<Option<Type>> {
    if let Expr::Var(_, atom) = expr {
        if atom == "None" {
            return Ok(None);
        }
    }
    Ok(Some(parse_type(expr)?))
}

pub(crate) fn parse_type_list(expr: &Expr) -> Result<Vec<Type>> {
    let items = parse_expr_list(expr)?;
    items.iter().map(parse_type).collect()
}

pub(crate) fn parse_type(expr: &Expr) -> Result<Type> {
    match expr {
        Expr::Var(_, atom) => match atom.as_str() {
            "Void" => Ok(void_ty()),
            "Time" => Ok(time_ty()),
            other => bail!("unknown type atom {}", other),
        },
        Expr::Call(_, head, rest) => match head.as_str() {
            "IntTy" => Ok(int_ty(parse_usize(single(rest, "IntTy")?)?)),
            "Enum" => Ok(enum_ty(parse_usize(single(rest, "Enum")?)?)),
            "Pointer" => Ok(pointer_ty(parse_type(single_term(rest, "Pointer")?)?)),
            "Signal" => Ok(signal_ty(parse_type(single_term(rest, "Signal")?)?)),
            "ArrayTy" => {
                if rest.len() != 2 {
                    bail!("ArrayTy expects 2 fields");
                }
                let len = parse_usize(&rest[0])?;
                let ty = parse_type(&rest[1])?;
                Ok(array_ty(len, ty))
            }
            "StructTy" => {
                if rest.len() != 1 {
                    bail!("StructTy expects list field");
                }
                let fields = parse_type_list(&rest[0])?;
                Ok(struct_ty(fields))
            }
            "FuncTy" => {
                if rest.len() != 2 {
                    bail!("FuncTy expects args list and return type");
                }
                let args = parse_type_list(&rest[0])?;
                let ret = parse_type(&rest[1])?;
                Ok(func_ty(args, ret))
            }
            "EntityTy" => {
                if rest.len() != 2 {
                    bail!("EntityTy expects inputs and outputs list");
                }
                let ins = parse_type_list(&rest[0])?;
                let outs = parse_type_list(&rest[1])?;
                Ok(llhd::ty::entity_ty(ins, outs))
            }
            other => bail!("unknown type form {}", other),
        },
        Expr::Lit(_, _) => bail!("unexpected literal in type"),
    }
}

pub(crate) fn signature_from_parts(
    inputs: Vec<Type>,
    outputs: Vec<Type>,
    ret: Option<Type>,
) -> Signature {
    let mut sig = Signature::new();
    for ty in inputs {
        sig.add_input(ty);
    }
    for ty in outputs {
        sig.add_output(ty);
    }
    if let Some(ty) = ret {
        sig.set_return_type(ty);
    }
    sig
}

fn single<'a>(rest: &'a [Expr], name: &str) -> Result<&'a Expr> {
    if rest.len() != 1 {
        bail!("{} expects 1 field", name);
    }
    Ok(&rest[0])
}

fn single_term<'a>(rest: &'a [Expr], name: &str) -> Result<&'a Expr> {
    single(rest, name)
}
