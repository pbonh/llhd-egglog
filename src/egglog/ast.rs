use anyhow::{anyhow, Result};
use egglog::ast::{Action, Command, Expr, Literal, RustSpan, Span};

pub(crate) fn expr_atom(value: impl Into<String>) -> Expr {
    Expr::Var(::egglog::span!(), value.into())
}

pub(crate) fn expr_var(value: &str) -> Expr {
    Expr::Var(::egglog::span!(), value.to_string())
}

pub(crate) fn expr_string(value: String) -> Expr {
    Expr::Lit(::egglog::span!(), Literal::String(value))
}

pub(crate) fn expr_i64(value: i64) -> Expr {
    Expr::Lit(::egglog::span!(), Literal::Int(value))
}

pub(crate) fn expr_usize(value: usize) -> Result<Expr> {
    let value = i64::try_from(value).map_err(|_| anyhow!("value out of i64 range"))?;
    Ok(expr_i64(value))
}

pub(crate) fn expr_list(values: Vec<Expr>) -> Expr {
    expr_call("list", values)
}

pub(crate) fn expr_call(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call(::egglog::span!(), name.to_string(), args)
}

pub(crate) fn expr_command(expr: Expr) -> Command {
    Command::Action(Action::Expr(::egglog::span!(), expr))
}

pub(crate) fn expr_call_parts(expr: &Expr) -> Result<(&str, &[Expr])> {
    match expr {
        Expr::Call(_, head, args) => Ok((head.as_str(), args.as_slice())),
        _ => Err(anyhow!("expected call")),
    }
}

pub(crate) fn parse_expr_atom(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Var(_, value) => Ok(value.clone()),
        _ => Err(anyhow!("expected atom")),
    }
}

pub(crate) fn parse_expr_string(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Lit(_, Literal::String(value)) => Ok(value.clone()),
        Expr::Var(_, value) => Ok(value.clone()),
        _ => Err(anyhow!("expected string")),
    }
}

pub(crate) fn parse_expr_int(expr: &Expr) -> Result<i64> {
    match expr {
        Expr::Lit(_, Literal::Int(value)) => Ok(*value),
        _ => Err(anyhow!("expected integer")),
    }
}

pub(crate) fn parse_expr_list(expr: &Expr) -> Result<Vec<Expr>> {
    let (head, args) = expr_call_parts(expr)?;
    if head != "list" {
        return Err(anyhow!("expected list"));
    }
    Ok(args.to_vec())
}

pub(crate) fn parse_usize(expr: &Expr) -> Result<usize> {
    let value = parse_expr_int(expr)?;
    if value < 0 {
        return Err(anyhow!("invalid usize"));
    }
    usize::try_from(value).map_err(|_| anyhow!("invalid usize"))
}
