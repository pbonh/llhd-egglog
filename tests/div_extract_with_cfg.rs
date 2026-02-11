use egglog::ast::{Command, Expr, Literal, Parser, PrintFunctionMode};
use egglog::{CommandOutput, EGraph};
use llhd::assembly::{parse_module_unchecked, write_module_string};
use llhd::ir::prelude::*;
use llhd_egglog::{unit_from_egglog_program, unit_to_egglog_program, LlhdEgglogProgram};
use std::collections::{HashMap, HashSet};
use std::fs;

mod common;
use common::units_equivalent;

#[test]
fn div_extract_with_cfg() {
    let input_src =
        fs::read_to_string("./tests/div_extract_with_cfg.llhd").expect("read input llhd");
    let expected_src = fs::read_to_string("./tests/div_extract_with_cfg_extracted.llhd")
        .expect("read expected llhd");

    let input_module = parse_module_unchecked(&input_src).expect("parse input module");
    let expected_module = parse_module_unchecked(&expected_src).expect("parse expected module");

    let mut rebuilt = Module::new();
    for decl in input_module.decls() {
        let data = DeclData {
            name: input_module[decl].name.clone(),
            sig: input_module[decl].sig.clone(),
            loc: input_module[decl].loc,
        };
        rebuilt.add_decl(data);
    }

    for unit in input_module.units() {
        let rebuilt_unit = rewrite_unit(unit);
        rebuilt.add_unit(rebuilt_unit);
    }

    if std::env::var("LLHD_EGGLOG_DUMP").ok().as_deref() == Some("1") {
        println!("{}", write_module_string(&rebuilt));
    }

    let mut right_units: Vec<_> = rebuilt.units().collect();
    for left_unit in expected_module.units() {
        let position = right_units.iter().position(|right_unit| {
            left_unit.kind() == right_unit.kind()
                && left_unit.sig() == right_unit.sig()
                && left_unit.name() == right_unit.name()
        });
        let Some(index) = position else {
            panic!("unit not found after div-extract-with-cfg");
        };
        let right_unit = right_units.swap_remove(index);
        if let Err(err) = units_equivalent(left_unit, right_unit) {
            panic!("unit mismatch after div-extract-with-cfg: {err}");
        }
    }

    if !right_units.is_empty() {
        panic!("extra units after div-extract-with-cfg");
    }

    let mut right_decls: Vec<_> = rebuilt.decls().collect();
    for left_decl in expected_module.decls() {
        let position = right_decls.iter().position(|right_decl| {
            expected_module[left_decl].name == rebuilt[*right_decl].name
                && expected_module[left_decl].sig == rebuilt[*right_decl].sig
        });
        let Some(index) = position else {
            panic!("decl not found after div-extract-with-cfg");
        };
        right_decls.swap_remove(index);
    }
    if !right_decls.is_empty() {
        panic!("extra decls after div-extract-with-cfg");
    }
}

fn rewrite_unit(unit: Unit<'_>) -> UnitData {
    let program = unit_to_egglog_program(&unit).expect("egglog program");
    let pure_rows = extract_pure_defs(&program);
    let root_facts = extract_root_facts(&program);
    let pure_facts = build_pure_facts(&pure_rows, &root_facts);

    let mut parser = Parser::default();
    let rules_src = fs::read_to_string("./tests/llhd_div_extract.egg").expect("read rules");
    let rules = parse_commands(&mut parser, &rules_src, "parse rules");
    let schedule_raw =
        fs::read_to_string("./tests/llhd_div_extract_schedule.egg").expect("read schedule");
    let schedule_src = strip_ruleset(&schedule_raw);
    let schedule = parse_commands(&mut parser, &schedule_src, "parse schedule");
    let pure_fact_program = pure_facts.join("\n");
    let pure_fact_commands = normalize_value_vars(parse_commands(
        &mut parser,
        &pure_fact_program,
        "parse pure facts",
    ));

    let mut program_commands = LlhdEgglogProgram::builder()
        .build()
        .with_pure_dfg_schema()
        .commands();
    program_commands.extend(pure_fact_commands);
    program_commands.extend(rules);
    program_commands.extend(schedule);

    let mut egraph = EGraph::default();
    egraph
        .run_program(program_commands)
        .expect("run egglog program");

    let rewritten_defs = extract_rewritten_defs(&mut egraph);
    let rewritten_program = rebuild_program(&program, &pure_rows, &rewritten_defs);
    unit_from_egglog_program(&rewritten_program).expect("deserialize program")
}

#[derive(Debug, Clone)]
struct PureDefRow {
    inst_id: usize,
    value_id: usize,
    block_id: usize,
    ty: String,
    term: String,
}

fn extract_pure_defs(program: &str) -> Vec<PureDefRow> {
    let mut parser = Parser::default();
    let mut rows = Vec::new();
    for line in program.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("(PureDef ") {
            continue;
        }
        let expr = parser
            .get_expr_from_string(None, trimmed)
            .expect("parse PureDef");
        rows.push(parse_pure_def_expr(&expr));
    }
    rows
}

fn extract_root_facts(program: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in program.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(RootDFG ") {
            out.push(trimmed.to_string());
        }
    }
    out
}

fn build_pure_facts(pure_rows: &[PureDefRow], root_facts: &[String]) -> Vec<String> {
    let mut parser = Parser::default();
    let mut defs = HashMap::new();
    for row in pure_rows {
        let expr = parser
            .get_expr_from_string(None, &row.term)
            .expect("parse PureDef term");
        defs.insert(row.value_id, expr);
    }
    let mut cache = HashMap::new();
    let mut out = Vec::new();
    for row in pure_rows {
        let mut visiting = HashSet::new();
        let expanded = expand_value(row.value_id, &defs, &mut cache, &mut visiting);
        let ty = egglog_type_term(&row.ty);
        out.push(format!(
            "(PureDef {} {} {} {} {})",
            row.inst_id, row.value_id, row.block_id, ty, expanded
        ));
    }
    out.extend(root_facts.iter().cloned());
    out
}

fn expand_value(
    value_id: usize,
    defs: &HashMap<usize, Expr>,
    cache: &mut HashMap<usize, String>,
    visiting: &mut HashSet<usize>,
) -> String {
    if let Some(cached) = cache.get(&value_id) {
        return cached.clone();
    }
    if !visiting.insert(value_id) {
        return format!("(ValueRef {})", value_id);
    }
    let Some(expr) = defs.get(&value_id) else {
        return format!("(ValueRef {})", value_id);
    };
    let expanded = expand_expr(expr, defs, cache, visiting);
    visiting.remove(&value_id);
    cache.insert(value_id, expanded.clone());
    expanded
}

fn expand_expr(
    expr: &Expr,
    defs: &HashMap<usize, Expr>,
    cache: &mut HashMap<usize, String>,
    visiting: &mut HashSet<usize>,
) -> String {
    match expr {
        Expr::Call(_, head, args) if head == "ValueRef" => args
            .get(0)
            .and_then(parse_optional_value_id)
            .map(|id| expand_value(id, defs, cache, visiting))
            .unwrap_or_else(|| "(ValueRef -1)".to_string()),
        Expr::Var(_, atom) => parse_value_var_atom(atom)
            .map(|id| expand_value(id, defs, cache, visiting))
            .unwrap_or_else(|| expr.to_string()),
        Expr::Call(_, head, args) => {
            let rendered: Vec<String> = args
                .iter()
                .map(|arg| expand_expr(arg, defs, cache, visiting))
                .collect();
            if rendered.is_empty() {
                format!("({})", head)
            } else {
                format!("({} {})", head, rendered.join(" "))
            }
        }
        _ => expr.to_string(),
    }
}

fn extract_rewritten_defs(egraph: &mut EGraph) -> Vec<PureDefRow> {
    let output = egraph
        .print_function("PureDef", None, None, PrintFunctionMode::Default)
        .expect("print PureDef")
        .expect("PureDef output");

    match output {
        CommandOutput::PrintFunction(_, termdag, terms, _) => terms
            .into_iter()
            .map(|(term, _)| {
                let rendered = termdag.to_string(term);
                let mut parser = Parser::default();
                let expr = parser
                    .get_expr_from_string(None, &rendered)
                    .expect("parse rewritten PureDef");
                parse_pure_def_expr(&expr)
            })
            .collect(),
        other => panic!("unexpected output: {other:?}"),
    }
}

fn rebuild_program(
    program: &str,
    original_defs: &[PureDefRow],
    rewritten_defs: &[PureDefRow],
) -> String {
    let root_ids: HashSet<_> = extract_inst_roots(program).into_iter().collect();
    let filtered_defs: Vec<_> = rewritten_defs
        .iter()
        .filter(|row| root_ids.contains(&row.value_id))
        .cloned()
        .collect();
    let linearized = linearize_defs(original_defs, &filtered_defs);
    let reachable = compute_reachable_values(program, &linearized);
    let mut rewritten_lines = Vec::new();
    for row in &linearized {
        if !reachable.contains(&row.value_id) {
            continue;
        }
        rewritten_lines.push(format!(
            "(PureDef {} {} {} {} {})",
            row.inst_id, row.value_id, row.block_id, row.ty, row.term
        ));
    }
    let mut lines = Vec::new();
    for line in program.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(PureDef ") {
            continue;
        }
        lines.push(line.to_string());
    }
    lines.extend(rewritten_lines);
    lines.join("\n")
}

fn linearize_defs(original_defs: &[PureDefRow], rewritten_defs: &[PureDefRow]) -> Vec<PureDefRow> {
    let mut ty_by_value = HashMap::new();
    for row in original_defs {
        ty_by_value.insert(row.value_id, row.ty.clone());
    }
    let mut value_to_inst = HashMap::new();
    let mut max_value_id = 0usize;
    let mut max_inst_id = 0usize;
    for row in original_defs {
        value_to_inst.insert(row.value_id, row.inst_id);
        max_value_id = max_value_id.max(row.value_id);
        max_inst_id = max_inst_id.max(row.inst_id);
    }

    let used_value_ids: HashSet<_> = rewritten_defs.iter().map(|row| row.value_id).collect();
    let mut available_value_ids: Vec<_> = original_defs
        .iter()
        .map(|row| row.value_id)
        .filter(|id| !used_value_ids.contains(id))
        .collect();
    available_value_ids.sort_unstable();

    let mut pool = IdPool {
        available_value_ids,
        next_value_id: max_value_id + 1,
        next_inst_id: max_inst_id + 1,
        value_to_inst,
    };

    let mut parser = Parser::default();
    let mut rows_by_value: HashMap<usize, PureDefRow> = HashMap::new();
    for row in rewritten_defs {
        let expr = parser
            .get_expr_from_string(None, &row.term)
            .expect("parse rewritten term");
        let root_ty = ty_by_value
            .get(&row.value_id)
            .cloned()
            .unwrap_or_else(|| row.ty.clone());
        let mut rows =
            lower_expr_with_target(&expr, row.value_id, row.block_id, &root_ty, &mut pool);
        for new_row in rows.drain(..) {
            rows_by_value.insert(new_row.value_id, new_row);
        }
    }

    rows_by_value.into_values().collect()
}

struct IdPool {
    available_value_ids: Vec<usize>,
    next_value_id: usize,
    next_inst_id: usize,
    value_to_inst: HashMap<usize, usize>,
}

impl IdPool {
    fn alloc_value_id(&mut self) -> usize {
        if let Some(id) = self.available_value_ids.first().copied() {
            self.available_value_ids.remove(0);
            return id;
        }
        let id = self.next_value_id;
        self.next_value_id += 1;
        id
    }

    fn inst_id_for(&mut self, value_id: usize) -> usize {
        if let Some(id) = self.value_to_inst.get(&value_id).copied() {
            return id;
        }
        let id = self.next_inst_id;
        self.next_inst_id += 1;
        self.value_to_inst.insert(value_id, id);
        id
    }
}

fn lower_expr_with_target(
    expr: &Expr,
    target_value_id: usize,
    block_id: usize,
    ty: &str,
    pool: &mut IdPool,
) -> Vec<PureDefRow> {
    let (value_id, mut rows) = lower_expr(expr, block_id, ty, pool, Some(target_value_id));
    if value_id != target_value_id {
        rows.push(PureDefRow {
            inst_id: pool.inst_id_for(target_value_id),
            value_id: target_value_id,
            block_id,
            ty: ty.to_string(),
            term: format!("(Alias (ValueRef {}))", value_id),
        });
    }
    rows
}

fn lower_expr(
    expr: &Expr,
    block_id: usize,
    ty: &str,
    pool: &mut IdPool,
    target_value_id: Option<usize>,
) -> (usize, Vec<PureDefRow>) {
    if let Some(value_id) = parse_value_ref(expr) {
        return (value_id, Vec::new());
    }

    let Expr::Call(_, head, args) = expr else {
        return (pool.alloc_value_id(), Vec::new());
    };

    let mut rows = Vec::new();
    let mut rendered_args = Vec::new();
    for arg in args {
        if is_value_expr(arg) {
            let (value_id, child_rows) = lower_expr(arg, block_id, ty, pool, None);
            rows.extend(child_rows);
            rendered_args.push(format!("(ValueRef {})", value_id));
        } else {
            rendered_args.push(arg.to_string());
        }
    }

    let value_id = target_value_id.unwrap_or_else(|| pool.alloc_value_id());
    let inst_id = pool.inst_id_for(value_id);
    let term = if rendered_args.is_empty() {
        format!("({})", head)
    } else {
        format!("({} {})", head, rendered_args.join(" "))
    };
    rows.push(PureDefRow {
        inst_id,
        value_id,
        block_id,
        ty: ty.to_string(),
        term,
    });
    (value_id, rows)
}

fn is_value_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Call(_, _, _))
}

fn parse_value_ref(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Call(_, head, args) if head == "ValueRef" => {
            args.get(0).and_then(parse_optional_value_id)
        }
        _ => None,
    }
}

fn parse_pure_def_expr(expr: &Expr) -> PureDefRow {
    match expr {
        Expr::Call(_, head, args) if head == "PureDef" => {
            if args.len() != 5 {
                panic!("PureDef expects 5 fields");
            }
            let inst_id = parse_usize_expr(&args[0]);
            let value_id = parse_usize_expr(&args[1]);
            let block_id = parse_usize_expr(&args[2]);
            let ty = args[3].to_string();
            let term = args[4].to_string();
            PureDefRow {
                inst_id,
                value_id,
                block_id,
                ty,
                term,
            }
        }
        _ => panic!("expected PureDef call"),
    }
}

fn parse_usize_expr(expr: &Expr) -> usize {
    match expr {
        Expr::Lit(_, egglog::ast::Literal::Int(value)) => {
            if *value < 0 {
                panic!("invalid usize");
            }
            *value as usize
        }
        Expr::Var(_, atom) => atom.parse::<usize>().expect("invalid usize atom"),
        _ => panic!("invalid usize expression"),
    }
}

fn egglog_type_term(ty: &str) -> String {
    if ty.trim_start().starts_with('(') {
        ty.to_string()
    } else {
        format!("({})", ty)
    }
}

fn compute_reachable_values(program: &str, pure_defs: &[PureDefRow]) -> HashSet<usize> {
    let roots = extract_inst_roots(program);
    let mut by_value: HashMap<usize, &PureDefRow> = HashMap::new();
    for row in pure_defs {
        by_value.insert(row.value_id, row);
    }

    let mut reachable = HashSet::new();
    let mut stack = roots;
    let mut parser = Parser::default();
    while let Some(value_id) = stack.pop() {
        if !reachable.insert(value_id) {
            continue;
        }
        let Some(row) = by_value.get(&value_id) else {
            continue;
        };
        let expr = parser
            .get_expr_from_string(None, &row.term)
            .expect("parse PureDef term");
        let mut refs = Vec::new();
        collect_value_refs(&expr, &mut refs);
        for value in refs {
            if !reachable.contains(&value) {
                stack.push(value);
            }
        }
    }
    reachable
}

fn extract_inst_roots(program: &str) -> Vec<usize> {
    let mut parser = Parser::default();
    let mut roots = Vec::new();
    for line in program.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("(Inst ") {
            continue;
        }
        let expr = parser
            .get_expr_from_string(None, trimmed)
            .expect("parse Inst");
        let Expr::Call(_, head, args) = expr else {
            continue;
        };
        if head != "Inst" || args.len() < 6 {
            continue;
        }
        let args_expr = &args[5];
        let Expr::Call(_, list_head, list_items) = args_expr else {
            continue;
        };
        if list_head != "list" {
            continue;
        }
        for item in list_items {
            if let Some(value) = parse_optional_value_id(item) {
                roots.push(value);
            }
        }
    }
    roots
}

fn parse_optional_value_id(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Var(_, atom) if atom == "invalid" => None,
        Expr::Var(_, atom) => atom.parse::<usize>().ok(),
        Expr::Lit(_, egglog::ast::Literal::Int(value)) => {
            if *value < 0 {
                None
            } else {
                Some(*value as usize)
            }
        }
        _ => None,
    }
}

fn parse_value_var_atom(atom: &str) -> Option<usize> {
    let trimmed = atom.strip_prefix('$').unwrap_or(atom);
    let mut chars = trimmed.chars();
    if chars.next()? != 'v' {
        return None;
    }
    let rest: String = chars.collect();
    rest.parse::<usize>().ok()
}

fn collect_value_refs(expr: &Expr, out: &mut Vec<usize>) {
    match expr {
        Expr::Call(_, head, args) if head == "ValueRef" => {
            if let Some(value) = args.get(0).map(parse_optional_value_id).flatten() {
                out.push(value);
            }
        }
        Expr::Call(_, _, args) => {
            for arg in args {
                collect_value_refs(arg, out);
            }
        }
        _ => {}
    }
}

fn strip_ruleset(program: &str) -> String {
    program
        .lines()
        .filter(|line| !line.trim().starts_with("(ruleset "))
        .collect::<Vec<_>>()
        .join("\n")
}

fn parse_commands(parser: &mut Parser, program: &str, context: &str) -> Vec<Command> {
    parser
        .get_program_from_string(None, program)
        .unwrap_or_else(|err| panic!("{context}: {err}"))
}

fn normalize_value_vars(commands: Vec<Command>) -> Vec<Command> {
    commands
        .into_iter()
        .map(|command| match command {
            Command::Action(egglog::ast::Action::Expr(span, expr)) => Command::Action(
                egglog::ast::Action::Expr(span, normalize_value_var_expr(expr)),
            ),
            Command::Action(egglog::ast::Action::Let(span, name, expr)) => Command::Action(
                egglog::ast::Action::Let(span, name, normalize_value_var_expr(expr)),
            ),
            other => other,
        })
        .collect()
}

fn normalize_value_var_expr(expr: Expr) -> Expr {
    match expr {
        Expr::Var(span, atom) => match parse_value_var_atom(&atom) {
            Some(id) => Expr::Call(
                span.clone(),
                "ValueRef".to_string(),
                vec![Expr::Lit(span, Literal::Int(id as i64))],
            ),
            None => Expr::Var(span, atom),
        },
        Expr::Call(span, head, args) => Expr::Call(
            span,
            head,
            args.into_iter().map(normalize_value_var_expr).collect(),
        ),
        other => other,
    }
}
