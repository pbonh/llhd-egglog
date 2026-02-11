use crate::egglog::serialize::unit_to_egglog_commands;
use crate::schema::{cfg_schema_commands, pure_dfg_schema_commands};
use anyhow::Result;
use egglog::ast::Command;
use llhd::ir::Unit;
use typed_builder::TypedBuilder;

/// Typed builder for combining LLHD egglog commands.
///
/// ```no_run
/// use llhd::ir::Unit;
/// use llhd_egglog::LlhdEgglogProgram;
///
/// # fn build_program(unit: &Unit<'_>) -> anyhow::Result<String> {
/// let program = LlhdEgglogProgram::builder()
///     .build()
///     .with_pure_dfg_schema()
///     .with_cfg_schema()
///     .with_unit_facts(unit)?
///     .to_string();
/// # Ok(program)
/// # }
/// ```
///
/// ```no_run
/// use llhd_egglog::LlhdEgglogProgram;
/// use egglog::ast::{Action, Command, Expr};
///
/// # fn with_rules(rules: Vec<Command>) -> String {
/// let program = LlhdEgglogProgram::builder()
///     .build()
///     .add_rules(rules)
///     .to_string();
/// # program
/// # }
/// ```
#[derive(Debug, Clone, TypedBuilder)]
pub struct LlhdEgglogProgram {
    #[builder(default)]
    schema: Vec<Command>,
    #[builder(default)]
    facts: Vec<Command>,
    #[builder(default)]
    rules: Vec<Command>,
}

impl LlhdEgglogProgram {
    pub fn with_cfg_schema(mut self) -> Self {
        self.schema.extend(cfg_schema_commands());
        self
    }

    pub fn with_pure_dfg_schema(mut self) -> Self {
        self.schema.extend(pure_dfg_schema_commands());
        self
    }

    pub fn with_unit_facts(mut self, unit: &Unit<'_>) -> Result<Self> {
        self.facts.extend(unit_to_egglog_commands(unit)?);
        Ok(self)
    }

    pub fn add_rules(mut self, rules: Vec<Command>) -> Self {
        self.rules.extend(rules);
        self
    }

    pub fn commands(&self) -> Vec<Command> {
        let mut out = Vec::new();
        out.extend(self.schema.iter().cloned());
        out.extend(self.facts.iter().cloned());
        out.extend(self.rules.iter().cloned());
        out
    }

    pub fn to_string(&self) -> String {
        commands_to_string(&self.commands())
    }
}

pub(crate) fn commands_to_string(commands: &[Command]) -> String {
    commands
        .iter()
        .map(|cmd| cmd.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}
