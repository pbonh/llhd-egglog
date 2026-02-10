use egglog_core_relations::BaseValue;
use egglog_core_relations::Value;

/// Wrapper for Vec values stored in egglog base tables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VecValue(pub Vec<Value>);

impl BaseValue for VecValue {}
