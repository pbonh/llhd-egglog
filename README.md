# LLHD CFG Skeleton + Egglog E-Graph Integration Summary

This document summarizes the additions in `llhd-egglog` for integrating a CFG
skeleton and an egglog e-graph alongside LLHD units.

## Overview

- The crate provides transient CFG skeleton and e-graph data for LLHD units.
- The e-graph captures non-stateful (pure) DFG operations using a Rust-encoded
  equivalent of `Wirelog/resources/egglog/llhd_dfg_sort.egg`.
- The CFG skeleton anchors control flow, side effects, and phi semantics as block
  arguments referencing e-classes.
- Data is transient and not serialized into LLHD assembly or binary formats.

## New Data Structures

- `CfgSkeleton` and related types in `llhd-egglog/src/cfg_skeleton.rs`.
- `UnitEGraph` and helpers in `llhd-egglog/src/egraph.rs`.
- `LlhdDfgSchema` and bridge constructors in `llhd-egglog/src/egglog_schema.rs`.
- `UnitAnalysis` in `llhd-egglog/src/lib.rs` to bundle both structures.

## Behavior

- Pure opcodes are embedded as `LLHDDFG` nodes in the e-graph.
- Side-effecting and control-flow ops are emitted in the CFG skeleton, referencing
  e-classes for operands.
- Phi nodes are lowered to block arguments, with per-edge argument lists on CFG
  skeleton terminators.
- Non-pure results are represented in the e-graph as `ValueRef` leaves to preserve
  references.

## Debugging

- `Unit::dump_cfg_skeleton()` is not available in upstream LLHD; instead use
  `CfgSkeleton::dump` with a `Unit` reference.
- `UnitEGraph::dump` prints the value-to-eclass mapping and tuple count.

## Notes

- The integration is transient and rebuildable; it does not modify LLHD file formats.
