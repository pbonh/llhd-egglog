# LLHD CFG Skeleton + Egglog E-Graph Integration Summary

This document summarizes the additions in `llhd-egglog` for integrating a CFG
skeleton and an egglog e-graph alongside LLHD units, with a pure-DFG term layer
for rewrite-friendly reasoning.

## Overview

- The crate provides transient CFG skeleton and e-graph data for LLHD units.
- The e-graph captures non-stateful (pure) DFG operations using a Rust-encoded
  equivalent of `llhd_dfg_sort.egg`.
- The CFG skeleton anchors control flow, side effects, and phi semantics as block
  arguments referencing e-classes.
- Pure DFG operations are also emitted as first-class terms (`LLHDPureDFG`) in the
  egglog program to enable rewrite-driven optimization.
- Data is transient and not serialized into LLHD assembly or binary formats.

## New Data Structures

- `CfgSkeleton` and related types in `src/cfg/skeleton.rs`.
- `UnitEGraph` and helpers in `src/egraph/mod.rs`.
- `LlhdDfgSchema` and bridge constructors in `src/schema/dfg.rs`.
- `UnitAnalysis` in `llhd-egglog/src/lib.rs` to bundle both structures.

## Behavior

- Pure opcodes are embedded as `LLHDDFG` nodes in the e-graph and also emitted as
  `LLHDPureDFG` terms via `PureDef` facts for rewriting.
- Side-effecting and control-flow ops are emitted in the CFG skeleton and as `Inst`
  entries in the egglog program, referencing e-classes for operands.
- Pure ops are not serialized as `Inst` entries; they are reconstructed from
  `PureDef` (which carries inst id, value id, block id, type, and term).
- Phi nodes are lowered to block arguments, with per-edge argument lists on CFG
  skeleton terminators.
- Non-pure results referenced by pure terms are represented as `ValueRef` leaves to
  preserve cross-domain references.

## Debugging

- `Unit::dump_cfg_skeleton()` is not available in upstream LLHD; instead use
  `CfgSkeleton::dump` with a `Unit` reference.
- `UnitEGraph::dump` prints the value-to-eclass mapping and tuple count.

## Notes

- The integration is transient and rebuildable; it does not modify LLHD file formats.
