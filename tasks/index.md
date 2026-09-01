# Task board

Global orchestrator board. Each task or cohesive milestone has a card
`tasks/<slug>.md`; a task may own several related declarations and modules.
This file holds only cross-task state: the target table, the dependency DAG,
global lessons, and authoritative validation.

## Targets

- `ClassFunction performance cleanup` — done — task: `tasks/optimize-benderglauberman-classfunction.md` — modules: `BenderGlauberman/ClassFunction.lean`

## Dependency DAG

- `ClassFunction performance cleanup` → `Theory.Character`, `Theory.Representation.RepEquiv`

## Global lessons

- (none)

## Global source-fidelity findings

- (none)

## Validation

- Authoritative build: `(2026-09-01T06:52:28Z) lake build` passed; `lake build BenderGlauberman` and targeted dependents also passed.
- Sorry inventory: `(2026-09-01T06:52:28Z) clean for `BenderGlauberman/ClassFunction.lean`; all exported axiom checks passed with only `{propext, Classical.choice, Quot.sound}`.

## Legacy

- `node_graph/*.md` are frozen legacy state; migrate a card into `tasks/` as it becomes active.
