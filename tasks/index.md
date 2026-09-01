# Task board

Global orchestrator board. Each task or cohesive milestone has a card
`tasks/<slug>.md`; a task may own several related declarations and modules.

## Targets

- `Stellmacher.theorem_two` statement cluster — done — task: `tasks/stellmacher-theorem-two.md` — modules: `Stellmacher.FinalTheorem`

## Dependency DAG

- `Stellmacher.theorem_two` → `Stellmacher.IsNTwoGroup`, `Stellmacher.IsOfExceptionalType`, `Stellmacher.IsSemidihedralGroup`

## Global lessons

- (none)

## Global source-fidelity findings

- (none)

## Validation

- Authoritative build: `lake build Stellmacher` succeeded at 2026-09-01T11:08:19Z.
- Sorry inventory: exactly the requested proof of `Stellmacher.theorem_two` is `sorry` in `Stellmacher/FinalTheorem.lean`; no `admit`, `axiom`, or `opaque` occurs there.

## Legacy

- `node_graph/*.md` are frozen legacy state; migrate a card into `tasks/` as it becomes active.
