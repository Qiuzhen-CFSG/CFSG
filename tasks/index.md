# Task board

Global orchestrator board. Each task or cohesive milestone has a card
`tasks/<slug>.md`; a task may own several related declarations and modules.

## Targets

- `Stellmacher.SectionOne.lemma_one_one` through `lemma_one_three` statement cluster — done — task: `tasks/stellmacher-section-one-basic.md` — modules: `Stellmacher.SectionOne`
- `Stellmacher.theorem_one` statement cluster — done — task: `tasks/stellmacher-theorem-one.md` — modules: `Stellmacher.FinalTheorem`
- `Stellmacher.theorem_two` statement cluster — done — task: `tasks/stellmacher-theorem-two.md` — modules: `Stellmacher.FinalTheorem`

## Dependency DAG

- `Stellmacher.SectionOne.lemma_one_one` → `Stellmacher.SectionOne.Hypotheses`, `Stellmacher.SectionOne.oddCore`, `Stellmacher.IsQuadraticAction`
- `Stellmacher.SectionOne.lemma_one_two` → `Stellmacher.SectionOne.actionClosure`, `Stellmacher.IsQuadraticAction`
- `Stellmacher.SectionOne.lemma_one_three` → `Stellmacher.SectionOne.involutionCommutator`, `Stellmacher.SectionOne.LemmaOneThreeConclusion`
- `Stellmacher.theorem_one` → `Stellmacher.baumannSubgroup`, `Stellmacher.IsCharacteristicTwoType`, `Stellmacher.IsOfMainTheoremType`
- `Stellmacher.theorem_two` → `Stellmacher.IsNTwoGroup`, `Stellmacher.IsOfExceptionalType`, `Stellmacher.IsSemidihedralGroup`

## Global lessons

- (none)

## Global source-fidelity findings

- [SF-stellmacher-1-odd-core] citation: `refs/latex/stellmacher-n-group.tex`:L249 transcribes `W = O_2(G)`, but the scan `refs/files/stellmacher-n-group.pdf`, journal p. 14, shows `W = O_{2'}(G)`; impact: all Section 1 declarations using `W`; disposition: repaired; evidence/repair: formalize `W` as `pPrimeCore 2 G`, while retaining the distinct standing hypothesis `O_2(G) = 1` from L243.

## Validation

- Authoritative build: `lake build Stellmacher` succeeded at 2026-09-01T11:51:14Z.
- Sorry inventory: exactly the requested statement-only proofs of `Stellmacher.theorem_one`, `Stellmacher.theorem_two`, `Stellmacher.SectionOne.lemma_one_one`, `lemma_one_two`, and `lemma_one_three` are `sorry`; no `admit`, `axiom`, or `opaque` occurs in the Stellmacher modules.

## Legacy

- `node_graph/*.md` are frozen legacy state; migrate a card into `tasks/` as it becomes active.
