# stellmacher-theorem-two — Theorem 2 statement

Status: done
Target declarations: `Stellmacher.theorem_two` and its statement-level interfaces
Lean modules: `Stellmacher.FinalTheorem`
Sources: `refs/latex/stellmacher-n-group.tex`:L69-L140

## Task

Pin a source-faithful Lean statement of Stellmacher's Theorem 2, leaving its proof as `sorry`.

## Imports

- `Theory.Quasithin` — 2-local and maximal 2-local subgroup predicates.
- `Theory.Comparator.Defs` — strongly embedded subgroup predicate.
- `FeitThompson.PCore.PCore` — the subgroup `Oₚ(U)` as `pCore p U`.
- Mathlib finite matrix, permutation, dihedral, and Sylow group interfaces — named models and the explicit alternatives.

## Bridges

- (none)

## Lessons

- (none)

## Resume (read this first — the recovery capsule)

- Current route: R3-combine-model
- Active route step: complete
- Working node: `main`
- Current blocker: none; the later Section 8–10 definitions of "of type X" are absent from the supplied transcription, so the landed statement uses the explicit amalgam description at lines 133–140 and records that source boundary.
- Next action: none; the requested interface cleanup is complete.
- Routes to avoid: interpreting "of type X" as `H ≃ X`, which contradicts the source's local-amalgam definition.
- Candidate next subnodes: `IsNTwoGroup`, `IsExceptionalModel`, `IsOfExceptionalType`, `IsSemidihedralGroup`.

## Progress

- observed: (2026-09-01T10:14:17Z) The target file has a clean direct-Lean baseline and currently contains only `module` plus an empty `Stellmacher` namespace.
- observed: (2026-09-01T10:14:17Z) Existing project interfaces cover 2-locality, strong embedding, `pCore`, Sylow subgroups, and dihedral groups; no semidihedral or Stellmacher local-type interface exists.
- validated: (2026-09-01T10:18:40Z) `Scratch/stellmacher-theorem-two/Probe.lean` elaborates the complete declaration cluster; its only diagnostic is the intentionally admitted `theorem_two` proof.
- closed: (2026-09-01T10:21:32Z) `Stellmacher/FinalTheorem.lean` elaborates directly; the only diagnostic is the requested `sorry` warning on `Stellmacher.theorem_two`, and the disposable probe was removed.
- closed: (2026-09-01T11:01:55Z) Inlined alternatives (a)–(e) into the public type of `theorem_two` and removed the one-use `TheoremTwoConclusion` definition; direct elaboration again reports only the requested `sorry` warning.
- initiated: (2026-09-01T11:07:06Z) Replace the redundant `ExceptionalType` tag and `ModelsExceptionalType` match with one inductive proposition carrying the four model witnesses.
- closed: (2026-09-01T11:08:19Z) `IsExceptionalModel` now carries the four model witnesses directly; targeted builds of `Stellmacher.FinalTheorem` and the `Stellmacher` wrapper both succeed with only the requested `sorry` warning.
- validated: (2026-09-01T11:38:38Z) `ExceptionalAmalgam` was retained as an abbreviation of the shared `LocalTypeAmalgam IsExceptionalModel`; Theorem 2's public statement rebuilds unchanged alongside Theorem 1.

## Proof Route

- Route id: R3-combine-model
- Sketch: Replace the data tag plus match-defined predicate by `IsExceptionalModel X`, an inductive proposition with one constructor for each source type. Store that proposition directly in `ExceptionalAmalgam.model`, eliminating its `kind` field. Preserve all four model witnesses and the public statement of `theorem_two`; no compatibility wrapper is needed because the removed declarations have no downstream consumers. Rebuild `Stellmacher.FinalTheorem` and the `Stellmacher` wrapper.
- Main risk: a `Prop`-valued inductive may carry only proof-relevant constructor arguments; all four proposed witnesses are propositions, so no large-elimination interface is required.

Steps:
- probe-interfaces: confirm exact Lean types and coercions for the statement-level declarations.
  Direct consumer: `Stellmacher.theorem_two`
  Helpers: all statement-level interfaces.
- pin-statement: transfer the elaborated declaration cluster to the owning module.
  Direct consumer: `Stellmacher.theorem_two`
  Helpers: all statement-level interfaces.
- validate: run direct source elaboration and inspect diagnostics/diff.
  Direct consumer: `Stellmacher.theorem_two`
  Helpers: none.

## Subnodes

- `main` — done.
  Note: assemble the five source alternatives.
  Dependencies: all statement-level interfaces.
- `IsNTwoGroup` — done.
  Note: finite groups whose 2-local subgroups are solvable.
  Dependencies: `Theory.Quasithin.IsTwoLocal`.
- `ExceptionalType` / `ModelsExceptionalType` — pruned.
  Note: redundant tag-plus-match interface replaced by `IsExceptionalModel`.
  Dependencies: none.
- `IsExceptionalModel` — done.
  Note: the four named groups in clause (a), with their witnesses carried by constructors.
  Dependencies: finite matrix/permutation group models.
- `IsOfExceptionalType` — done.
  Note: the local-amalgam meaning of "of type X" from the source introduction.
  Dependencies: `LocalTypeAmalgam`, `IsExceptionalModel`, maximal 2-locality, `pCore`.
- `IsSemidihedralGroup` — done.
  Note: the standard presentation used in clause (b).
  Dependencies: elementary group APIs.
- `TheoremTwoConclusion` — pruned.
  Note: removed as a one-use wrapper; source clauses (a)–(e) are inlined in `theorem_two`.
  Dependencies: none.

## Route Ledger

- `R1-statement` — done. Uses: `main` and all listed statement interfaces. Result: direct-source elaboration succeeds. Node disposition: keep. Decision/Lesson: preserve the source's local-amalgam reading of "type". Evidence: source lines 133–140 and `Stellmacher/FinalTheorem.lean` fields `ExceptionalAmalgam.e1`, `e2`, `compatible`, and `intersection_surjective`.
- `R2-inline` — done. Uses: `main`. Result: `TheoremTwoConclusion` removed and its body inlined without statement drift. Node disposition: prune `TheoremTwoConclusion`, keep `main`. Decision/Lesson: none. Evidence: direct elaboration at 2026-09-01T11:01:55Z.
- `R3-combine-model` — done. Uses: `IsExceptionalModel`, `IsOfExceptionalType`. Result: the redundant tag and match definition were removed without changing the four alternatives. Node disposition: prune `ExceptionalType` and `ModelsExceptionalType`; keep `IsExceptionalModel`. Decision/Lesson: none. Evidence: `lake build Stellmacher.FinalTheorem` and `lake build Stellmacher` at 2026-09-01T11:08:19Z.

## Validation

- Last check: `lake build Stellmacher.FinalTheorem` and `lake build Stellmacher` succeeded at 2026-09-01T11:38:38Z. Expected warnings: the statement-only `sorry`s on `theorem_one` and `theorem_two`; pre-existing imported deprecation at `FeitThompson/Fitting/Faithful.lean:55`.
- Final validation: closed for statement-only scope. Axiom checking is intentionally not applicable until the requested proof placeholder is replaced.

## Source Notes

- Audit status: theorem statement and available introductory definitions audited; closed for the supplied source excerpt.
- [omitted-definition] `refs/latex/stellmacher-n-group.tex`:L133-L140 promises precise definitions in Sections 8–10, but the supplied transcription ends at line 577 near the start of Section 2; impact: `IsOfExceptionalType` cannot quote those refinements verbatim; disposition: source-faithful statement using the explicit compatible local-amalgam description at L133-L140; evidence/repair: do not replace the phrase by ambient group isomorphism.
