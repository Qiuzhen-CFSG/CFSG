# stellmacher-theorem-two — Theorem 2 statement

Status: in progress
Target declarations: `Stellmacher.theorem_two` and its statement-level interfaces
Lean modules: `Stellmacher.FinalTheorem`
Sources: `refs/latex/stellmacher-n-group.tex`:L69-L140; `refs/files/stellmacher-n-group.pdf`:journal pp. 12, 38, 45, 65

## Task

Prove the source-faithful Lean statement of Stellmacher's Theorem 2 without
`sorry`.  The statement-level interfaces below were completed first; the
current phase formalizes the paper's proof reduction section by section.

## Imports

- `Theory.Quasithin` — 2-local and maximal 2-local subgroup predicates.
- `Theory.Comparator.Defs` — strongly embedded subgroup predicate.
- `FeitThompson.PCore.PCore` — the subgroups `Oₚ(U)`/`Oₚ′(U)` as
  `pCore p U`/`pPrimeCore p U`.
- Mathlib finite matrix, permutation, dihedral, and Sylow group interfaces — named models and the explicit alternatives.

## Bridges

- (none)

## Lessons

- (none)

## Resume (read this first — the recovery capsule)

- Current route: R6-section-by-section-proof
- Active route step: statement-major-steps
- Working node: `main`
- Current blocker: the repository has no proved Stellmacher classification lemmas for the Sections 2–11 case analysis; first write explicit major-step interfaces and prove the elementary reduction lemmas, then isolate the first genuinely missing classification theorem.
- Next action: add the major-step statements (amalgam reduction, local-type classification, and final trichotomy) in a dedicated proof module and prove their branch-injection/reduction lemmas.
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
- initiated: (2026-09-01T13:22:05Z) Parallel PDF review compared the theorem scan with the LaTeX transcription and found that clause (e) uses the odd `2'`-core, not the 2-core.
- closed: (2026-09-01T13:22:05Z) Replaced `pCore 2 U ≠ ⊥` by `pPrimeCore 2 U ≠ ⊥`, updated the theorem documentation, and rebuilt the owner module successfully.
- validated: (2026-09-01T14:56:46Z) Independent subagent reviews confirmed clauses (a)--(e), the `C₂ × S₄` model, and the semidihedral presentation.  They also checked that the existing finite-group strong-embedding interface derives Sylow-2 containment, so no unrelated predicate change is needed.
- initiated: (2026-09-01T15:29:03Z) The objective was reopened for a sorry-free proof.  A repository-wide search found no proved theorem supplying the Sections 2–11 classification, so the proof is being decomposed into explicit major-step statements before attempting the first classification node.

## Proof Route

- Route id: R4-pdf-source-audit
- Sketch: Compare every alternative in the Lean statement with the theorem scan, then repair any transcription-level notation drift. Preserve the shared local-amalgam interface for the phrase “of type X”, because the exact type-specific predicates in PDF Definitions 8.2, 8.6, and 10.1 are outside the supplied statement cluster. Use `pPrimeCore 2 U` for the scanned `O_{2'}(U)` clause and rebuild the owner and wrapper.
- Main risk: confusing the 2-core `O₂` used in the amalgam hypotheses with the odd core `O_{2'}` used in alternative (e).

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
- pdf-audit: compare the theorem and local-type definitions against the journal scan.
  Direct consumer: `Stellmacher.theorem_two`
  Helpers: `IsOfExceptionalType` documentation.

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
  Note: the four named groups in clause (a), with concrete PSL/S₆ witnesses where available and explicit simple/order surrogates for `G₂(2)'` and `²F₄(2)'`.
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
- `R4-pdf-source-audit` — done. Uses: `theorem_two` clause (e). Result: corrected the transcription's dropped prime by using `pPrimeCore 2 U`; retained the shared local-amalgam interface because the exact type-specific predicates in PDF Sections 8–10 require infrastructure outside this statement cluster. Decision/Lesson: distinguish `O₂` from `O_{2'}` whenever the scan and transcription disagree. Evidence: PDF journal p. 12 and targeted build at 2026-09-01T13:22:05Z.
- `R5-independent-review` — done. Uses: all theorem alternatives and imported interfaces. Result: two independent reviews found no further statement correction; the apparent missing Sylow-2 clause in `Theory.Comparator.IsStronglyEmbedded` is derivable in the finite setting. Decision/Lesson: keep the project-wide predicate unchanged and document the source-fidelity boundary for the later type-specific definitions. Evidence: review probes and `BenderSuzuki.SE.Basic.IsStronglyEmbedded.containsSylowTwo`.
- `R6-section-by-section-proof` — active. Sketch: formalize the paper's final reduction as three explicit interfaces (selection of a Gomi amalgam pair, classification of the resulting local pair, and the terminal alternatives), prove the disjunction-injection and normalization lemmas first, and then replace each interface placeholder with a proof from the corresponding source section. Main risk: the current repository contains none of the required Sections 2–11 classification infrastructure, so no unproved interface may be used as a bridge in the final theorem.

## Validation

- Last check: `lake build Stellmacher.FinalTheorem`, `lake build Stellmacher`, and the full `lake build` succeeded at 2026-09-01T15:03:38Z. Expected warnings: the statement-only `sorry`s on `theorem_one` and `theorem_two`; pre-existing imported deprecation at `FeitThompson/Fitting/Faithful.lean:55`.
- Final validation: pending the proof phase; the statement build remains green, but `theorem_two` currently depends on `sorryAx`.

## Source Notes

- Audit status: theorem statement audited against the PDF scan; exact type-specific definitions are present later in the PDF (Definitions 8.2, 8.6, and 10.1) but are represented here by the documented shared introductory interface.
- [omitted-definition] `refs/latex/stellmacher-n-group.tex`:L133-L140 promises precise definitions in Sections 8–10, but the supplied transcription ends at line 577 near the start of Section 2; impact: `IsOfExceptionalType` cannot quote those refinements verbatim; disposition: source-faithful statement using the explicit compatible local-amalgam description at L133-L140; evidence/repair: do not replace the phrase by ambient group isomorphism.
- [transcription] `refs/latex/stellmacher-n-group.tex`:L129 drops the prime in `O_{2'}(U)`; the PDF scan at journal p. 12 is authoritative for this symbol, and the Lean statement now uses `pPrimeCore 2 U`.
- [model-interface] PDF Definitions 8.2, 8.6, and 10.1 impose type-specific local conditions; no corresponding concrete `G₂(2)'`/`²F₄(2)'` group models are imported, so `IsExceptionalModel` documents simple/order surrogates and `IsOfExceptionalType` is an explicit shared interface rather than an ambient isomorphism claim.
