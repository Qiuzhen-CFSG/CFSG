# stellmacher-theorem-one — Theorem 1 statement

Status: done
Target declarations: `Stellmacher.theorem_one` and its introductory interfaces
Lean modules: `Stellmacher.FinalTheorem`
Sources: `refs/latex/stellmacher-n-group.tex`:L108-L118, L133-L145

## Task

Pin a source-faithful Lean statement of Stellmacher's Theorem 1, leaving its proof as `sorry`.

## Imports

- `FeitThompson.Gorenstein.Chapter8_2` — the Thompson subgroup `J(S₀)` and `Z(J(S₀))`.
- `FeitThompson.PGroup.Omega` — `Ω₁`.
- `Theory.Quasithin` — 2-local and maximal 2-local subgroup predicates.
- `FeitThompson.PCore.PCore` — `O₂` as `pCore 2`.
- `Stellmacher.FinalTheorem` local interfaces — the four Theorem 2 models and local-amalgam data.

## Bridges

- (none)

## Lessons

- (none)

## Resume (read this first — the recovery capsule)

- Current route: R1-main-statement
- Active route step: complete
- Working node: `main`
- Current blocker: none; the supplied transcription omits the promised Section 8–10 refinements, so the statement uses the explicit local-amalgam meaning at lines 133–145.
- Next action: none; the Theorem 1 statement cluster is complete.
- Routes to avoid: replacing "`H` is type `X`" by an ambient isomorphism `H ≃ X`; duplicating the existing amalgam fields for Theorem 1.
- Candidate next subnodes: `LocalTypeAmalgam`, `IsMainTheoremModel`, `baumannSubgroup`, `IsCharacteristicTwoType`, `IsOfMainTheoremType`.

## Progress

- initiated: (2026-09-01T11:35:16Z) Existing APIs were located for `thompsonCenter`, `omega₁`, `pCore`, 2-locality, and subgroup centralizers; the remaining work is statement composition and elaboration.
- validated: (2026-09-01T11:38:38Z) The generic amalgam and all Theorem 1 interfaces elaborated in `Scratch/stellmacher-theorem-one/Probe.lean`; the probe was removed after `lake build Stellmacher.FinalTheorem` and `lake build Stellmacher` succeeded.
- closed: (2026-09-01T11:38:38Z) `theorem_one` is public with its two source hypotheses and eight-type conclusion; its proof is the requested `sorry`.

## Proof Route

- Route id: R1-main-statement
- Sketch: Generalize `ExceptionalAmalgam` to a model-predicate-indexed `LocalTypeAmalgam` and retain the old name as an abbreviation. Define the eight-group conclusion by extending `IsExceptionalModel` with the four additional Theorem 1 models. Define `baumannSubgroup S₀` as `C_{S₀}(Ω₁(ZJ(S₀)))` using `thompsonCenter` and mapped `omega₁`. Define characteristic-2 type by `C_U(O₂(U)) ≤ O₂(U)`. State the two source hypotheses directly and conclude the existence of the corresponding local amalgam; leave only `theorem_one` as `sorry`.
- Main risk: exact coercions through `ZJ(S₀)` and the higher-order model predicate of `LocalTypeAmalgam`.

Steps:
- probe-interfaces: elaborate the higher-order amalgam index and subgroup coercions.
  Direct consumer: `Stellmacher.theorem_one`
  Helpers: all planned subnodes.
- pin-statement: transfer the validated declaration cluster to the owner module.
  Direct consumer: `Stellmacher.theorem_one`
  Helpers: all planned subnodes.
- validate: build `Stellmacher.FinalTheorem` and the wrapper.
  Direct consumer: `Stellmacher.theorem_one`
  Helpers: none.

## Subnodes

- `main` — done.
  Note: Theorem 1 with hypotheses (i), (ii), and the eight local-type alternatives.
  Dependencies: all listed helpers.
- `LocalTypeAmalgam` — done.
  Note: shared local-amalgam data indexed by a model predicate.
  Dependencies: maximal 2-locality and `pCore`.
- `IsMainTheoremModel` — done.
  Note: the eight named local models in the conclusion.
  Dependencies: `IsExceptionalModel` and concrete/order models for the remaining four groups.
- `baumannSubgroup` — done.
  Note: `C_{S₀}(Ω₁(ZJ(S₀)))` as a subgroup of the ambient group.
  Dependencies: `thompsonCenter`, `omega₁`.
- `IsCharacteristicTwoType` — done.
  Note: `C_U(O₂(U)) ≤ O₂(U)`.
  Dependencies: `pCore` and subgroup centralizer.
- `IsOfMainTheoremType` — done.
  Note: existence of a shared local amalgam with one of the eight models.
  Dependencies: `LocalTypeAmalgam`, `IsMainTheoremModel`.

## Route Ledger

- `R1-main-statement` — done. Uses: `main` and all planned helpers. Result: owner and wrapper builds succeed. Node disposition: keep. Decision/Lesson: share the local-amalgam structure with Theorem 2. Evidence: source lines 133–140 give the same meaning of "type" for the main theorem list; `LocalTypeAmalgam` serves both model predicates.

## Validation

- Last check: `lake build Stellmacher.FinalTheorem` and `lake build Stellmacher` succeeded at 2026-09-01T11:38:38Z. Expected warnings: the two statement-only `sorry`s; pre-existing imported deprecation at `FeitThompson/Fitting/Faithful.lean:55`.
- Final validation: closed for statement-only scope. Axiom checking is intentionally deferred until the requested proof placeholders are replaced.

## Source Notes

- Audit status: theorem statement and available introductory definition audited; closed for the supplied source excerpt.
- [omitted-definition] `refs/latex/stellmacher-n-group.tex`:L137-L140 points to Sections 8–10 for precise type definitions, but the supplied transcription ends near the start of Section 2; impact: the conclusion can use only the explicit compatible local-amalgam description at L133-L145; disposition: source-faithful introductory statement; evidence/repair: retain pair compatibility and `O₂(⟨P₁,P₂⟩)=1` rather than ambient isomorphism.
