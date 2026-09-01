# optimize-benderglauberman-classfunction — performance cleanup

Status: done
Target declarations: build-speed optimization of `BenderGlauberman/ClassFunction.lean` with unchanged public statements
Lean modules: `BenderGlauberman/ClassFunction.lean`
Sources: existing Lean module and imported character/representation interfaces

## Task

Reduce elaboration and kernel-checking work in the next unchecked file from `LEAN_FILES.md` without changing its public interface.

## Imports

- `Theory.Character` — character, scalar-product, induction, and representation interfaces
- `Theory.Representation.RepEquiv` — existing irreducibility transport theorem

## Bridges

- (none)

## Lessons

- context: `BenderGlauberman/ClassFunction.lean`
  symptom: a hand-built MonoidAlgebra linear-equivalence proof dominated the declaration profile
  cause: the project already provides `Theory.Representation.RepEquiv.irreducible_euqiv` through `ofRepresentationEquiv`
  rule: reuse the bundled representation-equivalence adapter before reconstructing scalar-action compatibility
  example: `isIrreducible_equiv`

## Resume (read this first — the recovery capsule)

Self-contained: reuse existing representation and submodule interfaces, then benchmark and validate the complete module.

- Current route: R1-interface-reuse
- Active route step: R1-S4
- Working node: `BenderGlauberman/ClassFunction.lean`
- Current blocker: none; all validation checks pass
- Next action: none; preserve the validated proof shape and select the next unchecked `LEAN_FILES.md` entry.
- Routes to avoid: R0-hand-rolled-equivalences — slower MonoidAlgebra induction and explicit complement bijection proofs
- Candidate next subnodes: none

## Progress

- validated: (2026-09-01T04:01:36Z) Baseline uncached `lake env lean BenderGlauberman/ClassFunction.lean`: WALL 11.27s, USER 53.50s, SYS 3.16s, RSS 2382500 KiB.
- initiated: (2026-09-01T04:01:36Z) Initialized task state because `tasks/` was absent; selected the first unchecked `LEAN_FILES.md` entry, `BenderGlauberman/ClassFunction.lean`.
- validated: (2026-09-01T06:52:28Z) Replaced `isIrreducible_equiv` with the existing `RepEquiv` adapter, replaced the explicit complementary-submodule bijection with `Submodule.prodEquivOfIsCompl`, and replaced repeated degree bookkeeping with private `decomp_degree_data`.
- validated: (2026-09-01T06:52:28Z) Replaced the one-dimensional scalar proof with `LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one`, used `Finsupp.basisSingleOne` directly in the regular-character trace proof, and simplified the integer-square bound.
- observed: (2026-09-01T06:52:28Z) Comparable uncached controls: original source WALL 11.56/12.17s, USER 56.81/55.73s; optimized source WALL 11.53/11.03s, USER 49.59/49.93s. User CPU fell by about 10–12%; wall time varied with parallel scheduling.
- validated: (2026-09-01T06:52:28Z) `lake build BenderGlauberman.ClassFunction` and representative dependents (`ClassFunctionHelpers`, `ClassFunctionProduct`, `Defs`, `Section1`) pass; full `lake build BenderGlauberman` and authoritative root `lake build` pass.
- validated: (2026-09-01T06:52:28Z) All 98 exported declarations checked with `#print axioms`; dependencies are contained in `{propext, Classical.choice, Quot.sound}`. Target placeholder scan is clean and `git diff --check` passes.
- validated: (2026-09-01T06:52:28Z) Marked `BenderGlauberman/ClassFunction.lean` complete in `LEAN_FILES.md`; removed disposable `Scratch/` probes.

## Proof Route

- Route id: R1-interface-reuse
- Sketch: Reuse existing representation equivalence and submodule direct-sum interfaces at action-free boundaries. Factor the duplicated degree extraction shared by the two scalar-product-one theorems into one private helper. Replace bespoke one-dimensional and regular-character proofs with existing finite-dimensional basis APIs. Preserve every public declaration statement and validate with uncached source compilation plus targeted builds.
- Main risk: An imported helper may have a propositionally equivalent but definitionally different type; retain explicit local endpoint lemmas and compile after each structural change.

Steps:
- R1-S1: profile the uncached module and identify declaration-level hotspots
  Direct consumer: `BenderGlauberman/ClassFunction.lean`
  Helpers: profiler output under `/tmp`
- R1-S2: replace bespoke equivalence and direct-sum constructions
  Direct consumer: `isIrreducible_equiv`, `coprod_equiv_of_isCompl`
  Helpers: `Theory.Representation.RepEquiv.irreducible_euqiv`, `Submodule.prodEquivOfIsCompl`
- R1-S3: factor duplicated degree extraction and simplify finite-dimensional proofs
  Direct consumer: `irreducible_char_degree_le_of_scalarProduct_one`, `char_eq_irreducible_of_scalarProduct_one_and_degree`
  Helpers: `decomp_degree_data`, `LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one`, `Finsupp.basisSingleOne`
- R1-S4: validate target and dependents, scan public declarations and forbidden placeholders
  Direct consumer: module and dependent builds
  Helpers: `lake build`, `#print axioms`, `rg`, `git diff --check`

## Subnodes

- `main` — done.
  Note: apply measured proof/interface reuse and complete validation.
  Dependencies: `R1-S1`, `R1-S2`, `R1-S3`.
- `profile` — done.
  Note: declaration profiler identified direct-sum, decomposition, scalar, and regular-character hotspots.
  Dependencies: none.
- `decomp_degree_data` — done.
  Note: shares degree/multiplicity extraction and identity-value formula between two public theorems.
  Dependencies: `char_decomp_coeff_one`.

## Route Ledger

- `R0-hand-rolled-equivalences` — pruned. Uses: `isIrreducible_equiv`, `coprod_equiv_of_isCompl`. Result: replaced after profiling. Node disposition: replace. Decision/Lesson: existing bundled equivalence and complement APIs avoid expensive custom induction and bijection proofs.
- `R1-interface-reuse` — done. Uses: `main`, `profile`, `decomp_degree_data`. Result: targeted, dependent, full library, and root builds pass. Node disposition: keep. Decision/Lesson: use `Finsupp.basisSingleOne` and finite-rank uniqueness APIs when the underlying representation space has an obvious finite basis.

## Validation

- Last check: (2026-09-01T06:52:28Z) targeted source, representative dependent, full BenderGlauberman, and root builds all pass; axiom and placeholder scans are clean.
- Final validation: closed.

## Source Notes

- Audit status: not applicable; this is a proof-performance refactor with no source theorem transcription.
- Findings: none.
