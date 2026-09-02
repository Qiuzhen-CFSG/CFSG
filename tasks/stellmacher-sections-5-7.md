# stellmacher-sections-5-7 — Sections 5–7 statement translation

Status: in progress
Target declarations: Stellmacher results 5.1–5.4, 6.1–6.4, and 7.1–7.8
Lean modules: `Stellmacher.SectionFiveToSeven.Defs`, `SectionFive`, `SectionSix`, `SectionSeven`
Sources: `refs/files/stellmacher-n-group.pdf` (journal pp. 27–36); `refs/latex/stellmacher-n-group.tex` (Section 5, lines 1062–1252)

## Task

Translate every numbered result in Sections 5–7 into a separate public Lean file while preserving the PDF hypotheses and conclusions.

## Imports

- `Stellmacher.FinalTheorem` — characteristic-2 and local-type predicates.
- `Stellmacher.SectionsOneToFourDefs` — shared ambient `O²`/core notation.
- `Theory.Quasithin`, Feit–Thompson core/Thompson APIs, and Mathlib Sylow/subnormal APIs — local subgroup notation.

## Bridges

- (none)

## Lessons

- context: `CosetGraphContext`; symptom: `Type*` structure failed with an invalid universe level; cause: the vertex universe was independent of the ambient group; rule: bind `universe u v`, use `G : Type u`, `Vertex : Type v`, and result `Type (max u v + 1)`; example: `CosetGraphContext`.
- context: dependent structure fields; symptom: grouped fields such as `a a' : Γ.Vertex` or `p n : ℕ` were elaborated as function-valued fields; cause: Lean's grouped-field elaboration with later dependent references; rule: put each dependent field on its own line; example: `CriticalPath.a`, `QuotientDihedralProduct.p`.

## Resume (read this first — the recovery capsule)

- Current route: `R1-section-5-7-statements`
- Active route step: independent review and source-fidelity audit
- Working node: `lemma_seven_eight`
- Current blocker: theorem bodies remain statement-only `sorry` placeholders, as in the existing statement-translation modules; quotient/product notation in (7.8) is represented by the explicit `QuotientDihedralProduct` witness interface.
- Next action: have an independent reviewer check each source-shaped statement, then run targeted and full builds and report the interface choices to `/root`.
- Routes to avoid: weakening any numbered result to `True`; omitting Section 7 standing assumptions; using an unqualified quotient type for (7.8) without a kernel/image witness.
- Candidate next subnodes: source review; wrapper import integration; axiom/sorry inventory.

## Progress

- initiated: (2026-09-01T17:04:09Z) Added and compiled shared definitions for Sections 5–7, including `HypothesisOne`, `HypothesisTwo`, local-family predicates, graph context, critical paths, and quotient-product witness data.
- validated: (2026-09-01T17:04:09Z) Added one public result file for each of 5.1–5.4, 6.1–6.4, and 7.1–7.8; each file elaborates successfully with a statement-only proof placeholder.
- validated: (2026-09-01T17:04:09Z) Added `SectionFive`, `SectionSix`, `SectionSeven`, and `SectionFiveToSeven` wrappers; `lake build Stellmacher.SectionFiveToSeven` succeeds.
- observed: (2026-09-01T17:16:40Z) Audited the graph action convention and aligned `CosetGraphContext.act_coset₁/₂` with right multiplication (`coset (h * g)`); added explicit Section 6 aliases and the quotient-map/image witness used by (7.8).
- validated: (2026-09-01T17:24:55Z) Rebuilt the top-level compatibility wrappers `Stellmacher.SectionFive`, `SectionSix`, and `SectionSeven`; all three targeted builds succeed with only pre-existing/statement-placeholder warnings.
- observed: (2026-09-01T17:32:41Z) Per-result second-pass audit found no omitted numbered clause; Section 7 clauses are grouped into conclusion structures while preserving each source implication and quantifier.
- corrected: (2026-09-01T18:17:13Z) PDF audit fixed the reversed non-containment signs in (6.1) and (6.2), switched (5.1)(c₃) to `\mathcal P^*`, corrected the non-containment conclusion in (7.7)(c), and replaced the local `E` notation by the true `O²` residual helper.
- source-check: (2026-09-01T18:42:52Z) Rechecked journal p. 31: (6.4) is pointwise — `P₂ ≠ ⟨C_{P₂}(w),S⟩` for every eligible `w`; the temporary global-family helper was removed and `sectionSixCentralizerJoin` now mirrors the displayed subgroup.
- corrected: (2026-09-01T19:29:21Z) Aligned the shared Section 6 notation `L_i = ⟨B^{P_i}⟩` with `conjugateClosure`, and recorded the normalized edge-stabilizer condition in `CriticalPath` (`{G_a,G_{a+1}}={P₁,P₂}`).
- corrected: (2026-09-01T19:39:34Z) Expanded (7.1)(c)'s “i.e.” clause in `LemmaSevenOneConclusion` to state both vertex-stabilizer conjugacy and edge-stabilizer conjugacy, not only the distinguished edge witness.
- source-check: (2026-09-01T18:17:13Z) Direct scan of journal p. 35 confirms (7.6)(b) is `E_a ≤ ⟨O₂(E_{a+1})^{G_a}⟩` (conjugate closure) and (7.6)(d) is `⟨C_{G_{a+1}}(Z_a),G_a∩G_{a+1}⟩ ≠ G_{a+1}`; the current `conjugateClosure` and centralizer-intersection forms are faithful and were retained.

## Proof Route

- Route id: `R1-section-5-7-statements` (active)
- Sketch: audit the PDF/TeX statements; expose reusable local-group and graph notation in `Defs`; encode each numbered result in its own public module; use explicit subgroup maps for ambient Sylow/core inclusions; use a kernel/image witness for the barred product in 7.8; validate all modules and wrappers.
- Main risk: OCR ambiguity in `O²`, dihedral order parameters, and graph barred notation.

Steps:

- `S5`: encode Hypotheses 1–2 and results 5.1–5.4. Direct consumers: `Result5_1`–`Result5_4`. Helpers: `HypothesisOne`, `FiveOneConditions`, `HypothesisTwo`.
- `S6`: encode local cores, action-critical subgroup, and results 6.1–6.4. Direct consumers: `Result6_1`–`Result6_4`. Helpers: `twoCoreIn`, `twoResidualIn`, `actionCriticalSubgroup`.
- `S7`: encode coset graph, critical path, and results 7.1–7.8. Direct consumers: `Result7_1`–`Result7_8`. Helpers: `CosetGraphContext`, `SectionSevenHypotheses`, `QuotientDihedralProduct`.

## Subnodes

- `lemma_five_one` — done. Source result 5.1 and alternatives (a)–(c₃). Dependencies: `HypothesisOne`, `FiveOneConditions`.
- `lemma_five_two` — done. Source result 5.2. Dependencies: `baumannIn`, `PStarFamily`, `SubnormalIn`.
- `lemma_five_three` — done. Source result 5.3. Dependencies: `HypothesisTwo`.
- `lemma_five_four` — done. Source result 5.4. Dependencies: `HypothesisTwo`, `IsMaximalTwoLocalContaining`.
- `lemma_six_one` — done. Source result 6.1. Dependencies: `HypothesisTwo`, `twoCoreIn`.
- `lemma_six_two` — done. Source result 6.2. Dependencies: `action` commutator, `thompsonSubgroup`.
- `lemma_six_three` — done. Source result 6.3. Dependencies: quotient groups and `DihedralGroup`.
- `lemma_six_four` — done. Source result 6.4. Dependencies: `actionCriticalSubgroup`, centralizers.
- `lemma_seven_one` — done. Source result 7.1. Dependencies: `CosetGraphContext`.
- `lemma_seven_two` — done. Source result 7.2. Dependencies: `actionKernel`.
- `lemma_seven_three` — done. Source result 7.3. Dependencies: `sylowTwoAmbient`, `omegaOneCenter`.
- `lemma_seven_four` — done. Source result 7.4. Dependencies: `CriticalPath`, quadratic commutators.
- `lemma_seven_five` — done. Source result 7.5. Dependencies: `CriticalPath`.
- `lemma_seven_six` — done. Source result 7.6. Dependencies: normality and neighbor-core predicates.
- `lemma_seven_seven` — done. Source result 7.7. Dependencies: subnormality and characteristic-2 predicate.
- `lemma_seven_eight` — done. Source result 7.8. Dependencies: `QuotientDihedralProduct`, `frattiniAmbient`.

## Route Ledger

- `R1-section-5-7-statements` — active. Uses: all listed subnodes. Result: modules compile; independent statement review pending. Node disposition: keep all. Decision/Lesson: represent the barred dihedral product by a quotient-map kernel/image witness so no unjustified normality instance is assumed. Evidence: `lake build Stellmacher.SectionFiveToSeven` succeeds.
- `R1-section-5-7-statements` — review correction (2026-09-01T19:29:21Z): direct page scans overruled two reviewer readings: (6.4) explicitly says “for every `w`” (pointwise), while (7.6)(b) displays the conjugate-generated subgroup `⟨O₂(E_{a+1})^{G_a}⟩` and (d) displays `C_{G_{a+1}}(Z_a)`; the Lean forms follow the scan.

## Validation

- Last check: targeted build for `Stellmacher.SectionFiveToSeven` (including SectionFive/SectionSix/SectionSeven wrappers) succeeded at 2026-09-01T19:54:16Z; only expected `sorry` warnings remain.
- Final validation: pending independent review, axiom checks, and authoritative full build.

## Source Notes

- Audit status: audited against the PDF scan and extracted text.
- Findings:
  - (source-fidelity) Section 6.3 scan reads `Pᵢ/Qᵢ ≅ D_{2·3^{nᵢ}}`; Lean uses `DihedralGroup (3 ^ nᵢ)`, whose Mathlib parameter is the half-order.
  - (source-fidelity) Journal p. 30 reads `B \nleq Q₂` in (6.1) and `J(S) \nleq Qᵢ` in (6.2); the Lean conclusions use non-containment, not containment.
  - (source-fidelity) Journal p. 31 reads the pointwise inequality `P₂ ≠ ⟨C_{P₂}(w),S⟩` in (6.4) for every `w ∈ C_V(J(V,S)) \ Ω₁(Z(S))`; `sectionSixCentralizerJoin` makes the displayed subgroup explicit.
  - (interface) The scan writes `J(V,\bar S)` with `\bar S` the image in `P₁/C_{P₁}(V)`; the current quotient-free `actionCriticalSubgroup V S` records the same fixed-point/cardinality criterion on the ambient lift, with the centralizer kernel absorbed into `C_V(-)`.
  - (source-fidelity) Journal p. 36 reads `E_{α'} \nleq C` in (7.7)(c); the Lean conclusion preserves this non-containment.
  - (source-fidelity) Section 7.8(b) scan reads a direct product `\bar L ≅ D_{2p^n} × \bar A₀`; the Lean `QuotientDihedralProduct` witness records this as a quotient image and its `A₀` image.
  - (source-fidelity) Section 5.4 alternative is `H₀ \nleq M` in the PDF; the Lean statement uses `¬ H₀ ≤ M`.
