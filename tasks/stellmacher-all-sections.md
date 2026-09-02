# stellmacher-all-sections — numbered-result translation (Sections 1–11)

Status: complete
Target declarations: every numbered result 1.1–10.1 in the paper, plus the two main theorems
Lean modules: `Stellmacher/SectionOne` through `Stellmacher/SectionTen`, with one result per Lean file
Sources: `refs/files/stellmacher-n-group.pdf` (journal pp. 14–66), `refs/latex/stellmacher-n-group.tex` where available

## Task

Translate all numbered lemmas/propositions/theorems faithfully, retaining every hypothesis and conclusion.  The PDF is authoritative when the partial LaTeX transcription drops or corrupts notation.

## Inventory

| Section | Numbered results | State | Owner |
|---|---:|---|---|
| 1 | 1.1–1.7 | translated (reviewed) | sections_1_4 |
| 2 | 2.1–2.5 | translated (reviewed) | sections_1_4 |
| 3 | 3.1–3.9 | translated (reviewed) | sections_1_4 |
| 4 | 4.1–4.7 | translated (reviewed) | sections_1_4 |
| 5 | 5.1–5.4 | translated (review pending) | sections_5_7 |
| 6 | 6.1–6.4 | translated (review pending) | sections_5_7 |
| 7 | 7.1–7.8 | translated (review pending) | sections_5_7 |
| 8 | 8.1–8.6 | transcribed to LaTeX | root |
| 9 | 9.1–9.10 | transcribed to LaTeX | root |
| 10 | 10.1 | transcribed to LaTeX | root |
| 11 | no separately numbered result; theorem assembly only | transcribed to LaTeX | root |

## Imports

- `Stellmacher.FinalTheorem` and `Stellmacher.SectionOne` — existing introductory interfaces
- per-section `Defs` modules — shared notation and hypotheses for the numbered statements

## Bridges

- (none)

## Resume

- Current route: R1-inventory-and-section-translation
- Active route step: section 8–10 interface design
- Working node: root-owned sections 8–10
- Current blocker: the PDF continues beyond the supplied LaTeX transcription; OCR notation must be checked against page images before pinning statements.
- Next action: inspect the section-7 interfaces as they land, then add one Lean file for each of 8.1–10.1 and wire public wrappers.
- Routes to avoid: silently weakening statements to `True` or dropping source hypotheses; treating “type X” as ambient isomorphism when the paper defines a local amalgam type.

## Progress


- initiated: (2026-09-01T16:20:46Z) Full PDF inventory found 61 numbered results: 1.1–1.7, 2.1–2.5, 3.1–3.9, 4.1–4.7, 5.1–5.4, 6.1–6.4, 7.1–7.8, 8.1–8.6, 9.1–9.10, and 10.1; Section 11 contains only final theorem assembly.
- initiated: (2026-09-01T16:20:46Z) Parallel owners assigned: Sections 1–4, Sections 5–7, and root Sections 8–11; an independent reviewer is running for the first owner.
- validated: (2026-09-01T17:26:45Z) Added statement-level files for (2.4)–(2.5), (3.1)–(3.9), and (4.1)–(4.7), plus `SectionsOneToFour` wrapper; each targeted module builds with only expected `sorry` warnings.
- repaired: (2026-09-01T17:26:45Z) Corrected `PStarSet` to require a maximal `L` and relative subnormality of the ambient `O²(E)` in `L`; added explicit quotient, orbit, irreducibility, and Sylow interfaces in `SectionsOneToFourDefs`.
- validated: (2026-09-01T17:45:58Z) Rebuilt `Stellmacher.SectionsOneToFour` after the center, Thompson-subgroup, and irreducibility corrections; targeted build passed with only expected `sorry` and deprecation warnings.
- refactored: (2026-09-01T17:55:37Z) Split introductory results (1.1)–(1.3) into `SectionOne/LemmaOneOne.lean`, `LemmaOneTwo.lean`, and `LemmaOneThree.lean`; retained `SectionOne.lean` as a public wrapper and added `SectionOne/Defs.lean` for shared definitions. `Stellmacher.SectionOne` and `Stellmacher.SectionsOneToFour` rebuild successfully.
- repaired: (2026-09-01T18:11:57Z) Made the `V^τ` notation in (2.5) explicit via an in-Sylow representative `V_S : Subgroup S` with ambient equality `V_S.map S.subtype = vSubgroup S`; this avoids silently translating `V ∩ S` when the source's ambient `V` is not definitionally a subgroup of `S`. Targeted Sections 2–4 build passes.
- repaired: (2026-09-01T18:38:12Z) Corrected (2.3) to use the source's unbarred `B = C_S(Ω₁(Z(J(S))))` and `L = ⟨B^G⟩`; removed the unrelated quotient witnesses from that statement. `Stellmacher.SectionsOneToFour` rebuilds successfully.
- repaired: (2026-09-01T18:53:15Z) Separated the two Section 1 families: `oneA` now models `𝒜(V,S)` (`m(A) ≤ 1`) and `oneAmax` models the later `𝒜(S)` with centralizer conditions. Lemma (1.5) uses `oneAmax`, while (1.7)'s `J(V,S)` uses `oneA`; targeted Sections 1–4 build passes.
- repaired: (2026-09-01T19:01:02Z) Corrected (1.6)(d): the direct-product factors are the `E_i ≅ SL₂(2)` themselves, with each derived subgroup `E_i'` required to lie in `Ω(W)`; the previous formulation incorrectly made the odd derived subgroups generate `WS`.
- repaired: (2026-09-01T19:16:24Z) Removed an unsupported elementary-abelian conjunct from `oneAmax`: the paper's `𝒜(S)` definition lists only `m(A) ≤ m(S)` and the two centralizer equalities (with `A ≤ S` implicit), unlike `𝒜(V,S)`.
- repaired: (2026-09-01T19:42:16Z) Added `elementaryAbelianMaxSubgroups`/`elementaryAbelianMaxJ` for the Section 2/4 definition of `J(S)` (elementary abelian, maximal order), replacing Mathlib's all-abelian `thompsonSubgroup` in (2.2), (2.3), (3.9), (4), and Sections 5–7 interfaces. Corrected (1.6)(b) to use `[V*,S,S]` via `vStarAction₂`.
- repaired: (2026-09-01T19:46:14Z) Reworked (2.5) to avoid adding `V≤S` as an unlisted hypothesis: `vSubgroupInSylow` and `automorphismTranslateV` model the canonical in-Sylow representative and its automorphism images internally, while the theorem concludes that their generated subgroup is normal in `O₂(G)`.
- corrected: (2026-09-02T05:17:30Z) A higher-resolution PDF/XML audit and the (2.1) sanity check show (2.2)'s displayed `\bar E=[O_{2'}(\bar G),\overline{J(S)}]\overline{J(S)}`; `LemmaTwoTwoConclusion` uses `pPrimeCore 2 barG`.  Using `pCore 2` would collapse `\bar E` to `\bar J` because (2.1) gives `O₂(\bar G)=1`, making the SL₂-factor conclusion vacuous.
- validated: (2026-09-01T22:05:08Z) Independent reviewer audited the PDF pages for every numbered result 1.1–4.7; no additional statement drift was found. `lake build Stellmacher.SectionsOneToFour` passes with only expected `sorry` and deprecation warnings. The Section 3.1–3.2 `O^{2'}`/`twoPrimeResidual` distinction and Section 4 product/containment clauses were explicitly rechecked.
- completed: (2026-09-02T06:38:54Z) Extended `refs/latex/stellmacher-n-group.tex` through Sections 6–11, including all numbered results 8.1–10.1, theorem assembly, acknowledgments, and references. Corrected scan-sensitive `O_{2'}`, `\Omega_8^+(3)`, and the full (8.6)/(10.1) alternatives. Rendered the completed LaTeX and visually checked cropped section-boundary and final pages.

## Proof Route

- Route id: R1-inventory-and-section-translation
- Sketch: audit the PDF statement inventory; define reusable per-section notation without encoding conclusions into assumptions; place each numbered result in its own public Lean file; import those files through section wrappers and the top-level wrapper; run targeted builds and independent statement reviews.
- Main risk: source notation (especially quotient models, graph distances, and centralizer/core symbols) is damaged by OCR and must not be mistaken for a changed hypothesis.

## Validation

- Last check: existing `lake build Stellmacher` baseline passed before this milestone.
- Final validation: pending all 61 result files, wrappers, source-fidelity audit, and targeted/full builds.

## Source Notes

- Audit status: Sections 1–4 independently reviewed; Sections 5–10 pending or under review.
- Known global findings are recorded in `tasks/index.md` (odd-core corrections in Section 1 and Theorem 2 clause (e)).
