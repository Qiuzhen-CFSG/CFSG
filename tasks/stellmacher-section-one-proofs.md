# stellmacher-section-one-proofs — sorry-free Section One

Status: in progress
Target declarations: `Stellmacher.SectionOne.lemma_one_one` through `lemma_one_seven`
Lean modules: `Stellmacher.SectionOne.LemmaOneOne` through `Stellmacher.SectionOne.LemmaOneSeven`, `Stellmacher.SectionOne`, `Stellmacher.SectionsOneToFour`
Source: `refs/latex/stellmacher-n-group.tex`:L233-L544

## Task

Prove all seven numbered results in Stellmacher Section One, following the
source proof and leaving no `sorry`, `admit`, `axiom`, or `opaque` in the
Section One module cluster.

## Imports

- `Stellmacher.SectionOne.Defs` and `Stellmacher.SectionsOneToFourDefs` — pinned statements and shared notation.
- Existing local and Mathlib finite-group/action APIs located by source-shaped search.

## Bridges

- (none; every extracted helper must be proved before use)

## Lessons

context: `Stellmacher.SectionOne.LemmaOneTwo`
symptom: importing `Theory.GroupAction.Lemmas` after `Stellmacher.SectionOne.Defs` reports that the environment already contains `commutatorAction_map_subtype_eq_commutatorAction₂`; `FeitThompson.GroupAction.Lemmas` declares the same global interface, so low-level generic helpers that must coexist with Section One should import the shared `Theory.GroupAction.Defs` plus the precise Mathlib modules instead of either colliding lemma bundle.
example: `commutatorAction_map_subtype_eq_commutatorAction₂`

## Resume (read this first — the recovery capsule)

- Current route: R1-source-proof-decomposition (active)
- Active route step: prove (1.2) by formalizing the source's normalization and three-subgroup argument, using the now-proved (1.1).
- Working node: `lemma_one_two`
- Current blocker: none; (1.1) is proved and axiom-checked.
- Next action: pin the exact subgroup-action form of the source proof for (1.2), locate the three-subgroup interface, and probe the needed action-closure transports.
- Routes to avoid: treating the paper's "well known" or classification assertions as unproved interfaces; reusing the exploratory untracked scratch files as task state; changing a pinned statement to make it provable.
- Candidate next subnodes: theorem-local transport lemmas from subgroup actions to ambient centralizers/commutators; source-core helpers for (1.2)–(1.7) as the proof audit identifies them.

## Progress

- initiated: (2026-09-02T04:51:06Z) Expanded the requested scope to all seven numbered Section One modules. The targeted baseline `lake build Stellmacher.SectionOne.LemmaOneOne` succeeds with the expected placeholder warning and the two pre-existing `FinalTheorem` placeholders.
- observed: (2026-09-02T05:08:19Z) All four clauses of (1.1) elaborate in `Scratch/stellmacher-section-one/ProbeOneOne.lean`: (a) transports the solvable coprime-action splitting; (b) and (c) transport fixed-point generation to ambient centralizers; (d) derives commutativity and exponent two from the quadratic commutator identity.
- validated: (2026-09-02T05:11:56Z) `lemma_one_one_part_a` through `lemma_one_one_part_d` and `lemma_one_one` now build in `Stellmacher.SectionOne.LemmaOneOne`; `#print axioms lemma_one_one` reports exactly `[propext, Classical.choice, Quot.sound]`. Remaining `sorry` messages in the build log are the two pre-existing `Stellmacher.FinalTheorem` placeholders.
- validated: (2026-09-02T05:17:04Z) Added and built `Theory.ThreeSubgroups`, proving both the normal-target relative three-subgroups lemma and its normalized-target wrapper via restriction to the generated subgroup and quotienting by the target.
- validated: (2026-09-02T05:20:29Z) Added and built `Theory.GroupAction.CommutatorSemidirect`; action commutators of a subgroup now transport exactly to subgroup commutators in the ambient semidirect product.

## Proof Route

- Route id: R1-source-proof-decomposition
- Sketch: Prove (1.1) by transporting the repository's coprime-action fixed-point and commutator theorems from subgroup actions back to ambient subgroups. Follow the LaTeX dependency order: use (1.1) in the three-subgroup proof of (1.2), formalize the induction/classification core of (1.3), then derive the direct-product statement (1.4). Prove the rational identity (1.5a) algebraically and its remaining clauses from the source's index-two induction. Use (1.4)–(1.5) to formalize the four-way induction of (1.6), then assemble (1.7) from (1.5e) and (1.6d). Extract only the smallest source-core helpers, prove each before its consumer, and keep public visibility only where a later numbered result needs it.
- Main risk: the source invokes substantial finite-group classification facts (`GL₄(2)`, `SL₃(4)`, and the `P × Q`/three-subgroup lemmas) whose exact local APIs may be absent; each such jump must be isolated and proved or routed through an existing proved theorem.

## Subnodes

- `lemma_one_one_part_a` — done. Dependencies: solvable coprime-action splitting and subgroup-action transport.
- `lemma_one_one_part_b` — done. Dependencies: noncyclic abelian `p`-group fixed-point generation and ambient-centralizer transport.
- `lemma_one_one_part_c` — done. Dependencies: cyclic-quotient fixed-point generation, elementary-abelian quotient cardinality, and ambient-centralizer transport.
- `lemma_one_one_part_d` — done. Dependencies: faithfulness and the quadratic commutator identity.
- `lemma_one_one` — done. Dependencies: the four clause helpers above.
- `Subgroup.commutator_commutator_le_of_rotate` — done in `Theory.ThreeSubgroups`. Dependencies: the ordinary three-subgroups lemma applied in a quotient by a normal target subgroup.
- `Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer` — done in `Theory.ThreeSubgroups`. Dependencies: restriction to the subgroup generated by the three inputs and the normal-target relative lemma; this is the source-shaped `≤ C_V(H)` interface needed by (1.2).
- `commutatorSubgroup_mono` — done in `Theory.GroupAction.CommutatorSemidirect`. Dependencies: monotonicity of subgroup closure.
- `commutatorSubgroup_map_semidirect_inl_eq_commutator` — done in `Theory.GroupAction.CommutatorSemidirect`. Dependencies: the explicit semidirect-product commutator formula; needed to apply the relative three-subgroups lemma to action commutators in (1.2).
- `commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot` — planned in `Theory.GroupAction.Quadratic`. Dependencies: the generator description of the iterated action commutator; this is the explicit fixed-point content of a quadratic action.
- `lemma_one_two` — planned. Dependencies: (1.1), three-subgroup/action-normalization helpers.
- `lemma_one_three` — planned. Dependencies: induction on `|F||V|` and the source's small linear-group classification steps.
- `lemma_one_four` — planned. Dependencies: (1.3) and `GL₄(2)` direct-product consequence.
- `lemma_one_five` — planned. Dependencies: finite-cardinality identity, (1.1), and index-two induction.
- `lemma_one_six` — planned. Dependencies: (1.4), (1.5), and source induction/classification.
- `lemma_one_seven` — planned. Dependencies: (1.5e), (1.6d), normal-closure/direct-product assembly.

## Route Ledger

- `R1-source-proof-decomposition` — active. Uses: all listed nodes in source order. Result: (1.1) proved; (1.2) is active. Node disposition: keep. Decision/Lesson: use explicit conjugation-action transports when inherited subgroup actions are definitionally unequal. Evidence: `refs/latex/stellmacher-n-group.tex`:L233-L544 and the successful targeted (1.1) build.

## Validation

- Last check: `lake build Stellmacher.SectionOne.LemmaOneOne` succeeded at 2026-09-02T05:11:56Z; the theorem is sorry-free and has only the permitted axioms.
- Final validation: pending all seven owner modules, dependents, axiom checks, `lake build Stellmacher`, and full `lake build`.
