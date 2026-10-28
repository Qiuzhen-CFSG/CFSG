/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/FiniteSymmetricDifferenceCard.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff

/-!
# FiniteSymmetricDifferenceCard

The cardinality of a symmetric difference is the sum of the two cardinalities
minus twice the intersection size. The proof splits into disjoint differences
and applies the finite inclusion-exclusion identities.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/FiniteSymmetricDifferenceCard.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and explicit public imports.
-/

public section

namespace Atlas.Combinatorics
open scoped symmDiff

/-- The inclusion-exclusion formula for a finite symmetric difference. -/
theorem card_symmDiff_eq {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∆ B).card=A.card+B.card-2*(A ∩ B).card := by
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def,Finset.card_union_of_disjoint hd]
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  omega

end Atlas.Combinatorics
