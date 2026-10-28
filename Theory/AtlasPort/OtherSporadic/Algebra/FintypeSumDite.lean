/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/FintypeSumDite.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# FintypeSumDite

A finite sum with a dependent conditional splits into sums over the two
complementary subtypes. The proof transports the filtered sums along subtype
equivalences.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/FintypeSumDite.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and explicit public imports.
-/

public section

namespace Atlas.Algebra

/-- Additive dependent splitting over a finite type. -/
theorem fintype_sum_dite {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    {p : ι → Prop} [DecidablePred p]
    (f : ∀ i, p i → A) (g : ∀ i, ¬p i → A) :
    (∑ i, dite (p i) (f i) (g i)) =
      (∑ i : {i // p i}, f i i.property) + ∑ i : {i // ¬p i}, g i i.property := by
  simp only [Finset.sum_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).sum_comp fun i : {i // p i} => f i i.property
  · exact (Equiv.subtypeEquivRight <| by simp).sum_comp fun i : {i // ¬p i} => g i i.property

end Atlas.Algebra
