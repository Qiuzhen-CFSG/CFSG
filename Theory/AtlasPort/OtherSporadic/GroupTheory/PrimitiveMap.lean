/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimitiveMap.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Maps from primitive actions

An equivariant map out of a primitive action is injective or constant.
Its fibers are blocks; a fiber containing two points must be the whole set.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimitiveMap.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with project module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

/-- An equivariant map from a primitive action is injective or constant. -/
theorem primitive_map_injective_or_constant {G H A X : Type*}
    [Group G] [Group H] [MulAction G A] [MulAction H X] [IsPreprimitive G A]
    {φ : G → H} (f : A →ₑ[φ] X) :
    Function.Injective f ∨ ∀ a b, f a = f b := by
  classical
  by_cases hi : Function.Injective f
  · exact Or.inl hi
  right
  obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hi
  have hB : IsBlock G (f ⁻¹' {f a}) := IsBlock.preimage f (IsBlock.singleton)
  rcases hB.subsingleton_or_eq_univ with hs | hu
  · exact False.elim (hne (hs (by simp) (by simpa using hab.symm)))
  · intro c d
    have hc : c ∈ f ⁻¹' {f a} := by rw [hu]; trivial
    have hd : d ∈ f ⁻¹' {f a} := by rw [hu]; trivial
    exact hc.trans hd.symm

end Atlas.GroupTheory
