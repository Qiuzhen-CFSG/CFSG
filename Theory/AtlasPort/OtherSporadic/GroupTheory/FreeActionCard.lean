/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/FreeActionCard.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# FreeActionCard

A free finite action with degree equal to the group order is regular.
Evaluation is injective and hence bijective by equality of cardinalities.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/FreeActionCard.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory

theorem unique_smul_of_free_card {G X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    (hc : Nat.card G = Nat.card X) (hf : ∀ x : X, ∀ g : G, g • x = x → g = 1)
    (x y : X) : ∃! g : G, g • x = y := by
  have hi : Function.Injective (fun g : G => g • x) := by
    intro g h he
    change g • x = h • x at he
    have hh : (h⁻¹*g) • x = x := by rw [mul_smul,he,inv_smul_smul]
    exact (inv_mul_eq_one.mp (hf x (h⁻¹*g) hh)).symm
  have hb : Function.Bijective (fun g : G => g • x) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hi,hc⟩
  obtain ⟨g,hg⟩ := hb.2 y
  exact ⟨g,hg,fun h hh => hi (hh.trans hg.symm)⟩

end Atlas.GroupTheory
