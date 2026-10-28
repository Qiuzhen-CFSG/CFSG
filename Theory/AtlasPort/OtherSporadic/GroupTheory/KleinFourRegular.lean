/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/KleinFourRegular.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# KleinFourRegular

The standard Klein four subgroup acts regularly on a four-element set.
Double transpositions have no fixed points, and equal cardinalities give transitivity.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/KleinFourRegular.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem kleinFour_fixed_eq_one (hc : Nat.card α = 4)
    (g : alternatingGroup.kleinFour α) (x : α) (hx : g.val.val x = x) : g = 1 := by
  have hg := g.prop
  rw [← SetLike.mem_coe,alternatingGroup.coe_kleinFour_of_card_eq_four hc] at hg
  rcases hg with hg | hg
  · exact Subtype.ext hg
  have hs : g.val.val.support.card = Fintype.card α := by
    rw [← Equiv.Perm.sum_cycleType,hg,← Nat.card_eq_fintype_card,hc]
    rfl
  have ht : g.val.val.support = Finset.univ := Finset.eq_univ_of_card _ hs
  have hn := Equiv.Perm.notMem_support.mpr hx
  rw [ht] at hn
  exact False.elim (hn (Finset.mem_univ x))

theorem kleinFour_regular (hc : Nat.card α = 4) (x y : α) :
    ∃! g : alternatingGroup.kleinFour α, g.val.val x = y := by
  classical
  let := Fintype.ofFinite (alternatingGroup.kleinFour α)
  have hinj : Function.Injective (fun g : alternatingGroup.kleinFour α => g.val.val x) := by
    intro g h he
    change g.val.val x = h.val.val x at he
    have hh : (h⁻¹ * g).val.val x = x := by
      change h.val.val.symm (g.val.val x) = x
      rw [he,Equiv.symm_apply_apply]
    exact (inv_mul_eq_one.mp (kleinFour_fixed_eq_one hc _ x hh)).symm
  have hcard : Fintype.card (alternatingGroup.kleinFour α) = Fintype.card α := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
      alternatingGroup.kleinFour_card_of_card_eq_four hc,hc]
  have hs := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj,hcard⟩
  obtain ⟨g,hg⟩ := hs.2 y
  exact ⟨g,hg,fun h hh => hinj (hh.trans hg.symm)⟩

end Atlas.GroupTheory
