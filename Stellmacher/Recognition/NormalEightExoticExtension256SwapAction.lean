module

public import Stellmacher.Recognition.NormalEightExoticExtension256ActionSetup
public import Theory.SpecificGroups.ExoticTwoGroup.ActionCoordinates

/-!
# The coordinate obstruction to a prescribed swap

The inner-action membership assertions do not determine coordinates in
which the outer action contains the specified swap. Indeed, whenever
these assertions hold, there are coordinates satisfying them in which
swap is absent. Cycling the three involutions preserves both inner
membership assertions, but two cyclically related swaps would generate
an element of order three in an image of order sixteen.

Consequently a swap-existence argument must also choose the orientation
of the omega four, or allow a further coordinate change. This module
does not assert the remaining structural swap-existence step.

Source: MacWilliams, Trans. AMS 150 (1970), §4(xiv), p.393 (the choice of
Sylow subgroup of Aut(C₄ × C₄) by a basis change), cited in
Janko–Thompson 1.4(c), p.386.
-/

open Subgroup C4SquareExtension ExoticTwoGroup.ActionModel

namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- Changing coordinates transports the entire conjugation action. -/
public theorem modelAction_trans {P : Type*} [Group P] (D : Subgroup P) [D.Normal]
    (e : D ≃* Model) (c : MulAut Model) :
    modelAction D (e.trans c) = (MulAut.congr c).toMonoidHom.comp (modelAction D e) := by
  rfl

/-- Inner normalization alone always admits coordinates in which swap is absent.
The group, base and elementary subgroup are unchanged by this choice. -/
public theorem exists_inner_coordinates_without_swap
    {P : Type*} [Group P] [Finite P]
    (D B : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hcard : Nat.card P = 256)
    (e : D ≃* Model)
    (h₁ : inner₁ ∈ ((modelAction D e).comp B.subtype).range)
    (h₂ : inner₂ ∈ ((modelAction D e).comp B.subtype).range) :
    ∃ e' : D ≃* Model,
      inner₁ ∈ ((modelAction D e').comp B.subtype).range ∧
      inner₂ ∈ ((modelAction D e').comp B.subtype).range ∧
      swap ∉ (modelAction D e').range := by
  classical
  by_cases ht : swap ∈ (modelAction D e).range
  · refine ⟨e.trans coordinateCycle, ?_, ?_, ?_⟩
    · rw [modelAction_trans, MonoidHom.comp_assoc, MonoidHom.range_comp]
      exact (inner_mem_coordinateCycle _ h₁ h₂).1
    · rw [modelAction_trans, MonoidHom.comp_assoc, MonoidHom.range_comp]
      exact (inner_mem_coordinateCycle _ h₁ h₂).2
    · rw [modelAction_trans, MonoidHom.range_comp]
      exact swap_not_mem_coordinateCycle _ (card_modelAction_range D hDC e hcard) ht
  · exact ⟨e, h₁, h₂, ht⟩

end Stellmacher.Recognition.NormalEightExoticExtension256
