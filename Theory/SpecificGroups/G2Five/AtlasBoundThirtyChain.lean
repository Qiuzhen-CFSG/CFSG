module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyPresentation
public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Subgroups of the thirty-relator presentation

Write `x,y` for the canonical generators. The proposed short chain uses
`H = ⟨x,y⁴⟩` and the cyclic subgroup `⟨x⟩`. The first defining relation
proves, without any finiteness assumption on the ambient group, that the
cyclic subgroup has at most ten elements.

Source: the exact words in `AtlasBoundThirtyPresentation` and the exploratory
subgroup chain documented in `AtlasBoundThirtySource/README.md`.
-/

namespace G2Five.AtlasPresentation

/-- Canonical generators of the abstract thirty-relator presentation. -/
@[expose] public def boundThirtyGenerator (b : Bool) : BoundThirtyPresentation :=
  PresentedGroup.of b

/-- The defining relations hold in their own abstract presentation. -/
public theorem boundThirty_relator_eq_one (i : Fin 30) :
    FreeGroup.lift boundThirtyGenerator (boundThirtyRelator i) = 1 := by
  have he : FreeGroup.lift boundThirtyGenerator =
      PresentedGroup.mk (Set.range boundThirtyRelator) := by
    apply FreeGroup.ext_hom
    intro b
    rfl
  rw [he]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- The first generator has exponent dividing ten. -/
public theorem boundThirty_x_pow_ten : boundThirtyGenerator false ^ 10 = 1 := by
  simpa only [boundThirtyRelator_zero, map_pow, FreeGroup.lift_apply_of] using
    boundThirty_relator_eq_one 0

/-- Generators of the middle subgroup, as ambient elements. -/
@[expose] public def boundThirtyMiddleWord (b : Bool) : BoundThirtyPresentation :=
  if b then boundThirtyGenerator true ^ 4 else boundThirtyGenerator false

/-- The subgroup `⟨x,y⁴⟩` in the abstract presentation. -/
@[expose] public def boundThirtyMiddle : Subgroup BoundThirtyPresentation :=
  Subgroup.closure (Set.range boundThirtyMiddleWord)

public theorem boundThirtyMiddleWord_mem (b : Bool) :
    boundThirtyMiddleWord b ∈ boundThirtyMiddle :=
  Subgroup.subset_closure ⟨b, rfl⟩

/-- The cyclic subgroup at the bottom of the direct enumeration. -/
@[expose] public def boundThirtyCyclic : Subgroup BoundThirtyPresentation :=
  Subgroup.zpowers (boundThirtyGenerator false)

public theorem boundThirtyCyclic_le_middle : boundThirtyCyclic ≤ boundThirtyMiddle :=
  Subgroup.zpowers_le.mpr (boundThirtyMiddleWord_mem false)

/-- This cyclic bound uses only the first of the thirty relations. -/
public theorem finite_card_boundThirtyCyclic_le :
    Finite boundThirtyCyclic ∧ Nat.card boundThirtyCyclic ≤ 10 := by
  have hx : IsOfFinOrder (boundThirtyGenerator false) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨10, by decide, boundThirty_x_pow_ten⟩
  refine ⟨hx.finite_zpowers.to_subtype, ?_⟩
  change Nat.card (Subgroup.zpowers (boundThirtyGenerator false)) ≤ 10
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) boundThirty_x_pow_ten

end G2Five.AtlasPresentation
