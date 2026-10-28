module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCover

/-!
# Reducing the thirty-relator order bound to its middle subgroup

The unconditional 48-coset cover proved in `AtlasBoundThirtyCover` reduces the
order bound to finiteness and the bound 31,250 for the actual subgroup `⟨x,y⁴⟩`.
This module retains that premise explicitly until a separate subgroup proof
supplies it. It does not assert an unconditional order bound.

Source: the literal presentation in `AtlasBoundThirtyPresentation` and the
subgroup chain documented in `AtlasBoundThirtySource/README.md`.
-/

namespace G2Five.AtlasPresentation

/-- The middle-subgroup bound and the certified cover give the required order bound. -/
public theorem boundThirtyPresentation_finite_card_le_of_middle
    (hmiddle : Finite boundThirtyMiddle ∧ Nat.card boundThirtyMiddle ≤ 31250) :
    Finite BoundThirtyPresentation ∧ Nat.card BoundThirtyPresentation ≤ 1500000 := by
  let : Finite boundThirtyMiddle := hmiddle.1
  have h := boundThirtyMiddleCover.finite_card_le
    (PresentedGroup.closure_range_of (Set.range boundThirtyRelator))
  refine ⟨h.1, h.2.trans ?_⟩
  simpa using Nat.mul_le_mul_right 48 hmiddle.2

end G2Five.AtlasPresentation
