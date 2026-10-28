module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.PairwiseRecognition.Inputs
/-!
# Relating the commutator modules to the recognized cores

The normal elementary abelian modules `V₁`, `V₂` lie in their factors'
two-cores. Once finite recognition supplies core order four, the source
modules are exactly these cores. This lets the final assembly reuse the
source disjointness of sibling modules without assuming core disjointness.

Source: Aschbacher–Smith, 15.4.12 and the paragraph following 15.4.23,
printed pp.1160 and 1165. Equality follows from containment and equal order.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type*} [Group G] {d : Geometry G} (h : LocalData d)
include h

theorem LocalData.V₁_le_twoCore (i : Bool) : d.V₁ i ≤ (d.X i).pCoreIn 2 := by
  let := h.V₁_elementary i
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) (h.V₁_le i)
    ((show d.X i ≤ d.G₁ i from le_sup_left).trans (h.V₁_normalized i))

theorem LocalData.V₂_le_twoCore (j : Bool) : d.V₂ j ≤ (d.Y j).pCoreIn 2 := by
  let := h.V₂_elementary j
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) (h.V₂_le j)
    ((show d.Y j ≤ d.G₂ j from le_sup_left).trans (h.V₂_normalized j))

theorem LocalData.V₁_eq_twoCore_of_card [Finite G] (i : Bool)
    (hc : Nat.card ((d.X i).pCoreIn 2) = 4) : d.V₁ i = (d.X i).pCoreIn 2 := by
  apply eq_of_le_of_card_ge (h.V₁_le_twoCore i)
  rw [hc, h.V₁_card]

theorem LocalData.V₂_eq_twoCore_of_card [Finite G] (j : Bool)
    (hc : Nat.card ((d.Y j).pCoreIn 2) = 4) : d.V₂ j = (d.Y j).pCoreIn 2 := by
  apply eq_of_le_of_card_ge (h.V₂_le_twoCore j)
  rw [hc, h.V₂_card]

end CFSG.Quasithin.Chapter15.Section04.Source
