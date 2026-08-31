module

public import GorensteinWalter.BrauerSuzukiWallCardTwoTop
public import GorensteinWalter.BrauerSuzukiWallCardTwoProper

/-!
# The complete order-two branch

The normalizer of the involution centralizer is either the whole group,
giving the `A₄ ≃ PSL₂(3)` case, or proper, giving the `A₅` case.
-/

namespace GorensteinWalter

universe u

/-- Every Brauer--Suzuki--Wall configuration with `|K| = 2` is a `D`-group. -/
public theorem BrauerSuzukiWallHypotheses.isDGroup_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) :
    IsDGroup G := by
  by_cases hN : Subgroup.normalizer (h.H : Set G) = ⊤
  · exact h.isDGroup_of_card_K_eq_two_of_normalizer_eq_top hk hN
  · exact h.isDGroup_of_card_K_eq_two_of_normalizer_ne_top hk hN

end GorensteinWalter
