module

public import GorensteinWalter.BrauerSuzukiWallNonFour
public import GorensteinWalter.BrauerSuzukiWallCardFour

/-!
# Brauer--Suzuki--Wall

All possible cardinalities of the distinguished abelian subgroup `K` have
now been discharged.
-/

namespace GorensteinWalter

universe u

/-- The complete Brauer--Suzuki--Wall endpoint used by Gorenstein--Walter
Lemma 2.2. -/
public theorem BrauerSuzukiWallHypotheses.isDGroup
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    IsDGroup G := by
  by_cases hk : Nat.card h.K = 4
  · exact h.isDGroup_of_card_K_eq_four hk
  · exact h.isDGroup_of_card_K_ne_four hk

end GorensteinWalter
