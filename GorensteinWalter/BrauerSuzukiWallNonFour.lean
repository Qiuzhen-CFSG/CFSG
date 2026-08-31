module

public import GorensteinWalter.BrauerSuzukiWallCardCases
public import GorensteinWalter.BrauerSuzukiWallCardTwo
public import GorensteinWalter.BrauerSuzukiWallOrderCases
public import GorensteinWalter.BrauerSuzukiWallStructure
public import GorensteinWalter.BrauerSuzukiWallZassenhaus

/-!
# The non-order-four Brauer--Suzuki--Wall branches

The order-two source branch and the high-cardinality character/structure
branch are complete.  This module packages them behind the single remaining
exception `|K| = 4`.
-/

namespace GorensteinWalter

universe u

/-- A Brauer--Suzuki--Wall configuration is a `D`-group unless its
distinguished abelian subgroup has order four. -/
public theorem BrauerSuzukiWallHypotheses.isDGroup_of_card_K_ne_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K ≠ 4) :
    IsDGroup G := by
  rcases h.card_K_cases with hkTwo | hkFour | hkHigh
  · exact h.isDGroup_of_card_K_eq_two hkTwo
  · exact False.elim (hk hkFour)
  · exact (brauerSuzukiWallConclusion_nonempty_of_order_cases
      h hkHigh (h.order_cases hkHigh)).some.isDGroup

end GorensteinWalter
