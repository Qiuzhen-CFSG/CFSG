module

public import GorensteinWalter.BrauerSuzukiWallCardTwoA5
public import GorensteinWalter.A5

/-!
# The proper-normalizer case in the order-two branch

The faithful degree-five coset action identifies the proper `|K|=2` branch
with `A₅`, so the existing alternating-group recognizer makes it a
`D`-group.
-/

namespace GorensteinWalter

universe u

/-- The proper-normalizer subcase of the `|K| = 2` branch is a `D`-group. -/
public theorem
    BrauerSuzukiWallHypotheses.isDGroup_of_card_K_eq_two_of_normalizer_ne_top
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    IsDGroup G :=
  isDGroup_of_mulEquiv_aFive
    (h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top
      hk hNne)

end GorensteinWalter
