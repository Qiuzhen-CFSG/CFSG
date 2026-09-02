module

public import Stellmacher.SectionThree.LemmaThreeSix

open scoped BigOperators Pointwise

namespace Stellmacher.SectionThree

universe u

/-! **Stellmacher (3.7).**  The bars are represented by the quotient of `L`
by its 2-core, and each `O²(\bar P)` on the right is the image in that
quotient of the ambient 2-residual of `P`. -/
public theorem lemma_three_seven
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (L : Subgroup G) (hL : L ∈ LSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable L) :
    ⁅fittingSubgroup (L ⧸ pCore 2 L),
        (S.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))⁆ =
      ⨆ P : {P : Subgroup G // P ∈ PStarSet L S},
        twoResidualImageInQuotient L (P : Subgroup G) := by
  sorry

end Stellmacher.SectionThree
