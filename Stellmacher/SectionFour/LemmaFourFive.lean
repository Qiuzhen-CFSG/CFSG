module

public import Stellmacher.SectionFour.LemmaFourFour

open scoped Pointwise

namespace Stellmacher.SectionFour

universe u

/-! **Stellmacher (4.5).** -/
public theorem lemma_four_five
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (mSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (cSubgroup S) (S : Subgroup G))
    (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    (hPnot : P ∉ SectionThree.PSet (mSubgroup S) (S : Subgroup G)) :
    ∃ Pstar : Subgroup G,
      Pstar ∈ SectionThree.PStarSet (mSubgroup S) (S : Subgroup G) ∧
      (P, Pstar) ∈ Lambda S ∧
      ((SectionThree.PStarSet (cSubgroup S) (S : Subgroup G) ⊆
          SectionThree.PSet (mSubgroup S) (S : Subgroup G)) →
        twoCoreAmbient (mSubgroup S) ≤ twoCoreAmbient (cSubgroup S) ∧
        ∃ E : Subgroup G,
          (E : Set G) =
            (twoResidualAmbient Pstar : Set G) *
              (twoCoreAmbient (cSubgroup S) : Set G) ∧
          IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) := by
  sorry

end Stellmacher.SectionFour
