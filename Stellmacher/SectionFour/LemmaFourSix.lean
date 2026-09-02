module

public import Stellmacher.SectionFour.LemmaFourFive

namespace Stellmacher.SectionFour

universe u

/-! **Stellmacher (4.6).**  The conclusion is deliberately `nsubseteq`, as
in the paper (it is not a proper-subset assertion). -/
public theorem lemma_four_six
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (mSubgroup S) (S : Subgroup G)) :
    ¬ SectionThree.PStarSet (cSubgroup S) (S : Subgroup G) ⊆
      SectionThree.PSet (mSubgroup S) (S : Subgroup G) := by
  sorry

end Stellmacher.SectionFour
