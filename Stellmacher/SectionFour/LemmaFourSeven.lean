module

public import Stellmacher.SectionFour.LemmaFourSix

namespace Stellmacher.SectionFour

universe u

/-! **Stellmacher (4.7).**  The first member is required to be *not contained*
in `C`, exactly as in the source. -/
public theorem lemma_four_seven
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) :
    ∃ P Pstar : Subgroup G,
      (P, Pstar) ∈ Lambda S ∧
      ¬ P ≤ cSubgroup S ∧
      Pstar ∈ pZero S := by
  sorry

end Stellmacher.SectionFour
