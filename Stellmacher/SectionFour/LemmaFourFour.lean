module

public import Stellmacher.SectionFour.LemmaFourThree

namespace Stellmacher.SectionFour

universe u

/-! **Stellmacher (4.4).** -/
public theorem lemma_four_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    (hPnot : P ∉ SectionThree.PSet (mSubgroup S) (S : Subgroup G))
    (k : ℕ) (hk : k = 0 ∨ k = 1) :
    ∃ Pstar : Subgroup G,
      Pstar ∈ pAt S k ∧ (P, Pstar) ∈ Lambda S := by
  sorry

end Stellmacher.SectionFour
