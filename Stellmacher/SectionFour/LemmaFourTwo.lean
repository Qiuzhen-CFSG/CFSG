module

public import Stellmacher.SectionFour.LemmaFourOne

namespace Stellmacher.SectionFour

universe u

/-! **Stellmacher (4.2).** -/
public theorem lemma_four_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (L : Subgroup G) (hL : SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) L) :
    localD L (S : Subgroup G) = localDStar L (S : Subgroup G) ∧
      localD L (S : Subgroup G) = twoCoreAmbient L ∧
      dSubgroup S =
        sInf {D : Subgroup G |
          ∃ L' : Subgroup G,
            L' ∈ SectionThree.maxLSet (⊤ : Subgroup G) (S : Subgroup G) ∧
              D = twoCoreAmbient L'} := by
  sorry

end Stellmacher.SectionFour
