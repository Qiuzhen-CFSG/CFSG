module

public import Stellmacher.SectionFour.LemmaFourTwo

namespace Stellmacher.SectionFour

universe u

/-! **Stellmacher (4.3).** -/
public theorem lemma_four_three
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) :
    dSubgroup S =
        sInf {D₀ : Subgroup G |
          ∃ P : Subgroup G, P ∈ pZero S ∧ D₀ = twoCoreAmbient P} ∧
      dSubgroup S =
        sInf {D₁ : Subgroup G |
          ∃ P : Subgroup G, P ∈ pOne S ∧ D₁ = twoCoreAmbient P} := by
  sorry

end Stellmacher.SectionFour
