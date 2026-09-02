module

public import Stellmacher.SectionFiveToSeven.Defs

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (6.1).**  The Baumann subgroup of the amalgam is not
contained in the 2-core of `P₂`. -/
public theorem lemma_six_one
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) :
    ¬ baumannIn S ≤ twoCoreIn P2 := by
  sorry

end Stellmacher.SectionsFiveToSeven
