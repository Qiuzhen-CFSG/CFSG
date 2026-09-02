module

public import Stellmacher.SectionFiveToSeven.Defs

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (5.3).**  Under Hypothesis 2 both members of the amalgam
are solvable and of characteristic 2 type. -/
public theorem lemma_five_three
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) :
    Group.IsSolvable P1 ∧ Stellmacher.IsCharacteristicTwoType P1 ∧
      Group.IsSolvable P2 ∧ Stellmacher.IsCharacteristicTwoType P2 := by
  sorry

end Stellmacher.SectionsFiveToSeven
