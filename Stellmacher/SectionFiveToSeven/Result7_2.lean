module

public import Stellmacher.SectionFiveToSeven.Defs

namespace Stellmacher.SectionsFiveToSeven

universe u v

/-- **Stellmacher (7.2).**  The action of the ambient group on its coset
graph is faithful. -/
public theorem lemma_seven_two
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) :
    Γ.actionKernel = ⊥ := by
  sorry

end Stellmacher.SectionsFiveToSeven
