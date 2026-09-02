module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (6.4).**  In the trivial-action case, each indicated
centralizer together with `S` cannot generate all of `P₂`. -/
public theorem lemma_six_four
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (V : Subgroup H)
    (hV : V = sectionSixV S P1)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (hJ : actionCriticalSubgroup V S ≠ ⊥) :
    ∀ w : H,
      w ∈ V →
      w ∈ Subgroup.centralizer (actionCriticalSubgroup V S : Set H) →
      w ∉ omegaOneCenter S →
      P2 ≠ sectionSixCentralizerJoin P2 S w := by
  sorry

end Stellmacher.SectionsFiveToSeven
