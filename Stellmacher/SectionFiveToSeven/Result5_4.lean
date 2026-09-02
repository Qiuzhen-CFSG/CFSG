module

public import Stellmacher.SectionFiveToSeven.Defs

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (5.4).**  The central elementary-abelian subgroup of `S` is
contained in the 2-core of `⟨F₁,F₂⟩` under the stated alternative. -/
public theorem lemma_five_four
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (T F1 F2 H0 M : Subgroup H)
    (hT : baumannIn S ≤ T ∧ T ≤ S)
    (hF1 : F1 ∈ PFamily (⊤ : Subgroup H) T)
    (hF2 : F2 ∈ PFamily (⊤ : Subgroup H) T)
    (hH0 : H0 = F1 ⊔ F2)
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hcore : twoCoreIn H0 ≠ ⊥)
    (halt : S = (S0 : Subgroup H) ∨ ¬ H0 ≤ M) :
    omegaOneCenter S ≤ twoCoreIn H0 := by
  sorry

end Stellmacher.SectionsFiveToSeven
