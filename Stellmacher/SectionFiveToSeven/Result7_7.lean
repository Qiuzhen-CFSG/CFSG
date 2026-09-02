module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenSevenConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (C : Subgroup G) : Prop where
  centralizer_commutator :
    ⁅Subgroup.centralizer (z Γ cp.a : Set G),
      e Γ cp.a ⊔ twoCoreIn (e Γ cp.firstStep)⁆ ≤ q Γ cp.a
  next_v_centralizer_two :
    IsTwoGroup (Subgroup.centralizer (v Γ cp.firstStep : Set G))
  longer_endpoint :
    1 < cp.length →
      ¬ e Γ cp.a' ≤ C ∧ z Γ cp.a' ≠ z Γ cp.firstStep

/-- **Stellmacher (7.7).**  The characteristic-2 centralizer conclusions in
the case where the next residual is subnormal in `C_G(Ω₁(Z(S)))`. -/
public theorem lemma_seven_seven
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hsubnormal : SubnormalIn (e Γ cp.firstStep) C)
    (hcore : twoCoreIn C ≤ S)
    (hchar : Stellmacher.IsCharacteristicTwoType C) :
    LemmaSevenSevenConclusion Γ cp C := by
  sorry

end Stellmacher.SectionsFiveToSeven
