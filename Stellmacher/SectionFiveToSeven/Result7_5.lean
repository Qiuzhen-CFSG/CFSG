module

public import Stellmacher.SectionFiveToSeven.Defs


open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenFiveConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) : Prop where
  odd_distance : Odd cp.length
  next_center : z Γ cp.firstStep = omegaOneCenter S ∧
    z Γ cp.firstStep = omegaOneCenter (stabilizer Γ cp.firstStep)
  centralizer_residual :
    q Γ cp.a ⊓ Subgroup.centralizer (e Γ cp.a : Set G) = ⊥
  start_center_trivial : Subgroup.center (stabilizer Γ cp.a) = ⊥
  longer_case :
    1 < cp.length →
      IsElementaryAbelian 2 (v Γ cp.firstStep) ∧
      IsQuadraticOn (v Γ cp.firstStep) (v Γ cp.a') ∧
      IsQuadraticOn (v Γ cp.a') (v Γ cp.firstStep)

/-- **Stellmacher (7.5).**  Consequences of commuting endpoint centers along
a critical path. -/
public theorem lemma_seven_five
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a, z Γ cp.a'⁆ = ⊥) :
    LemmaSevenFiveConclusion Γ cp := by
  sorry

end Stellmacher.SectionsFiveToSeven
