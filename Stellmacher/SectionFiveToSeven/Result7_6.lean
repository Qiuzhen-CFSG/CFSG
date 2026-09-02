module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenSixConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) : Prop where
  core_intersection_not_normal :
    ¬ IsNormalIn (q Γ cp.a ⊓ q Γ cp.firstStep)
      (stabilizer Γ cp.firstStep)
  next_residual_core :
    ¬ twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.a ∧
      e Γ cp.a ≤ conjugateClosure (twoCoreIn (e Γ cp.firstStep))
        (stabilizer Γ cp.a)
  neighbor_core_noncontainment :
    ∀ m : Γ.Vertex, m ∈ neighborhood Γ cp.firstStep →
      q Γ m ⊔ (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) =
        stabilizer Γ cp.firstStep →
      ¬ q Γ cp.a ⊓ q Γ cp.firstStep ≤ q Γ m
  centralizer_join_proper :
    (Subgroup.centralizer (z Γ cp.a : Set G) ⊓
        stabilizer Γ cp.firstStep) ⊔
      (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) ≠
      stabilizer Γ cp.firstStep

/-- **Stellmacher (7.6).**  The four non-normality and containment properties
along the first edge of a critical path. -/
public theorem lemma_seven_six
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) :
    LemmaSevenSixConclusion Γ cp := by
  sorry

end Stellmacher.SectionsFiveToSeven
