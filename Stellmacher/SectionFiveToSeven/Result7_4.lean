module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenFourConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) : Prop where
  first_containment : z Γ cp.a ≤ v Γ cp.firstStep ∧
    v Γ cp.firstStep ≤ stabilizer Γ cp.a'
  reverse_containment : z Γ cp.a' ≤ stabilizer Γ cp.a ∧
    v Γ cp.a' ≤ stabilizer Γ cp.firstStep
  edge_centralizer :
    S ⊓ Subgroup.centralizer (z Γ cp.a : Set G) = q Γ cp.a
  commutator_case :
    ⁅z Γ cp.a, z Γ cp.a'⁆ ≠ ⊥ →
      (∀ T : Sylow 2 ↥(stabilizer Γ cp.a'),
        sylowTwoAmbient (stabilizer Γ cp.a') T ⊓
            Subgroup.centralizer (z Γ cp.a' : Set G) = q Γ cp.a') ∧
      IsCriticalPair Γ cp.a' cp.a
  quadratic :
    IsQuadraticOn (z Γ cp.a) (z Γ cp.a') ∧
      IsQuadraticOn (z Γ cp.a') (z Γ cp.a)

/-- **Stellmacher (7.4).**  Containment, centralizer, critical-pair, and
quadratic-action properties for a critical path. -/
public theorem lemma_seven_four
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) :
    LemmaSevenFourConclusion Γ cp := by
  sorry

end Stellmacher.SectionsFiveToSeven
