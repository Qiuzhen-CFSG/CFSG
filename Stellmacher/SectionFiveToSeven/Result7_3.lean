module

public import Stellmacher.SectionFiveToSeven.Defs

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenThreeConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) : Prop where
  sylow_and_core :
    ∀ d l : Γ.Vertex, l ∈ neighborhood Γ d →
      ∀ T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l),
        IsSylowTwoIn (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T)
          (stabilizer Γ d) ∧
        IsSylowTwoIn (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T)
          (stabilizer Γ l) ∧
        q Γ d ≤ stabilizer Γ l
  center_core :
    ∀ d l : Γ.Vertex, l ∈ neighborhood Γ d →
      z Γ d ≤ omegaOneCenter (q Γ d)
  centralizer_alternative :
    ∀ d l : Γ.Vertex, l ∈ neighborhood Γ d →
      ∀ T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l),
        (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T ⊓
            Subgroup.centralizer (z Γ d : Set G) = q Γ d) ∨
          (z Γ d = omegaOneCenter (stabilizer Γ d) ∧
            z Γ d = omegaOneCenter
              (sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T))
  center_neighbor_trivial :
    ∀ d l : Γ.Vertex, l ∈ neighborhood Γ d →
      z Γ d = omegaOneCenter (stabilizer Γ d) →
      Subgroup.center (stabilizer Γ l) = ⊥

/-- **Stellmacher (7.3).**  Sylow, center, and centralizer properties along
an edge of the coset graph. -/
public theorem lemma_seven_three
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) :
    LemmaSevenThreeConclusion Γ := by
  sorry

end Stellmacher.SectionsFiveToSeven
