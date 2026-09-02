module

public import Stellmacher.SectionFiveToSeven.Defs

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenOneConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) : Prop where
  connected : IsConnected Γ
  edge_not_vertex_transitive : IsEdgeTransitive Γ ∧ ¬ IsVertexTransitive Γ
  distinguished_edge : ∃ a b : Γ.Vertex,
    IsAdjacent Γ a b ∧ stabilizer Γ a = P1 ∧ stabilizer Γ b = P2
  vertex_stabilizers_conjugate :
    ∀ d : Γ.Vertex, ∃ g : G,
      stabilizer Γ d = conjugateBy P1 g ∨
        stabilizer Γ d = conjugateBy P2 g
  edge_stabilizers_conjugate :
    ∀ d l : Γ.Vertex, IsAdjacent Γ d l →
      ∃ g : G,
        stabilizer Γ d ⊓ stabilizer Γ l = conjugateBy (P1 ⊓ P2) g
  local_transitivity : ∀ d : Γ.Vertex,
    IsActionTransitiveOn Γ (stabilizer Γ d) (neighborhood Γ d)

/-- **Stellmacher (7.1).**  Elementary properties of the coset graph,
including the conjugacy description of vertex and edge stabilizers. -/
public theorem lemma_seven_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) :
    LemmaSevenOneConclusion Γ := by
  sorry

end Stellmacher.SectionsFiveToSeven
