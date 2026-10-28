module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.LocalAction
public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.CarrierComparison
public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.GraphComparison

/-!
# Rank-three recognition of the exact Higman--Sims carrier

A transitive permutation subgroup on 100 points whose actual point stabilizer
is M₂₂ and has three orbits, including one of length 22, is isomorphic to the
specified ATLAS Higman--Sims carrier. No simplicity, primitivity, graph
comparison, or model identification is an additional hypothesis.

The graph has forced parameters (100,22,0,6). Its neighbors carry the natural
Mathieu action, and the 77 nonneighbors are reconstructed as the native
Mathieu hexads. A checked coordinate bijection identifies its edges with the
literal ATLAS graph. Primitivity gives simplicity and perfectness of the
original group; its order and the graph-automorphism order bound then identify
its image with the exact ATLAS subgroup. The isomorphism retains the actual
permutation-action intertwining equation.

Source: Wales, "Uniqueness of the graph of a rank three group", Pacific
J. Math. 30 (1969), pp.271--274, especially the HS application on p.274.
This discharges the standalone permutation-recognition input in
Aschbacher--Smith I.4.8 (printed p.418). Constructing the rank-three action
from the type-HS local hypotheses remains a separate source argument.
-/

public section
namespace Sporadic.LeechRelated.HS

/-- The group identification also identifies the actual degree-100 actions. -/
theorem RankThreeData.recognition_equivariant {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) :
    ∃ (E : Fin 100 ≃ Fin 100) (f : P ≃* Carrier),
      ∀ g x, inclusion (f g) (E x) = E (g • x) := by
  obtain ⟨E, hE⟩ := h.exists_graph_equiv
  obtain ⟨f, hf⟩ := h.recognition_of_graph_equiv E hE
  exact ⟨E, f, hf⟩

/-- Standalone recognition of the rank-three Mathieu extension as the exact
Higman--Sims carrier. -/
theorem RankThreeData.recognition {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : Nonempty (P ≃* Carrier) := by
  obtain ⟨_, f, _⟩ := h.recognition_equivariant
  exact ⟨f⟩

end Sporadic.LeechRelated.HS
