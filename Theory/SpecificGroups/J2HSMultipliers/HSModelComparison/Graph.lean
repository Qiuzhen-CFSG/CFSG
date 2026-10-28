module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.Graph
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The graph of the published HS permutation generators

This packages the kernel-checked orbital relation of `HSG1-p100B0` as a
simple graph. A graph isomorphism from this graph to the marked Leech graph
is the geometric input to the comparison of the two group models.

Source: the ATLAS degree-100 permutations and the retained orbit certificate
in `LeechRelated/AtlasCarriers/HS/AutomorphismNormalizerIndex/Graph.lean`.
-/

@[expose] public section

namespace Sporadic.LeechRelated.HS.ModelComparison

/-- The actual graph preserved by the two published permutation generators. -/
def permutationGraph : SimpleGraph (Fin 100) where
  Adj := NormalizerIndex.adjacency
  symm := ⟨fun _ _ => (NormalizerIndex.adjacency_symm _ _).mp⟩
  loopless := ⟨NormalizerIndex.adjacency_irrefl⟩

end Sporadic.LeechRelated.HS.ModelComparison
