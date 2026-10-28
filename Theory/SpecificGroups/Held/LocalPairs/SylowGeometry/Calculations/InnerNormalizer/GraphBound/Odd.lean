module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.OddGraph0
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.OddGraph1
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.OddGraph2
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.OddGraph3

/-!
# Membership of the odd colored graph symmetry

Assemble all checked adjacency rows with the checked color preservation.
The sign certificate is independent of these graph checks.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

public theorem odd_mem : oddPermutation ∈ coloredGraphGroup := by
  refine ⟨?_, odd_colors⟩
  intro x y
  have hx := x.isLt
  by_cases h0 : x.val < 512
  · exact odd_graph_0 x (by omega) h0 y
  by_cases h1 : x.val < 1024
  · exact odd_graph_1 x (by omega) h1 y
  by_cases h2 : x.val < 1536
  · exact odd_graph_2 x (by omega) h2 y
  exact odd_graph_3 x (by omega) hx y

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
