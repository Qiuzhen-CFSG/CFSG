module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleHomotopy

/-!
# Triangle contraction in the ternary orthogonality graph

The checked geometry of the actual projective norm-minus-one points supplies
the three local hypotheses of the diameter-two contraction theorem. Thus every
closed walk contracts by backtracks and triangles. This is the simple
connectivity assertion of Aschbacher--Smith F.5.8(2), printed pp.303--304.

The acting group and conjugacy of triangles are separate assertions: neither
is needed to contract walks, and neither is inferred from the finite graph.
-/

public section

namespace OmegaSixThree.OrthogonalityGraph

/-- The source's quadrilateral and pentagon filling conditions on the actual
projective graph. -/
theorem triangleContractionData : graph.TriangleContractionData where
  short x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_common_neighbor x y
    exact Or.inr (Or.inr ⟨z, hxz, hyz.symm⟩)
  common_connected x y hne hn := (commonNeighbors_connected x y hne hn).preconnected
  triple x y v hxy _ _ _ _ := by
    obtain ⟨a, hxa, hya, hva⟩ := edge_common_neighbor x y v hxy
    exact ⟨a, hva, hxa, hya⟩

/-- F.5.8(2): all closed edge paths in the projective orthogonality graph
contract using triangles and backtracks. -/
theorem triangleSimplyConnected : graph.TriangleSimplyConnected :=
  triangleContractionData.simplyConnected

end OmegaSixThree.OrthogonalityGraph
