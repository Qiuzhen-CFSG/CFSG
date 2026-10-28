module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber6
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber7
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber8
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber9
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows.Fiber10

/-!
# All packed crossing rows in the max2 forest

The certified node lookup and row arithmetic identify each bounded numerical
check with the unchanged `PackedEdge` equation. The eleven components contain
4736 nodes, hence exactly 4725 nonroot equations. The two singleton components
have no nonroot obligations.

This supplies only the packed-row input to `Forest.edges_of_certificates`.
Actor matrix evaluations remain independent, as does the group-order bound
used by that assembly theorem.

Source: ATLAS J4G1-max2W1, R. A. Wilson, S. J. Nickerson, J. N. Bray;
see `Edges/source/README.md` and `PackedRows/source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges

/-- All 4725 prescribed nonroot crossing-row equations, without extra premises. -/
theorem packed_edges (k : Fin 11) (n : Fin (fiberBound k)) (hn : n.val ≠ 0) :
    PackedEdge k n.val := by
  apply (PackedRows.check_iff k n.val).mp
  rw [← PackedRows.fastTuple_eq]
  fin_cases k
  · have h := n.isLt
    change n.val < 1 at h
    omega
  · have h := n.isLt
    change n.val < 1 at h
    omega
  · exact PackedRows.fiber2 n hn
  · exact PackedRows.fiber3 n hn
  · exact PackedRows.fiber4 n hn
  · exact PackedRows.fiber5 n hn
  · exact PackedRows.fiber6 n hn
  · exact PackedRows.fiber7 n hn
  · exact PackedRows.fiber8 n hn
  · exact PackedRows.fiber9 n hn
  · exact PackedRows.fiber10 n hn

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
