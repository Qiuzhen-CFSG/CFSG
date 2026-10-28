module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Generation
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Cycles

/-!
# The actual native Mathieu uniqueness system

The vertices are the 759 octads; the local group is the literal stabilizer of
the standard sextet. All three generation identities and both transitivity
conditions are proved on these carriers. The local graph is precisely the
induced disjoint-octad graph in the standard sextet, with its actual trio and
plane stabilizers retained.

The base reduction now has only the four-generation premise: the plane-edge
premise from `Cycles` is discharged by the native local orbit calculation.
Four-generation and the source/model local comparison are separate obligations.

Source: Aschbacher, *Sporadic Groups* (1994), §38, Exercise 13.2,
printed pp.205–210, and §41, pp.219–222.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open PairOvergroups Theory.GroupTheory.GraphUniquenessSystem

/-- The native octad–trio–sextet uniqueness system, with no generation premises. -/
def system : System M24 Octad where
  graph := graph
  H := sextetStabilizer standardSextet
  x := first
  y := second
  adjacent := first_adj_second
  preserves := preserves
  faithful := faithful
  vertex_transitive := vertex_transitive first
  edge_transitive O P h := by
    obtain ⟨g,hO,hP⟩ := edge_transitive h
    exact ⟨g,Or.inl ⟨hO,hP⟩⟩
  local_orbit := by
    obtain ⟨g,hg,_⟩ := exists_local_swap
    exact ⟨g,hg⟩
  generate := generate
  vertex_generate := vertex_generate
  local_generate := local_generate

@[simp] theorem system_graph : system.graph = graph := rfl
@[simp] theorem system_local : system.H = sextetStabilizer standardSextet := rfl
@[simp] theorem system_vertex : system.vertexGroup = octadStabilizer first :=
  stabilizer_octad first
@[simp] theorem system_edge : system.edgeGroup =
    octadStabilizer first ⊓ octadStabilizer second := by
  change MulAction.stabilizer M24 first ⊓ MulAction.stabilizer M24 second = _
  rw [stabilizer_octad, stabilizer_octad]

/-- The marked edge stabilizer preserves the actual standard trio. -/
theorem system_edgeSet_le_trio : system.edgeSetGroup ≤ trioStabilizer standardTrio :=
  edgeStabilizer_le_trio first_adj_second first_on_standardTrio second_on_standardTrio

/-- The point–plane intersection is the literal intersection of native stabilizers. -/
theorem system_marked_intersection : system.H ⊓ system.vertexGroup =
    sextetStabilizer standardSextet ⊓ octadStabilizer first := by
  rw [system_local, system_vertex]

/-- Native local edges are exactly the adjacent octads incident with the marked plane. -/
theorem localEdge_iff (O P : Octad) : system.localEdge O P ↔
    graph.Adj O P ∧ OnPlane O standardSextet ∧ OnPlane P standardSextet := by
  constructor
  · intro h
    refine ⟨system.localEdge_adj h, ?_⟩
    obtain ⟨g,hg | hg⟩ := h
    all_goals
      have hs : (g : M24) • standardSextet = standardSextet := Sextet.ext g.property
      have hfirst := onPlane_smul (g : M24)
        (standardTrio_on_standardSextet first first_on_standardTrio)
      have hsecond := onPlane_smul (g : M24)
        (standardTrio_on_standardSextet second second_on_standardTrio)
      change (g : M24) • first = _ ∧ (g : M24) • second = _ at hg
    · exact ⟨by simpa only [hs,hg.1] using hfirst,
        by simpa only [hs,hg.2] using hsecond⟩
    · exact ⟨by simpa only [hs,hg.2] using hsecond,
        by simpa only [hs,hg.1] using hfirst⟩
  · rintro ⟨hOP,hO,hP⟩
    obtain ⟨g,hg⟩ := plane_edge_transitive hOP hO hP
    exact ⟨g,Or.inl hg⟩

/-- Once four-generation is supplied, the actual native system has a cycle base. -/
theorem isBase_of_fourGenerated (h4 : FourGenerated) : system.IsBase :=
  system.isBase_of_octadGraph_fourGenerated rfl h4
    (fun {O P} hOP hO hP => (localEdge_iff O P).mpr ⟨hOP,hO,hP⟩)

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph
