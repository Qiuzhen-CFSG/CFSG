module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NeighborCounts
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Connectivity
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.EdgeFixer
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreFaithful
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Generation

/-!
# The complete earlier-source input for the AS91 cycle argument

The original marked algebra supplies every field of the unchanged section 7
Input. The exact (6.2)(3) marker-intersection statement discharges the premise
of the independent fusion/generation theorem. Its generation conclusion gives
ambient connectivity. The line, plane, orbital, radical and triangle results
supply the remaining geometric fields on the same P and L.

This is conditional on the explicit earlier-section LocalData. Constructing
that data and the section 8 comparison remains with source recognition.
Ambient simplicity is inherited from the original finite-simple consumer;
it supplies point faithfulness and is not used as a generation substitute.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §§5–6, pp.599–602.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open Subgroup SourceCycleBase
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Source (6.5)(2), with the exact earlier marker-intersection premise
proved from this same LocalData. -/
theorem LocalData.generate {h : IsTypeJ4 z} (a : LocalData h) :
    centralizer z ⊔ a.P.M = ⊤ :=
  SourceFusion.generate a a.source_six_two_three_map

/-- The full ambient incidence geometry is connected, after discharging
the source generation equation. -/
theorem LocalData.geometry_connected {h : IsTypeJ4 z} (a : LocalData h) :
    (incidenceGraph a.L).Connected :=
  a.geometry_connected_of_generate a.generate

/-- Every unchanged section 7 input field, constructed from the original
marked section 4 algebra and the ambient simplicity instance supplied by
its actual recognition consumer. The point and line data are unchanged. -/
noncomputable def source_input_of_local_data [IsSimpleGroup G]
    (h : IsTypeJ4 z) (a : LocalData h) : Input h := by
  classical
  let t := Classical.choose a.exists_edge_element
  have ht := Classical.choose_spec a.exists_edge_element
  exact {
    P := a.P
    L := a.L
    t := t
    t_plane := ht.1
    t_line := ht.2.1
    t_not_point := ht.2.2.1
    t_sq := ht.2.2.2.1
    faithful := a.point_corefree
    generate := a.generate
    vertex_maximal := a.vertex_maximal
    plane_maximal := a.plane_maximal
    edge_fixer := a.edge_fixer t ht.2.1
    line_transitive := ht.2.2.2.2
    residue := a.residueChart
    plane := a.planeChart
    local_edge := a.local_edge t ht.1 ht.2.1 ht.2.2.1
    line_card := a.line_card
    flag_transitive := fun x l π hxl _ hlπ => a.flag_transitive x l π hxl hlπ
    geometry_connected := a.geometry_connected
    residues_connected := a.residues_connected
    string := a.string
    unique_line := a.unique_line
    plane_closed := a.plane_closed
    core_fixes_lines := a.core_fixes_lines
    core_fixes_planes := a.core_fixes_planes
    core_transitive_other := a.core_transitive_other
    core_regular_other := a.core_regular_other
    core_faithful_neighbors := a.core_faithful_neighbors
    plane_card := a.plane_card
    plane_neighbor_card := a.plane_neighbor_card
    plane_nonneighbor_card := a.plane_nonneighbor_card
    plane_rank_three := a.plane_rank_three
    unique_plane := a.unique_plane
    plane_pair_types := a.plane_pair_types
    plane_pair_orbits := a.plane_pair_orbits
    plane_pair_types_realized := a.plane_pair_types_realized
    orbital_partition := a.orbital_partition
    orbital_transitive := a.orbital_transitive
    delta_zero := a.delta_zero
    delta_coplanar := a.delta_coplanar
    delta_card := a.delta_card
    delta_one_neighbors := a.delta_one_neighbors
    delta_two_neighbors := a.delta_two_neighbors
    core_stabilizer_transitive := a.core_stabilizer_transitive
    triangles_in_plane := a.triangles_in_plane
    triangle_permutations := a.triangle_permutations
    triangle_labels := a.triangle_labels
    common_neighbors_in_plane := a.common_neighbors_in_plane
    marker_mem_core := a.marker_mem_core }

@[simp] theorem source_input_point [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    (source_input_of_local_data h a).P = a.P := rfl

@[simp] theorem source_input_line [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    (source_input_of_local_data h a).L = a.L := rfl
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
