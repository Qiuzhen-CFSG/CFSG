module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.Girth
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.ApartmentCycle
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.Metric

/-!
# Metric predecessors in the actual octagonal coset geometry

The marked Weyl apartment and Bruhat coverage give connectedness and diameter
at most eight. The proved cycle bound then gives the unique preceding neighbor
of every vertex at positive distance below eight. All vertices remain literal
typed parabolic cosets. Source: GLS3 §§2.3,2.6; Aschbacher–Smith J.5.9.
-/

public section
namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open Subgroup
variable {X I : Type*} [Group X] {T : TitsSystem (X := X)} {F : I → Subgroup X}
namespace OctagonalDatum
variable (D : OctagonalDatum T F)
include D

theorem connected : (graph F).Connected := by
  have : Nonempty (CosetGeometry.Vertex F) := ⟨CosetGeometry.base F (D.typeEquiv.symm false)⟩
  refine { preconnected := ?_ }
  intro u v
  obtain ⟨p,_⟩ := diameter_bound_of_standardApartmentCycle F T D.borel_le
    D.standardApartmentCycle u v
  exact ⟨p⟩

theorem dist_le_eight (u v : CosetGeometry.Vertex F) : (graph F).dist u v ≤ 8 := by
  obtain ⟨p,hp⟩ := diameter_bound_of_standardApartmentCycle F T D.borel_le
    D.standardApartmentCycle u v
  exact ((graph F).dist_le p).trans hp

theorem unique_predecessor (r v : CosetGeometry.Vertex F)
    (hpos : 0 < (graph F).dist v r) (hshort : (graph F).dist v r < 8) :
    ∃! w, (graph F).Adj v w ∧ (graph F).dist w r + 1 = (graph F).dist v r :=
  SimpleGraph.OctagonShortPaths.unique_predecessor D.connected D.cycle_bound r v hpos hshort

end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
