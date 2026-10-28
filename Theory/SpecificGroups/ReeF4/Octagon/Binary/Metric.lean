module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.Metric

/-!
# The actual binary Ree metric fact used in J.5.9

The native binary Weyl datum supplies connectedness, diameter eight as an
upper bound, and the unique inward neighbor at every positive distance below
eight. This applies the generic octagonal argument to the literal full Ree
parabolics, with the source Suzuki-first vertex convention unchanged.
Source: Aschbacher–Smith J.5.9, printed p.448.
-/

public section
namespace ReeF4.Octagon.Binary
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry

theorem graph_connected : (graph family).Connected := by
  obtain ⟨D⟩ := exists_datum
  exact D.connected

theorem graph_dist_le_eight (u v : CosetGeometry.Vertex family) :
    (graph family).dist u v ≤ 8 := by
  obtain ⟨D⟩ := exists_datum
  exact D.dist_le_eight u v

/-- Original binary-octagon instance of source J.5.9. -/
theorem unique_predecessor (r v : CosetGeometry.Vertex family)
    (hpos : 0 < (graph family).dist v r) (hshort : (graph family).dist v r < 8) :
    ∃! w, (graph family).Adj v w ∧
      (graph family).dist w r + 1 = (graph family).dist v r := by
  obtain ⟨D⟩ := exists_datum
  exact D.unique_predecessor r v hpos hshort

end ReeF4.Octagon.Binary
