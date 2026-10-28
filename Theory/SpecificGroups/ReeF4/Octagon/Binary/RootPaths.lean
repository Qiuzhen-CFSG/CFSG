module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.OctagonRootPath

/-!
# Nine-path transitivity for the full binary Ree source model

The constructed binary octagonal datum applies the generic normalizer-apartment
argument to the actual full Ree group and its two prescribed parabolics. The
source Bool order is retained: false is the Suzuki-side first parabolic and
true the linear-side second parabolic. Both vertex types satisfy the same
literal rooted nine-path transitivity statement used by F.4.8's common-cover
transport; the group and action are not replaced by a recognition output.

Source: Aschbacher–Smith F.1.12 and F.4.8.
-/

public section
namespace ReeF4.Octagon.Binary
open Theory.AlgebraicGroup.TitsSystem SimpleGraph.PathTransitivePolygon Subgroup

/-- Every vertex stabilizer of the actual binary Ree model is nine-path transitive. -/
theorem rootPathTransitive_nine (v : CosetGeometry.Vertex family) :
    RootPathTransitive (DihedralGeometry.graph family) (Model 0) v 9 := by
  obtain ⟨D⟩ := exists_datum
  exact D.rootPathTransitive_nine v

/-- The two original source base types, with Suzuki first and linear second. -/
theorem both_base_rootPathTransitive_nine (i : Bool) :
    RootPathTransitive (DihedralGeometry.graph family) (Model 0) (CosetGeometry.base family i) 9 :=
  rootPathTransitive_nine _

end ReeF4.Octagon.Binary
