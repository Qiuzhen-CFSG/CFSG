module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.PlaneRecognition.Model
public import Theory.Combinatorics.ProjectivePlaneFourCoordinates

/-!
# Coordinates for the completion's order-four plane

The three metric and valence hypotheses give the actual coset projective plane.
Uniqueness of the order-four incidence plane identifies its points and lines with
PG(2,4), with false vertices as points and true vertices as lines. No group
recognition or action-image assumption is used in constructing these coordinates.

Source: the PSL₃(4) plane branch of Aschbacher–Smith F.4.8(2), printed p.278,
as used in F.4.26, printed p.288. The separate smallness argument supplies the
metric hypotheses from the original involutions.
-/
@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
open Configuration Matrix.PSL3Four Matrix.PSL3Four.SylowModel.MatrixRealization
local instance : DecidableEq F := Classical.decEq _
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

/-- The actual coset plane has projective coordinates over the field of four
elements, using only uniqueness of short geodesics, diameter and valence. -/
theorem exists_coordinates_of_geometry
    (hu : c.graph.UniqueGeodesicsBelow 3) (hd : ∀ v w, c.graph.dist v w ≤ 3)
    (hv : ∀ v, Nat.card (c.graph.neighborSet v) = 5) :
    ∃ (ep : c.Point ≃ PG) (el : c.Line ≃ PG), ∀ p l, ep p ∈ el l ↔ p ∈ l := by
  let := c.planeOfGeometry hu hd hv
  apply Four.exists_incidence_equiv (c.pointCount_of_geometry hv)
  intro l
  rw [ProjectivePlane.pointCount_eq, order_projectivePlane]
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
