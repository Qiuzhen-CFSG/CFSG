module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.GeometricReduction
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane
public import Theory.Combinatorics.CollineationAction

/-!
# The completion's actual projective plane and faithful action

Points and lines are the false and true fibers of the original typed coset
graph. Diameter three, uniqueness of geodesics below three, and valence five
provide a projective plane of order four, with 21 points and 21 lines.
The whole-overlap hypothesis makes the original paired incidence action
faithful; the plane axioms then make its point action faithful as well.

These are geometric inputs to the action comparison in Aschbacher–Smith
F.4.8(2), p.278, as used in F.4.26, p.288. No identification with the
Desarguesian model or with its linear collineations is asserted here.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
open Configuration Subgroup.CosetGeometry
noncomputable section
variable {G : Type*} [Group G] (c : Completion G)

abbrev Point := RankTwo.Point c.family
abbrev Line := RankTwo.Line c.family

def planeAction : G →* Collineation c.Point c.Line :=
  Collineation.ofAction G c.Point c.Line

theorem planeAction_injective (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective c.planeAction := by
  intro g h he
  apply c.vertex_action_injective_of_overlap ho
  apply Equiv.Perm.ext
  intro v
  change g • v = h • v
  cases ht : v.type with
  | false =>
    exact congrArg Subtype.val (congrArg (fun d : Collineation c.Point c.Line =>
      Collineation.pointHom c.Point c.Line d ⟨v, ht⟩) he)
  | true =>
    exact congrArg Subtype.val (congrArg (fun d : Collineation c.Point c.Line =>
      Collineation.lineHom c.Point c.Line d ⟨v, ht⟩) he)

variable [Finite G]
variable (hu : c.graph.UniqueGeodesicsBelow 3)
  (hd : ∀ v w, c.graph.dist v w ≤ 3)
  (hv : ∀ v, Nat.card (c.graph.neighborSet v) = 5)

@[instance_reducible] def planeOfGeometry : ProjectivePlane c.Point c.Line :=
  RankTwo.projectivePlaneOfGeometry c.family c.generated hu hd 4 (by decide) hv

include hu hd hv in
theorem card_points_of_geometry : Nat.card c.Point = 21 :=
  RankTwo.card_fiber_of_plane_geometry c.family c.generated hu hd 4 hv false

include hu hd hv in
theorem card_lines_of_geometry : Nat.card c.Line = 21 :=
  RankTwo.card_fiber_of_plane_geometry c.family c.generated hu hd 4 hv true

omit [Finite G] in
include hv in
theorem pointCount_of_geometry (l : c.Line) : pointCount c.Point l = 5 :=
  (Nat.card_congr (RankTwo.pointsOnLineEquivNeighbors c.family l)).trans (hv l.val)

omit [Finite G] in
include hv in
theorem lineCount_of_geometry (p : c.Point) : lineCount c.Line p = 5 :=
  (Nat.card_congr (RankTwo.linesOnPointEquivNeighbors c.family p)).trans (hv p.val)

theorem plane_order_of_geometry :
    let := c.planeOfGeometry hu hd hv
    ProjectivePlane.order c.Point c.Line = 4 := by
  let := c.planeOfGeometry hu hd hv
  have h := c.pointCount_of_geometry hv ⟨RankTwo.base c.family true, rfl⟩
  rw [ProjectivePlane.pointCount_eq] at h
  omega

include hu hd hv in
theorem point_action_injective_of_geometry
    (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (MulAction.toPermHom G c.Point) := by
  let := c.planeOfGeometry hu hd hv
  intro g h he
  apply c.planeAction_injective ho
  apply Collineation.ext_points
  intro p
  exact Equiv.congr_fun he p
end
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
