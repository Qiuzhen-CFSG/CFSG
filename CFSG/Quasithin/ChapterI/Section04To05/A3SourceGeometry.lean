module

public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry.Incidence
public import CFSG.Quasithin.ChapterI.Section04To05.A3Recognition

/-!
# Recognition from the original A₃ coset geometry

The local Fano identifications, unique lines, faithful point action and
fifteen-point count construct every field used by the permutation-module
recognition theorem. The nontrivial point-core line action supplies its
remaining core hypothesis. Thus an original A₃ D-system gives an actual
PSL₄(2) isomorphism, without an incidence or recognition premise.

Source: Aschbacher–Smith I.5.1(1), via I.5.7–10, printed pp.419–422.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
variable {G : Type*} [Group G] (S : DSystem .A3 G)

/-- All earlier-source geometry on the literal point, line and plane cosets. -/
theorem a3_source_geometry : Nonempty (A3Recognition.GeometryData S) := by
  classical
  refine ⟨{
    card_points := S.a3_points_card
    faithful_points := S.a3_faithful_points
    card_lines := S.a3_point_lines_card S.basePoint
    card_planes := S.a3_point_planes_card S.basePoint
    line_points := S.a3_line_points
    point_line_plane := fun _ _ _ => S.point_line_plane
    planes := fun π => ?_
    cover := fun l => ?_ }⟩
  · let f := (S.exists_fanoPlaneResidue π.val).some
    exact ⟨f.points, f.lines, f.incident⟩
  · obtain ⟨π, hx, hl⟩ := S.a3_plane_cover S.basePoint l
    exact ⟨⟨π, hx⟩, hl⟩

/-- The point core has a nontrivial action on the other two points of a line. -/
theorem a3_point_core_ne_bot : S.Q 0 ≠ ⊥ := by
  intro h
  exact S.a3_point_core_not_le_lineCore (h ▸ bot_le)

include S in
/-- I.5.1(1), with the actual binary projective special linear carrier. -/
theorem a3_source_recognition :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨d⟩ := a3_source_geometry S
  exact ⟨A3Recognition.equivPSL4_of_geometry d S.a3_point_core_ne_bot⟩

end Quasithin.I5.DSystem
