module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.Noncollinear
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointConnectivity
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreLineAction

/-!
# Actual two-step noncollinear configurations

The connected original point graph and the existence of a noncollinear
point force a two-edge path whose endpoints are noncollinear. Its two
original lines cannot lie in one plane, since the Fano plane makes their
endpoints collinear. These are the initial geodesics used in I.5.9(3),
with the literal lines and point-core adjustment action retained.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def CoplanarLines (l m : S.Line) : Prop := ∃ π : S.Plane, S.Inc l π ∧ S.Inc m π

theorem collinear_of_coplanar_lines {x z : S.Point} {l m : S.Line}
    (hx : S.Inc x l) (hz : S.Inc z m) (hplane : S.CoplanarLines l m) :
    S.Collinear x z := by
  obtain ⟨π, hl, hm⟩ := hplane
  exact S.collinear_of_common_plane (S.point_line_plane hx hl) (S.point_line_plane hz hm)

theorem exists_two_step_noncollinear (x : S.Point) :
    ∃ y z : S.Point, S.pointGraph.Adj x y ∧ S.pointGraph.Adj y z ∧ ¬ S.Collinear x z := by
  classical
  by_contra! h
  obtain ⟨z, hz⟩ := S.c3_exists_noncollinear x
  have hr := S.pointGraph_connected.preconnected x z
  have ht := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
  have hc : S.Collinear x z := by
    clear hz hr
    induction ht with
    | refl => exact S.collinear_refl x
    | @tail y z hy hyz ih =>
      by_cases he : x = y
      · rw [he]
        exact hyz.2
      · exact h y z ⟨he, ih⟩ hyz
  exact hz hc

theorem exists_noncoplanar_two_line_path (x : S.Point) :
    ∃ y z : S.Point, ∃ l m : S.Line,
      x ≠ y ∧ y ≠ z ∧ S.Inc x l ∧ S.Inc y l ∧ S.Inc y m ∧ S.Inc z m ∧
        ¬ S.Collinear x z ∧ ¬ S.CoplanarLines l m := by
  obtain ⟨y, z, hxy, hyz, hxz⟩ := S.exists_two_step_noncollinear x
  obtain ⟨l, hxl, hyl⟩ := hxy.2
  obtain ⟨m, hym, hzm⟩ := hyz.2
  exact ⟨y, z, l, m, hxy.1, hyz.1, hxl, hyl, hym, hzm, hxz,
    fun h => hxz (S.collinear_of_coplanar_lines hxl hzm h)⟩

end Quasithin.I5.DSystem
