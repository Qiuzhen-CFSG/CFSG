module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCentralObstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The literal distance-four comparison in the fixed-radius branch

The restricted failed-comparison commutator lies in [V_u,Q_u], hence in
D_u, and in Z_u, hence centralizes Q_u. It therefore centralizes G_u.
Its inclusion in the full critical commutator through a similarly puts it
in D_a and X_a, so it centralizes G_a. The actual second-selector conjugator
then contradicts the full-cover two-center obstruction.

This proves comparison (1) in MS93 (5.12), printed pp.924--925, under the
actual radius fixedness hypothesis. No first midpoint orbit, equality of
endpoint fixed kernels, or invariance of the restricted subgroup under a
selected mover is assumed. The internal import reuses only transport of
the literal fixed-radius hypothesis between vertices of the same color.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem fixed_core_centralizes_vertex
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ fixedCore d.radical a)
    (hQ : D ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical))) :
    D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hS : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) ha
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  apply le_centralizer_iff.mp
  rw [←hS]
  exact sup_le (le_centralizer_iff.mp (hD.trans inf_le_right)) (le_centralizer_iff.mp hQ)

/-- Radius fixedness proves the literal comparison for any compatible
backward path and the actual second-selector orbit, at every mover type. -/
theorem Input.replacement_distance_four_fixed_comparison
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
  by_contra hbad
  let e := path.walk.getVert 2
  let W := U d.radical v ⊓ Q d.radical z
  let A := X d.radical e ⊓ Q d.radical u
  let D := ⁅W,A⁆
  let C := ⁅Z d.radical u,Z d.radical e⁆
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hDC : D ≤ C :=
    (h.replacement_distance_four_root_comparison_of_failure d path hb back hut hvt hbad).1
  have hfixed_u := radius_fixed_at d path.start_color back.start_color hfixed
  have huv : (cosetGraph d.radical).dist v u ≤ 2 := neighbor_distance_le_two hut hvt
  have hUv : U d.radical v ≤ V d.radical u :=
    (U_le_Z v).trans (le_iSup_of_le v (le_iSup_of_le huv le_rfl))
  have hWVu : W ≤ V d.radical u :=
    inf_le_left.trans hUv
  have hDu : D ≤ fixedCore d.radical u :=
    (commutator_mono hWVu inf_le_right).trans hfixed_u
  have hDZu : D ≤ Z d.radical u := hDC.trans (critical_commutator_le_start_seed back)
  have hCu := fixed_core_centralizes_vertex h d geometry hb4 back.start_color D hDu
    (hDZu.trans (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes u back.start_color)))
  have hl := path.length_eq_b
  have hbl := back.length_eq_b
  have hua : (cosetGraph d.radical).dist u a=2 := by
    rw [←hmid]
    exact back.dist_start (by omega)
  have hea : (cosetGraph d.radical).dist e a=2 := by
    rw [SimpleGraph.dist_comm]
    exact path.dist_start (by omega)
  have hCV : C ≤ ⁅V d.radical a,V d.radical a⁆ :=
    commutator_mono (le_iSup_of_le u (le_iSup_of_le hua.le le_rfl))
      (le_iSup_of_le e (le_iSup_of_le hea.le le_rfl))
  have hDa : D ≤ fixedCore d.radical a := hDC.trans (hCV.trans
    ((commutator_mono le_rfl (geometry.V_le_Q (by omega) a path.start_color)).trans hfixed))
  have hDX : D ≤ X d.radical a := hDC.trans (hCV.trans
    (h.replacement_radius_commutator_bounds d geometry hb4 path.start_color u e).1)
  have hCa := fixed_core_centralizes_vertex h d geometry hb4 path.start_color D hDa
    (le_centralizer_iff.mp ((Q_le_centralizer_X d.radical a).trans (centralizer_le hDX)))
  exact (h.replacement_distance_four_comparison_not_two_centers d path hb back hut hvt
    y hy hya hbad) (le_inf hCa hCu)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
