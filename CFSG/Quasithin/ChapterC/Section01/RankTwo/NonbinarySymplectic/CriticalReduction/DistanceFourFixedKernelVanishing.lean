module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootLayers
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# Vanishing on the actual second residual selector

For the source-correct full actor W = Z_v intersect Q_a and the full
intersection A = X_e intersect Q_u, fixed-radius bounds put [W,A] in both
D_u and D_a. The same residual element y in L_u sending a to v fixes this
commutator and transfers its L_a-fixedness to L_v-fixedness. Full-seed
natural-cover vanishing then kills it, including all central attachments.

The internal imports reuse fixed-radius transport and full-seed vanishing.
No failed comparison, mover equality, image bound or first orbit is assumed.
Source: the restricted-kernel step of MS93 (5.12), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual second residual selector makes the two full source kernel
intersections commute in the fixed-radius distance-four branch. -/
theorem Input.replacement_distance_four_fixed_kernel_commutator_eq_bot
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (y : FreeAmalgam d.radical) (hy : y ∈ Ltilde d.radical u)
    (hya : act d.radical y a=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅Z d.radical v ⊓ Q d.radical a,
      X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆=⊥ := by
  let e := path.walk.getVert 2
  let W := Z d.radical v ⊓ Q d.radical a
  let A := X d.radical e ⊓ Q d.radical u
  let D := ⁅W,A⁆
  have hfixed_u := radius_fixed_at d path.start_color back.start_color hfixed
  have hWVu : W ≤ V d.radical u := inf_le_left.trans
    (le_sup_left.trans (neighbor_seed_join_le_radius hut hvt))
  have hDu : D ≤ centralizer (Ltilde d.radical u : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono hWVu inf_le_right).trans hfixed_u).trans inf_le_right
  have hea : (cosetGraph d.radical).dist e a=2 := by
    rw [←hmid,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (back.walk.getVert 2) (path.walk.getVert 2)=2
    rw [back.dist_end,back.length_eq_b,hb]
  have hAVa : A ≤ V d.radical a := inf_le_left.trans
    ((h.replacement_distance_four_X_eq_Z d geometry hb back.end_color).le.trans
      (le_iSup_of_le e (le_iSup_of_le hea.le le_rfl)))
  have hDa : D ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    change ⁅W,A⁆ ≤ _
    rw [commutator_comm]
    exact ((commutator_mono hAVa inf_le_right).trans hfixed).trans inf_le_right
  have hDy : D.map (MulAut.conj y⁻¹).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hDu ((Ltilde d.radical u).inv_mem hy)))
  have hDv : D ≤ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hDa).trans
      (map_centralizer_le_centralizer_image _ _)
    change D.map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer
      ((Ltilde d.radical a).map (MulAut.conj y⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    rwa [hDy,←Ltilde_act,hya] at hh
  have hv : color d.radical v=false := by
    rw [←hya,action_preserves_color]
    exact path.start_color
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hz := (full_seed_commutator_fixed_iff h d geometry (by omega) hv A W hAS inf_le_left).mp
    (by rw [commutator_comm]; exact hDv)
  change ⁅W,A⁆=⊥
  rw [commutator_comm,hz]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
