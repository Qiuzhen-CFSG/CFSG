module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedResidualLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallOpposite

/-!
# Opposite fixation contradicts the full mixed failure line

The marked failure line is fixed at the starting vertex. Opposite-midpoint
fixation transports through the retained local and edge actors to the backward
vertex. If the full backward seed escapes the conjugate midpoint core, the
literal four-edge walk through the starting vertex is critical, and the reverse
kernel noncentrality theorem applies. If the seed is trapped, faithfulness on
the full natural cover makes its central movement trivial instead.

No equality between the original and conjugate backward kernels is needed.
The private import reuses the full-cover faithful central-movement calculation.
Source: MS93 (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Fixation at the conjugate midpoint is impossible for the nonzero full
mixed failure line already fixed at the starting vertex. -/
theorem conjugate_failure_line_not_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hcard : Nat.card (⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
      Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) = 2)
    (hedge : ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
      Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆ ≤ Z d.radical q.edge)
    (hfixa : ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
      Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hfixc : ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
      Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆ ≤
        centralizer (stabilizer d.radical (act d.radical x (p.walk.getVert 2)) :
          Set (FreeAmalgam d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hca : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    simpa only [hq2] using (q.path.dist_start (i := 2) (by omega)).le
  have hxa : act d.radical x a = a := hx
  have hcancel (v : Vertex d.radical) : act d.radical x⁻¹ (act d.radical x v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  let c := act d.radical x (p.walk.getVert 2)
  let F := Z d.radical (act d.radical x z) ⊓ Q d.radical a
  let H := ⁅Z d.radical q.start ⊓ Q d.radical c,F⁆
  change Nat.card H = 2 at hcard
  change H ≤ Z d.radical q.edge at hedge
  change H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) at hfixa
  change H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) at hfixc
  have hmap : H.map (MulAut.conj x).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hfixa hx))
  have hmid : H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj x).toMonoidHom) hfixc).trans
      (map_centralizer_le_centralizer_image _ _)
    change H.map (MulAut.conj x).toMonoidHom ≤
      centralizer ((stabilizer d.radical c).map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    have hcmap : (stabilizer d.radical c).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical (p.walk.getVert 2) := by
      simpa only [inv_inv,c,hcancel] using (stabilizer_act d.radical x⁻¹ c).symm
    rwa [hmap,hcmap] at hh
  have hHQ : H ≤ Q d.radical q.edge := by
    intro y hy
    have hz := hedge hy
    rw [Z,if_neg (by simp [q.edge_color])] at hz
    exact (mem_omegaCenter_iff.mp hz).1
  have hback := q.centrality_transfer H hHQ hfixa hmid
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hFQa : F ≤ Q d.radical a := inf_le_right
  have hFGback : F ≤ stabilizer d.radical q.start := hFQa.trans
    (Q_le_stabilizer_of_dist_le_two a q.start p.start_color q.path.start_color
      (by rwa [SimpleGraph.dist_comm]))
  have hFQc : F ≤ Q d.radical c := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _
      ((action_preserves_color d.radical _ _).trans p.end_color))
    rw [(replacementGeometry h d).distance_constant _
      ((action_preserves_color d.radical _ _).trans p.end_color)]
    change (cosetGraph d.radical).dist (act d.radical x z)
      (act d.radical x (p.walk.getVert 2)) < replacementDistance h d
    rw [dist_act,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hne : H ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  by_cases htrap : Z d.radical q.start ≤ Q d.radical c
  · have he : Z d.radical q.start ⊓ Q d.radical c = Z d.radical q.start := inf_eq_left.mpr htrap
    apply hne
    change ⁅Z d.radical q.start ⊓ Q d.radical c,F⁆ = ⊥
    rw [he]
    apply seed_central_commutator_eq_bot s hc q.path.start_color F hFGback
    simpa only [H,he] using hback
  · have hat : Adjacent d.radical a (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    have htc : Adjacent d.radical (p.walk.getVert 1) (p.walk.getVert 2) :=
      (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega))
    have hatx : Adjacent d.radical a (act d.radical x (p.walk.getVert 1)) := by
      simpa only [hxa] using (adjacent_act_iff d.radical x _ _).mpr hat
    have htxc : Adjacent d.radical (act d.radical x (p.walk.getVert 1)) c :=
      (adjacent_act_iff d.radical x _ _).mpr htc
    let w : (cosetGraph d.radical).Walk q.start c :=
      .cons ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical q.adjacent_start))
          (.cons ((cosetGraph_adj d.radical _ _).mpr hatx)
            (.cons ((cosetGraph_adj d.radical _ _).mpr htxc) .nil)))
    have hw : w.length = 4 := rfl
    have hmin := criticalDistance_le d.radical q.start
      ((replacementGeometry h d).exists_critical _ q.path.start_color) htrap
    rw [(replacementGeometry h d).distance_constant _ q.path.start_color] at hmin
    have hdist : (cosetGraph d.radical).dist q.start c = replacementDistance h d :=
      le_antisymm (by have hh := SimpleGraph.dist_le w; rw [hw] at hh; omega) hmin
    let r : CriticalPath d.radical (replacementGeometry h d) q.start c := {
      start_color := q.path.start_color
      walk := w
      shortest := hw.trans (hb.symm.trans hdist.symm)
      critical := ⟨by rw [(replacementGeometry h d).distance_constant _ q.path.start_color]; exact hdist,htrap⟩ }
    let rr : CriticalPath d.radical (replacementGeometry h d) c q.start := {
      start_color := r.end_color
      walk := r.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,r.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse_pair s hc r }
    have hpre : rr.walk.getVert (rr.walk.length-2) = a := by
      change w.reverse.getVert (w.reverse.length-2) = a
      rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hw]
      rfl
    exact critical_predecessor_kernel_noncentral s hc hb2 rr
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb rr)
      F hFQc (by simpa only [hpre] using hFQa) hne hback

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
