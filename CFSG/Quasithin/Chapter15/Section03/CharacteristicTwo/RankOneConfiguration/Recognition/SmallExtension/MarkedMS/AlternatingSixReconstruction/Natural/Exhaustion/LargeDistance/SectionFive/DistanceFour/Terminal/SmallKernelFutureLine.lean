module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# Backward-kernel normalization using a future critical path

A failed normalization produces an order-two commutator line in the backward,
midpoint and endpoint seeds. If the line is fixed at the starting vertex, the
future generating edge also fixes it: its edge core fixes the starting vertex,
and its endpoint seed lies in the original endpoint core. The first backward
transporter then carries fixedness to the original endpoint, contradicting the
critical predecessor-kernel obstruction.

This retains the entire backward kernel and all central attachments. The
future path and its literal generation and transport identities remain explicit.
Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Future generation transfers fixedness of the actual failure line to the
critical endpoint and forces full backward-kernel normalization. -/
theorem small_backward_kernel_normalized_of_future_line_fixed
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4)
    {a z c y : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hcCol : color d.radical c = false)
    (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (r : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) y)
    (hr2 : r.walk.getVert 2 = z)
    (hfuture : Q d.radical (p.walk.getVert 1) ⊔ Z d.radical y =
      stabilizer d.radical (p.walk.getVert 2))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (hga : act d.radical g z = a)
    (hline : ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),
      Z d.radical z ⊓ Q d.radical a⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_contra hbad
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let K := Z d.radical c ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical a
  let H := ⁅K,F⁆
  obtain ⟨_,hHcard,hHseeds⟩ :=
    small_backward_kernel_nonnormal_three_seed_line s hc hb p hsmall hcCol hca hbad
  change Nat.card H = 2 at hHcard
  change H ≤ Z d.radical c ⊓ Z d.radical v ⊓ Z d.radical z at hHseeds
  have hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := hline
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hTGa : Q d.radical (p.walk.getVert 1) ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hYQz : Z d.radical y ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt d.radical y ((replacementGeometry h d).exists_critical y r.end_color)
    rw [(replacementGeometry h d).distance_constant y r.end_color,←hr2,
      SimpleGraph.dist_comm,r.dist_end,hrl]
    exact hb2
  have hcentv : H ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hfuture]
    exact sup_le (hTGa.trans (le_centralizer_iff.mp hcenta))
      (le_centralizer_iff.mp ((hHseeds.trans inf_le_right).trans
        ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z p.end_color)).trans
          (centralizer_le hYQz))))
  have hrestore : act d.radical g⁻¹ a = z := by
    rw [←hga,←act_mul,mul_inv_cancel,act_one]
  have hcentz : H ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [←hrestore,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hcenta).trans
      (map_centralizer_le_centralizer_image _ _)
    have hf : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hcentv hg))
    simpa only [inv_inv,hf,Subgroup.coe_map] using hh
  have hKQa : K ≤ Q d.radical a := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcCol)
    rw [(replacementGeometry h d).distance_constant c hcCol]
    exact hca.trans_lt hb2
  have hKpre : K ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [hl]
    exact inf_le_right
  have hnon : ⁅Z d.radical z ⊓ Q d.radical a,K⁆ ≠ ⊥ := by
    rw [commutator_comm]
    intro he
    change H = ⊥ at he
    rw [he,card_bot] at hHcard
    omega
  exact critical_predecessor_kernel_noncentral s hc hb2 p hsmall K hKQa hKpre hnon
    (by rwa [commutator_comm])

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

