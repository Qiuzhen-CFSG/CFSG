module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallIntersection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelEdges

/-!
# Common-kernel normalization for the elementary cube

The failure line for a second backward kernel lies in the two endpoint
seeds and the first predecessor seed.  The cube radius bound puts the same
line in the first backward seed.  Two strict seed-intersection triples then
make the line central at the two component stabilizers.  The first
transporter carries this centrality to the endpoint of the first critical
path, where the predecessor-kernel obstruction gives a contradiction.

This is the source-(5.12)(1) common-kernel step.  The second selector is
left as an explicit input so that both moving covers and all central
attachments remain visible to its consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Two strict compatible triples normalize the first selected full kernel. -/
theorem cube_two_strict_triples_normalize
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a v c b : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c v)
    (hq2 : q.walk.getVert 2 = a)
    (hqsmall : (Q d.radical v).relIndex (Z d.radical c) < 4)
    (hbc : (cosetGraph d.radical).dist b c ≤ 2)
    (hbCol : color d.radical b = false)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g v = c)
    (hfirst : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical v ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hsecond : Z d.radical b ⊓ Z d.radical c ⊓ Z d.radical a ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) :
    Z d.radical v ≤ normalizer
      (((Z d.radical b ⊓ Q d.radical a) ⊔ Z d.radical c :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_contra hbad
  have hb2 : 2 < replacementDistance h d := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let K := Z d.radical b ⊓ Q d.radical a
  let F := Z d.radical v ⊓ Q d.radical c
  let H := ⁅K,F⁆
  have hca : (cosetGraph d.radical).dist b c ≤ 2 := hbc
  have hfailure := small_backward_kernel_nonnormal_three_seed_line s hc hb q hqsmall hbCol hca
  rw [hq2] at hfailure
  obtain ⟨_,hHcard,hHseeds⟩ := hfailure hbad
  change Nat.card H = 2 at hHcard
  change H ≤ Z d.radical b ⊓ Z d.radical a ⊓ Z d.radical v at hHseeds
  have hZbV : Z d.radical b ≤ V d.radical c :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hbc)
  have hHc : H ≤ Z d.radical c := by
    exact (commutator_mono (inf_le_left.trans hZbV) inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb2 u hfull.le c q.start_color)
  have hHa : H ≤ Z d.radical a := hHseeds.trans (inf_le_left.trans inf_le_right)
  have hHv : H ≤ Z d.radical v := hHseeds.trans inf_le_right
  have hfirst' : H ≤ Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical v :=
    le_inf (le_inf hHc hHa) hHv
  have hcenta : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    hfirst'.trans hfirst
  have hsecond' : H ≤ Z d.radical b ⊓ Z d.radical c ⊓ Z d.radical a :=
    le_inf (le_inf (hHseeds.trans (inf_le_left.trans inf_le_left)) hHc) hHa
  have hcentc : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) :=
    hsecond'.trans hsecond
  have hrestore : act d.radical g⁻¹ c = v := by
    rw [←hgc,←act_mul,mul_inv_cancel,act_one]
  have hcentv : H ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    rw [←hrestore,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hcentc).trans
      (map_centralizer_le_centralizer_image _ _)
    have hf : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hcenta hg))
    simpa only [inv_inv,hf,Subgroup.coe_map] using hh
  have hKQc : K ≤ Q d.radical c := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical b
      ((replacementGeometry h d).exists_critical b hbCol)
    rw [(replacementGeometry h d).distance_constant b hbCol]
    exact hbc.trans_lt hb2
  have hKQpre : K ≤ Q d.radical (q.walk.getVert (q.walk.length - 2)) := by
    rw [show q.walk.length - 2 = 2 by omega,hq2]
    exact inf_le_right
  have hnon : ⁅Z d.radical v ⊓ Q d.radical c,K⁆ ≠ ⊥ := by
    rw [commutator_comm]
    intro he
    change H = ⊥ at he
    rw [he,card_bot] at hHcard
    omega
  exact critical_predecessor_kernel_noncentral s hc hb2 q hqsmall K hKQc hKQpre hnon
    (by rw [commutator_comm]; exact hcentv)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
