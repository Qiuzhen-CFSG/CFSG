module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenUnequalFailureLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelFutureLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Selection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ResidualTerminal

/-!
# The actual second source line in the unequal image-sixteen branch

The first strict selection can be repeated at its starting vertex: transport
its unequal neighboring pair through the common edge, then use the crossed
backward selection. Thus both selections retain their literal transporters,
strict slices and source generating edges.

The second moving-U/full-X failure line has order two, lies in the original
edge seed, and is fixed by the first backward residual. If the first selected
mover fixed it as well, (5.5)(b) would make it central at the original vertex.
Residual/edge generation would then make it central at the backward vertex.
The original future path and transporter would force full-kernel
normalization, contradicting the second strict slice.

This is an obstruction reduction, not the source exclusion. Establishing the
missing mover fixation from the source hypotheses remains necessary. Both
moving covers and all full central attachments are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)(b,c), (5.12)(1), printed pp.915,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

include e hz hn in
/-- On two literal unequal strict selections, the second source line is
residual-fixed and edge-contained, but cannot be fixed by the first selected
mover. This identifies the exact remaining action obligation in (5.12)(1). -/
theorem second_source_line_not_fixed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z c b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hne : edgeMover c (q.walk.getVert 1) ≠ edgeMover a (q.walk.getVert 1))
    (hcross : edgeMover a (p.walk.getVert 1) ⊔ edgeMover a (q.walk.getVert 1) =
      stabilizer d.radical a)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (r : CriticalPath d.radical (replacementGeometry h d) b a)
    (hr2 : r.walk.getVert 2 = c)
    (hrne : edgeMover b (r.walk.getVert 1) ≠ edgeMover c (r.walk.getVert 1))
    (hrgen : Q d.radical (r.walk.getVert 1) ⊔ Z d.radical (p.walk.getVert 2) =
      stabilizer d.radical c)
    (hrstrict : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical b)) :
    let H := ⁅U d.radical b ⊓ Q d.radical a,
      X d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆
    Nat.card (H : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      H ≤ Z d.radical (p.walk.getVert 1) ∧
      H ≤ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer (edgeMover a (q.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q
  have hrsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
  have hbc : (cosetGraph d.radical).dist b c ≤ 2 := by
    rw [←hr2,r.dist_start (by omega)]
  have hct : Adjacent d.radical c (q.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a (q.walk.getVert 1) := by
    simpa only [hq2] using adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hab : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hVa : Z d.radical (p.walk.getVert 2) ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ q.end_color)
    rw [(replacementGeometry h d).distance_constant _ q.end_color,SimpleGraph.dist_comm,
      p.dist_start (by omega)]
    exact hb2
  have hfix : ⁅Z d.radical b,Z d.radical a⁆ ≤
      centralizer (Z d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
          (centralizer_le hVa))
  have hbad : ¬ Z d.radical (p.walk.getVert 2) ≤ normalizer
      (((Z d.radical b ⊓ Q d.radical a) ⊔ Z d.radical c :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hnorm
    exact strict_small_normalized_actor_false s hc hb r hrsmall
      (Z d.radical (p.walk.getVert 2)) (by simpa only [hr2] using hrgen)
      (by simpa only [hr2] using hrstrict) (by simpa only [hr2] using hnorm) hfix
  have he := small_backward_failure_line_eq_source (c := b) s hc hb q hsmall
  rw [hq2] at he
  have heq := he r hr2 hbad
  have hsource := strict_small_backward_source_failure_knownSimple
    (e := e) (hz := hz) (hn := hn) (c := b) hb q
  rw [hq2] at hsource
  have hcardH := (hsource r hr2 hrgen hrstrict).1
  have hedge := sixteen_unequal_second_failure_line_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb p q hq2 hne hgen hstrict r hr2 hbad
  have hres := SixteenSmall.sixteen_unequal_small_failure_line_residual_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) (c := b) hcard hb q hsmall
  rw [hq2] at hres
  have hresH := hres r hr2 hrne hrgen hbad
  rw [heq] at hedge hresH
  refine ⟨hcardH,hedge,hresH,?_⟩
  intro hfixed
  have hcenta := (le_inf hedge hfixed).trans (crossed_edge_fixed_kernel p.start_color hab hcross)
  have hcentc : ⁅U d.radical b ⊓ Q d.radical a,
      X d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆ ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←residual_edge_generation (h := h) q.start_color hct]
    exact sup_le (le_centralizer_iff.mp hresH)
      ((show Q d.radical (q.walk.getVert 1) ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (le_centralizer_iff.mp hcenta))
  have hf := small_backward_kernel_normalized_of_future_line_fixed
    (y := z) s hc hb q hsmall r.start_color hbc
  rw [hq2] at hf
  exact hbad (hf p rfl hgen g hg hgc (by rwa [heq]))

include e hz hn in
/-- The original alpha-based strict path produces the complete second
source-line obstruction without any extra mover-fixation, normalization or
opposite-slice premise. The terminal contradiction is still open. -/
theorem selected_second_source_line_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))) :
    ∃ c b : Vertex d.radical,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
      ∃ r : CriticalPath d.radical (replacementGeometry h d) b (alpha d.radical),
        q.walk.getVert 2 = alpha d.radical ∧ r.walk.getVert 2 = c ∧
        (∃ g ∈ stabilizer d.radical (alpha d.radical),
          act d.radical g (p.walk.getVert 2) = c ∧
          act d.radical g (p.walk.getVert 1) = q.walk.getVert 1) ∧
        (∃ j ∈ stabilizer d.radical (q.walk.getVert 1),
          act d.radical j (alpha d.radical) = c ∧
          ∃ k ∈ stabilizer d.radical c,
            act d.radical k (act d.radical j c) = b ∧
            act d.radical k (q.walk.getVert 1) = r.walk.getVert 1) ∧
        edgeMover c (q.walk.getVert 1) ≠ edgeMover (alpha d.radical) (q.walk.getVert 1) ∧
        edgeMover (alpha d.radical) (p.walk.getVert 1) ⊔
          edgeMover (alpha d.radical) (q.walk.getVert 1) = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        edgeMover b (r.walk.getVert 1) ≠ edgeMover c (r.walk.getVert 1) ∧
        Q d.radical (r.walk.getVert 1) ⊔ Z d.radical (p.walk.getVert 2) = stabilizer d.radical c ∧
        2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical b) ∧
        let H := ⁅U d.radical b ⊓ Q d.radical (alpha d.radical),
          X d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆
        Nat.card (H : Subgroup (FreeAmalgam d.radical)) = 2 ∧
          H ≤ Z d.radical (p.walk.getVert 1) ∧
          H ≤ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) ∧
          ¬ H ≤ centralizer
            (edgeMover (alpha d.radical) (q.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hg,q,hq1,hq2,hne,hcross,hgen,hi,_⟩ :=
    selected_source_failure_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hstrict
  let c := act d.radical g (p.walk.getVert 2)
  let t := q.walk.getVert 1
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    simpa only [hq2] using adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hne' : edgeMover c t ≠ edgeMover (alpha d.radical) t := by
    simpa only [t,hq1] using hne
  obtain ⟨j,hj,hja⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm d.radical hat) (adjacent_symm d.radical hct)
  have hjt : act d.radical j t = t := hj
  have hd : Adjacent d.radical (act d.radical j c) t := by
    simpa only [hjt] using (adjacent_act_iff d.radical j _ _).mpr hct
  have hiD : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j c)) := by
    have hh : 2 < (B d.radical (act d.radical j (alpha d.radical))
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j c)) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 j (alpha d.radical) rfl,U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hi
    simpa only [hja] using hh
  have hnD : edgeMover (act d.radical j c) t ≠ edgeMover c t := by
    intro he
    apply hne'
    apply map_injective (f := (MulAut.conj j⁻¹).toMonoidHom) (MulAut.conj j⁻¹).injective
    dsimp only
    rw [SmallMover.join_map _ (MulAut.conj j⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj j⁻¹).injective,
      ←U_act,←Q_act,←Q_act,←U_act,←Q_act,hja,hjt]
    exact he
  have back := unequal_backward_crossed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb q
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q) hd hnD hiD
  rw [show q.walk.length - 2 = 2 by omega,hq2] at back
  obtain ⟨k,hk,hct',hbt',hneB,_,hiB,hgenB,r,hr1,hover⟩ := back
  have hr2 : r.walk.getVert 2 = c := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  refine ⟨c,act d.radical k (act d.radical j c),q,r,hq2,hr2,
    ⟨g,hg,rfl,hq1.symm⟩,⟨j,hj,hja,k,hk,rfl,hr1.symm⟩,
    hne',?_,?_,hi,?_,?_,hiB,?_⟩
  · simpa only [hq1] using hcross
  · simpa only [hq1] using hgen
  · simpa only [hr1] using hneB
  · simpa only [hr1] using hgenB
  exact second_source_line_not_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb p q hq2
    (by simpa only [t] using hne')
    (by simpa only [hq1] using hcross)
    (by simpa only [hq1] using hgen) hi g hg rfl r hr2
    (by simpa only [hr1] using hneB) (by simpa only [hr1] using hgenB) hiB

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
