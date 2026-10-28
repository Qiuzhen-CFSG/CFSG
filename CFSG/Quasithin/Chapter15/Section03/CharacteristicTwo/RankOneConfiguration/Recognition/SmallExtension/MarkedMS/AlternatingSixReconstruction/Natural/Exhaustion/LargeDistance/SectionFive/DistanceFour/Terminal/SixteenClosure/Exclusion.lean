module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.DerivedFixer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RemainingSixteen
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.SecondFailure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.DerivedFailure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The unequal image-sixteen source contradiction

The full backward failure line equals the source moving-U/full-X line.
The index-two source generation estimate fixes this line under the entire
derived starting stabilizer. Its placement in the original full seed lets
the unequal-mover derived fixer act, contradicting the second source-line
nonfixation. All full central attachments remain in the original graph.

The private obstruction import reuses the established strict normalized-actor
contradiction without widening the source module's public interface.

Source: MS93 (5.5)(b,c), (5.12)(1), printed pp.915,924--925.
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

private theorem second_source_line_derived_fixed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a v c b : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c v)
    (hq2 : q.walk.getVert 2 = a)
    (r : CriticalPath d.radical (replacementGeometry h d) b a)
    (hr2 : r.walk.getVert 2 = c)
    (hrne : edgeMover b (r.walk.getVert 1) ≠ edgeMover c (r.walk.getVert 1))
    (hrgen : Q d.radical (r.walk.getVert 1) ⊔ Z d.radical v = stabilizer d.radical c)
    (hrstrict : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical b)) :
    let H := ⁅U d.radical b ⊓ Q d.radical a,X d.radical v ⊓ Q d.radical c⁆
    H ≤ Z d.radical a ∧
      H ≤ centralizer ((⁅stabilizer d.radical c,stabilizer d.radical c⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q
  have hrsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hVa : Z d.radical v ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v q.end_color)
    rw [(replacementGeometry h d).distance_constant _ q.end_color,SimpleGraph.dist_comm,
      ←hq2,q.dist_end,hql]
    exact hb2
  have hfix : ⁅Z d.radical b,Z d.radical a⁆ ≤
      centralizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a r.end_color)).trans
          (centralizer_le hVa))
  have hbad : ¬ Z d.radical v ≤ normalizer
      (((Z d.radical b ⊓ Q d.radical a) ⊔ Z d.radical c :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hnorm
    exact strict_small_normalized_actor_false s hc hb r hrsmall (Z d.radical v)
      (by simpa only [hr2] using hrgen) (by simpa only [hr2] using hrstrict)
      (by simpa only [hr2] using hnorm) hfix
  have he := small_backward_failure_line_eq_source (c := b) s hc hb q hsmall
  rw [hq2] at he
  have heq := he r hr2 hbad
  have hsource := strict_small_backward_source_failure_knownSimple
    (e := e) (hz := hz) (hn := hn) (c := b) hb q
  rw [hq2] at hsource
  have hseeds := (hsource r hr2 hrgen hrstrict).2.1
  have hderived := unequal_failure_line_derived_fixed_knownSimple (c := b) hcard hb q hsmall
  rw [hq2] at hderived
  have hd := hderived r hr2 hrne hrgen hbad
  rw [heq] at hd
  exact ⟨hseeds.trans (inf_le_left.trans inf_le_right),hd⟩

private theorem second_source_configuration_false_knownSimple
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
      (U d.radical b)) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hct : Adjacent d.radical c (q.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a (q.walk.getVert 1) := by
    simpa only [hq2] using adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hnot := (second_source_line_not_fixed_knownSimple
    hcard hb p q hq2 hne hcross hgen hstrict g hg hgc r hr2 hrne hrgen hrstrict).2.2.2
  have hdata := second_source_line_derived_fixed_knownSimple
    hcard hb q hq2 r hr2 hrne hrgen hrstrict
  have hJ : edgeMover c (q.walk.getVert 1) ≤ stabilizer d.radical c :=
    (SmallMover.join_le _ _ _ _).trans
      (show Q d.radical (q.walk.getVert 1) ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hfixJ := hdata.2.trans (centralizer_le (commutator_mono hJ hJ))
  apply hnot
  exact (le_inf hdata.1 hfixJ).trans (unequal_derived_fixer_knownSimple
    hcard hb2 p.start_color hat hct hne
      (sixteen_small_omega_centrally_generated_knownSimple hcard hb a p.start_color))

/-- The actual strict unequal image-sixteen source configuration is
impossible: its second source line is both fixed and not fixed by the same
selected mover. All path-selection and fixation inputs are constructed. -/
theorem strict_false_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))) : False := by
  obtain ⟨c,b,q,r,hq2,hr2,⟨g,hg,hgc,_⟩,_,hne,hcross,hgen,hi,hrne,hrgen,hrstrict,_⟩ :=
    selected_second_source_line_knownSimple hcard hb p hstrict
  exact second_source_configuration_false_knownSimple
    hcard hb p q hq2 hne hcross hgen hi g hg hgc r hr2 hrne hrgen hrstrict

/-- The original order-sixteen radical image cannot have critical distance
four, on either full moved cover and with every central attachment retained. -/
theorem sixteen_distance_four_false_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4) : False := by
  obtain ⟨z,p,_,hstrict⟩ := SixteenEqual.initial_selection_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard
  exact strict_false_knownSimple hcard hb p hstrict

include e hz hn in
/-- Critical distance four is impossible for the literal natural minimum
characteristic replacement, after all radical-image cases are discharged. -/
theorem distance_four_false_knownSimple
    (hb : replacementDistance h d = 4) : False := by
  exact sixteen_distance_four_false_knownSimple
    (RemainingSixteen.image_sixteen_knownSimple (e := e) (hz := hz) (hn := hn) hb) hb

/-- The actual source-(5.12) distance-four input, with the supplied symmetric
action and central layer preserved by the original assembly adapter. -/
theorem distanceFourInput_knownSimple : DistanceFourInput.{u} KnownSimple.IsKnownSimple := by
  apply RemainingSixteen.distanceFourInput_of_sixteen
  intro G _ _ L R h e hz hn d s _ hb hcard
  have hcard' : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16 := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hcard
  exact sixteen_distance_four_false_knownSimple hcard' hb

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
