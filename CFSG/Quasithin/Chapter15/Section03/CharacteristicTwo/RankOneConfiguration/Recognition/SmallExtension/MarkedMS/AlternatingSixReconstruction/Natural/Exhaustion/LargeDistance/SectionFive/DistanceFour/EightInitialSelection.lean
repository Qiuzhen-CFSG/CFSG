module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightUnequal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightBaumann
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection

/-!
# Initial selection in every natural A6 distance-four branch

The remaining non-elementary image-eight case has equal or unequal edge
movers. Both cases supply a generating backward critical path from a
strict slice. If no nonabelian selected path existed, both midpoint slices
would be strict. A first backward shift makes the whole radius escape;
the reciprocal path makes the forward slice strict. A second shift then
has both endpoints in the selected orbit span, proving that span nonabelian.

The final theorem combines image eight with the established elementary
and image-sixteen selections on the literal minimum characteristic
replacement. It retains both moving covers and all central attachments.
It supplies the initial-selection premise to the independent selected
terminal family; the terminal contradiction is still required for the
complete DistanceFourInput.
Source: MS93 (5.7)--(5.8), pp.919--920, and (5.12), p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightInitialSelection
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Both neighboring-mover cases give the same original backward path. -/
theorem backward_shift_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hmodel := EightBaumann.three_duad_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard (by omega : 2 < replacementDistance h d)
  by_cases he : SmallMover.join (U d.radical delta) (Q d.radical delta)
      (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4
  · exact EightEqual.equal_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      hne hcard (by omega) hmodel p hsmall hdelta he hstrict
  · exact EightUnequal.unequal_backward_shift_knownSimple hne hcard hb hmodel p hsmall hdelta he hstrict

include e hz hn in
/-- A strict forward slice with arbitrary neighboring movers supplies initial
nonabelian large-slice selection, including both full moving covers. -/
theorem large_forward_initial_selection_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  refine ⟨z,p,?_,hstrict⟩
  by_cases hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))
  · exact large_image_selected_span_nonabelian s hc hb p hlarge
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq,hover⟩ :=
    backward_shift_knownSimple hne hcard hb p hsmall hct hstrict
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hstart : Z d.radical (act d.radical g (p.walk.getVert 2)) ≤ P := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan d.radical _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _
        ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
  have hend : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ P := by
    rw [hl]
    exact Z_le_localZSpan d.radical _ _
  intro hzero
  exact critical_Z_commutator_ne_bot s hc q
    (le_bot_iff.mp ((commutator_mono hstart hend).trans_eq hzero))

include e hz hn in
/-- Every non-elementary order-eight radical image has an initial nonabelian large-slice
critical path at distance four. Both moving covers and the full central
attachments remain in the literal minimum characteristic replacement. -/
theorem initial_selection_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  classical
  by_contra hno
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hlarge := (initial_selection_or_large_midpoint_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb).resolve_left hno
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨delta,hdelta,hstrict⟩ := SixteenEqual.strict_neighbor_at_first_edge hb p (hlarge _ _ p).1
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    by_contra! hlargeimage
    exact hno (exists_nonabelian_large_slice_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p (large_image_selected_span_nonabelian s hc hb p hlargeimage))
  obtain ⟨t,hat,g,hg,hgt,hct,_,_,q,_,_⟩ :=
    backward_shift_knownSimple hne hcard hb p hsmall hdelta hstrict
  have hout : ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert 2) := by
    intro htrap
    apply q.critical.2
    rw [hl]
    exact (neighbor_seed_le_radius hat hct).trans htrap
  obtain ⟨w,r,hr⟩ := radius_escape_reciprocal_path s hc hb p hout
  have hforward : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
    simpa only [hr] using (hlarge _ _ r).1
  exact hno (large_forward_initial_selection_knownSimple hne hcard hb p hforward)


include e hz hn in
/-- Initial nonabelian large-slice selection in every image and cover case
of the original natural minimum characteristic replacement at distance four. -/
theorem initial_selection_all_knownSimple
    (hb : replacementDistance h d = 4) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  rcases SixteenEqual.initial_selection_or_eight_knownSimple
    (e := e) (hz := hz) (hn := hn) hb with hsel | ⟨_,hne,_,hcard⟩
  · exact hsel
  · exact initial_selection_knownSimple hne hcard hb

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightInitialSelection
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
