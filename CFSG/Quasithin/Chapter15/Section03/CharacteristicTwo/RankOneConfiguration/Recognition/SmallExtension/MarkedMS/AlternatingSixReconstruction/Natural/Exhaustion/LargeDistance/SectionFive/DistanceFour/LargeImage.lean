module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.StrictSlices
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SmallSlice

/-!
# Radius escape and selected nonabelianness for large critical images

For a critical pair with seed image of order at least four, the controlled
reverse subactor escapes the starting two-core and centralizes the radius
intersection modulo the full starting seed. If the whole starting radius
lay in the predecessor core, its normal section modulo the seed would be
fixed by this actor, hence by the two-residual. This contradicts the proved
nonzero residual movement of the radius. Thus radius escape holds for every
radical image, without a Sylow or point-core hypothesis.

At distance four, a seed witnessing this escape gives a reciprocal critical
path from the midpoint through the original base. Source (2.2)(iv) on that
path makes the original forward seed eligible. If its selected span were
abelian, it would lie in the midpoint two-core; the same controlled actor
would then force it into the Baumann slice, contradicting eligibility.

The small-slice critical-image exclusion now applies without an independent
nonabelianness assumption: a large critical image forces a forward slice
larger than two. The final application gives both critical indices equal
to two from the small forward slice alone. Every group, kernel and path is
on the literal natural replacement, with both moving covers and the full
central attachments retained. Large-slice exclusion, initial selection in
the small-image case, and the whole residual-core upper estimates remain
open; these results do not assert DistanceFourInput.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.2)(iv), printed pp.856--857, the controlled actor of (5.2)(i),
pp.913--914, radius escape in (5.8), pp.919--920, and the large-image branch
of (5.12)(2), pp.925--926. The direct radius argument uses the actual
restricted subactor, not an enlarged endpoint-commutator bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The controlled endpoint subactor forces escape of the whole radius from
the predecessor core, for every radical image and every distance above two. -/
theorem large_image_radius_escape
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨W,hWU,_,hindex,hcomm⟩ := critical_radius_restricted_commutator s hc hb p hlarge
  have hWG : W ≤ stabilizer d.radical a := (hWU.trans (DistanceEight.U_le_Z d.radical _)).trans
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical)
  have hWQ : ¬ W ≤ Q d.radical a := by
    intro hWQ
    have he := relIndex_eq_one.mpr hWQ
    omega
  intro hVQ
  rw [inf_eq_left.mpr hVQ] at hcomm
  have hVB := normalized_radius_le_slice_of_actor_at s hb p.start_color
    (V d.radical a) W le_rfl (DistanceEight.V_normalized d.radical a) hWG hWQ hcomm
  apply radius_moving_not_le_Z s hc hb a p.start_color
  change ⁅V d.radical a,Ltilde d.radical a⁆ ≤ Z d.radical a
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl v hv
  exact ((mem_B_iff d.radical a _
    ((replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb)) v).mp (hVB hv)).2 l hl

include s in
/-- At distance four, a seed witnessing radius escape produces a reciprocal
critical path through the same base, with its midpoint retained literally. -/
theorem radius_escape_reciprocal_path
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hescape : ¬ V d.radical a ≤ Q d.radical (p.walk.getVert 2)) :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
      q.walk.getVert 2 = a := by
  classical
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hca : (cosetGraph d.radical).dist c a = 2 := by rw [SimpleGraph.dist_comm,hac]
  have hex : ∃ z, color d.radical z = false ∧
      (cosetGraph d.radical).dist z a ≤ 2 ∧ ¬ Z d.radical z ≤ Q d.radical c := by
    by_contra! hno
    exact hescape (NaturalStructure.Exclusion.radius_le_of_m_ball p.start_color _ hno)
  obtain ⟨z,hzCol,hza,hzQ⟩ := hex
  have hlo := criticalDistance_le d.radical z ((replacementGeometry h d).exists_critical z hzCol) hzQ
  rw [(replacementGeometry h d).distance_constant z hzCol] at hlo
  change replacementDistance h d ≤ (cosetGraph d.radical).dist z c at hlo
  have htri := (cosetGraph_connected d.radical).dist_triangle (u := z) (v := a) (w := c)
  have hzc : (cosetGraph d.radical).dist z c = 4 := by omega
  have hza2 : (cosetGraph d.radical).dist z a = 2 := by omega
  have haz : (cosetGraph d.radical).dist a z = 2 := by rw [SimpleGraph.dist_comm,hza2]
  let r : CriticalPath d.radical (replacementGeometry h d) z c :=
    CriticalPath.ofPair hzCol ⟨by rw [(replacementGeometry h d).distance_constant z hzCol]; exact hzc.trans hb.symm,hzQ⟩
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a z
  have hw2 : w.length = 2 := hw.trans hca
  have hv2 : v.length = 2 := hv.trans haz
  let q : CriticalPath d.radical (replacementGeometry h d) c z := {
    start_color := hcCol
    walk := w.append v
    shortest := by rw [SimpleGraph.Walk.length_append,hw2,hv2,SimpleGraph.dist_comm,hzc]
    critical := critical_reverse_pair s hc r }
  refine ⟨z,q,?_⟩
  change (w.append v).getVert 2 = a
  rw [←hw2,SimpleGraph.Walk.getVert_append]
  simp

include s in
/-- A large critical image makes the original forward seed eligible, using
one reciprocal path rather than a universal critical-escape premise. -/
theorem large_image_forward_eligible
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ¬ U d.radical (p.walk.getVert 2) ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hescape := large_image_radius_escape s hc hb2 p hlarge
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  rw [hl] at hescape
  obtain ⟨z,q,hq⟩ := radius_escape_reciprocal_path s hc hb p hescape
  simpa only [hq] using critical_start_not_le_second_slice s hc hb2 q

include s in
/-- At distance four, a large critical image forces the selected span to be
nonabelian, retaining the controlled subactor and the full central cover. -/
theorem large_image_selected_span_nonabelian
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅localZSpan d.radical (p.walk.getVert 2) a,
      localZSpan d.radical (p.walk.getVert 2) a⁆ ≠ ⊥ := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c a
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hPV : P ≤ V d.radical a := localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hac])
  have hPQ : P ≤ Q d.radical a := hPV.trans (V_le_Q d.radical p.start_color hb2)
  have hPG : P ≤ stabilizer d.radical c := hPQ.trans
    (Q_le_stabilizer_of_dist_two d.radical a c p.start_color hac)
  intro hzero
  have hPC : P ≤ Q d.radical c := by
    rw [←C_eq_Q s hc c hcol]
    exact le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp hzero).trans
      (centralizer_le (Z_le_localZSpan d.radical c a)))
  obtain ⟨W,hWU,_,hindex,hcomm⟩ := critical_radius_restricted_commutator s hc hb2 p hlarge
  have hWG : W ≤ stabilizer d.radical a := (hWU.trans (DistanceEight.U_le_Z d.radical _)).trans
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical)
  have hWQ : ¬ W ≤ Q d.radical a := by
    intro hWQ
    have he := relIndex_eq_one.mpr hWQ
    omega
  have hPW : ⁅P,W⁆ ≤ Z d.radical a := by
    rw [hl] at hcomm
    exact (commutator_mono (le_inf hPV hPC) le_rfl).trans hcomm
  have hPB := normalized_radius_le_slice_of_actor_at s hb2 p.start_color P W hPV
    (localZSpan_normalized d.radical c a) hWG hWQ hPW
  exact large_image_forward_eligible s hc hb p hlarge
    ((DistanceEight.U_le_Z d.radical c).trans ((Z_le_localZSpan d.radical c a).trans hPB))

include e hz hn in
/-- A large critical image forces a forward slice larger than two. This
discharges nonabelianness in the actual small-slice image exclusion. -/
theorem large_image_forward_slice_gt_two_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hn := large_image_selected_span_nonabelian s hc hb p hlarge
  by_contra! hsmall
  exact large_critical_image_false_of_small_slice s hc hb p hn hsmall hlarge

include e hz hn in
/-- A small forward slice forces both literal critical images to have order
two, including when nonabelianness of the selected span is not yet known. -/
theorem small_slice_critical_indices_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 2 ∧
      (Q d.radical (alpha d.radical)).relIndex (Z d.radical a') = 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  apply small_critical_indices s hc p
  by_contra! hlarge
  have hstrict := large_image_forward_slice_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
