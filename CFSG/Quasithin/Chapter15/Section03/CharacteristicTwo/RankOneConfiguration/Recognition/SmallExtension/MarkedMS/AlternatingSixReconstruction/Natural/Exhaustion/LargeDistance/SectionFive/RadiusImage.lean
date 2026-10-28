module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusApplication

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.QuadraticSylow

/-!
# Radius-image bounds for every original radical image

At a comparison component vertex, every seed of a sufficiently close radius
acts quadratically on the actual natural quotient. The radius normalizes its
seed subgroups and is a two-group. The normal-quadratic Sylow calculation
therefore bounds its image by eight, independently of the radical's image.
Conjugation gives the estimate at arbitrary component vertices, including
the vertex two steps before a critical endpoint.

The known-simple applications discharge the full symmetric marking and the
central-layer premise on the original minimum characteristic replacement.
The chief-factor consumer retains its literal local commutator premise;
discharging that premise in all cases, and MS93 (5.11)--(5.12), remain with
qt-e-ms-small-a6-exhaustion-large-distance. Both central-cover orders are
retained. Source: MS93 (5.2), printed pp.914--915.
-/

public noncomputable section
open Subgroup BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
section General
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {r : Replacement L R} (s : FullSymmetricAction h e hz hn r)

private theorem seed_le_stabilizer_of_dist_le {a b : Vertex r.radical}
    (ha : color r.radical a = false)
    (hd : (cosetGraph r.radical).dist a b ≤ replacementDistance h r) :
    Z r.radical a ≤ stabilizer r.radical b := by
  apply Z_le_stabilizer_of_dist_le a ((replacementGeometry h r).exists_critical a ha)
  rwa [(replacementGeometry h r).distance_constant a ha]

private theorem graph_seed_quadratic (hc : DistanceTwo.CentralLayer r)
    (a : Vertex r.radical) (ha : color r.radical a = false)
    (hd : (cosetGraph r.radical).dist a (alpha r.radical) ≤ replacementDistance h r) :
    QuadraticPointCore.Quadratic (graphImage s (Z r.radical a)) := by
  let A := (Z r.radical a).comap (embedM r.radical)
  have hm : A.map (embedM r.radical) = Z r.radical a :=
    map_comap_eq_self ((seed_le_stabilizer_of_dist_le (h := h) ha hd).trans_eq (stabilizer_m_base r.radical))
  have hZa : Z r.radical (alpha r.radical) ≤ stabilizer r.radical a :=
    seed_le_stabilizer_of_dist_le (h := h) rfl (by rwa [SimpleGraph.dist_comm])
  let := (replacementGeometry h r).Z_elementary (replacementDistance_pos h r) a ha
  have hcomm : ⁅U r.radical (alpha r.radical),Z r.radical a⁆ ≤ Z r.radical a :=
    le_normalizer_iff_commutator_le_right.mp ((DistanceEight.U_le_Z r.radical _).trans
      (hZa.trans (Z_normalized r.radical a)))
  apply image_quadratic_of_commutator s A
  intro x hx y hy
  apply embedM_injective r.radical
  simp only [map_mul]
  have hx' : embedM r.radical x ∈ Z r.radical a := by
    apply hcomm
    rw [hc.U_eq_moved,←hm,←map_commutator]
    exact mem_map_of_mem _ hx
  exact (le_centralizer_iff_isMulCommutative.mpr inferInstance) hx' _ hy

private theorem graphImage_normalizes {A B : Subgroup (FreeAmalgam r.radical)}
    (hn : B ≤ normalizer (A : Set (FreeAmalgam r.radical))) :
    graphImage s B ≤ normalizer (graphImage s A : Set S) := by
  exact (map_mono ((comap_mono hn).trans (le_normalizer_comap (embedM r.radical)))).trans
    (le_normalizer_map s.projection)

include s in
private theorem radius_image_at_base_le_eight (hc : DistanceTwo.CentralLayer r)
    (hb : 2 < replacementDistance h r) (a : Vertex r.radical)
    (ha : color r.radical a = false)
    (hd : (cosetGraph r.radical).dist a (alpha r.radical) + 2 ≤ replacementDistance h r) :
    (Q r.radical (alpha r.radical)).relIndex (V r.radical a) ≤ 8 := by
  have hVaQ : V r.radical a ≤ Q r.radical a := V_le_Q r.radical (geometry := replacementGeometry h r) ha hb
  have hVbase : V r.radical a ≤ stabilizer r.radical (alpha r.radical) := by
    apply (V_le_iff r.radical ha _).mpr
    intro d hdcol hda
    apply seed_le_stabilizer_of_dist_le (h := h) hdcol
    have ht := (cosetGraph_connected r.radical).dist_triangle (u:=d) (v:=a) (w:=alpha r.radical)
    omega
  let I := {d : Vertex r.radical // color r.radical d = false ∧
    (cosetGraph r.radical).dist d a ≤ 2}
  have hV : V r.radical a = ⨆ d : I, Z r.radical d.val := by
    apply le_antisymm
    · apply (V_le_iff r.radical ha _).mpr
      intro d hd hda
      exact le_iSup_of_le (⟨d,hd,hda⟩ : I) le_rfl
    · exact iSup_le fun d => le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  have hseed (d : I) : Z r.radical d.val ≤ V r.radical a :=
    hV ▸ le_iSup (fun d : I => Z r.radical d.val) d
  have hm (d : I) : ((Z r.radical d.val).comap (embedM r.radical)).map (embedM r.radical) =
      Z r.radical d.val := map_comap_eq_self ((hseed d).trans hVbase |>.trans_eq (stabilizer_m_base r.radical))
  have hgen : graphImage s (V r.radical a) = ⨆ d : I, graphImage s (Z r.radical d.val) := by
    have hcmap : (V r.radical a).comap (embedM r.radical) =
        ⨆ d : I, (Z r.radical d.val).comap (embedM r.radical) := by
      apply map_injective (embedM_injective r.radical)
      rw [Subgroup.map_iSup]
      simp only [hm]
      rw [map_comap_eq_self (hVbase.trans_eq (stabilizer_m_base r.radical)),hV]
    change ((V r.radical a).comap (embedM r.radical)).map s.projection = _
    rw [hcmap,Subgroup.map_iSup]
    rfl
  have hP : IsPGroup 2 (graphImage s (V r.radical a)) :=
    (((Q_isPGroup r.radical (replacement_radical_isPGroup h r)
      (replacement_core_le_radical h r) a ha).to_le hVaQ).comap_of_injective
        (embedM r.radical) (embedM_injective r.radical)).map s.projection
  rw [←graphImage_card s _ hVbase]
  apply QuadraticSylow.generated_normal_quadratic_bound _ hP _ hgen
  · intro d
    let := (replacementGeometry h r).Z_elementary (replacementDistance_pos h r) d.val d.property.1
    let := IsElementaryAbelian.comap_of_injective (p:=2) (embedM r.radical)
      (embedM_injective r.radical) (Z r.radical d.val)
    exact IsElementaryAbelian.map s.projection
  · intro d
    apply graphImage_normalizes
    exact hVaQ.trans ((Q_le_stabilizer_of_dist_le_two a d.val ha d.property.1
      (by rw [SimpleGraph.dist_comm]; exact d.property.2)).trans (Z_normalized r.radical d.val))
  · intro d
    apply graph_seed_quadratic s hc d.val d.property.1
    have ht := (cosetGraph_connected r.radical).dist_triangle (u:=d.val) (v:=a) (w:=alpha r.radical)
    have hda := d.property.2
    omega


include s in
/-- Source (5.2)'s radius image estimate, for either central cover and every
actual radical image. -/
theorem radius_image_index_le_eight_general (hc : DistanceTwo.CentralLayer r)
    (hb : 2 < replacementDistance h r) (a e : Vertex r.radical)
    (ha : color r.radical a = false) (he : color r.radical e = false)
    (hd : (cosetGraph r.radical).dist a e + 2 ≤ replacementDistance h r) :
    (Q r.radical e).relIndex (V r.radical a) ≤ 8 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color r.radical he
  have hbase : act r.radical g⁻¹ e = alpha r.radical := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hbnd := radius_image_at_base_le_eight s hc hb (act r.radical g⁻¹ a)
    (by rwa [action_preserves_color]) (by rw [←hbase,dist_act]; exact hd)
  rw [←hbase,Q_act,V_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hbnd
  exact hbnd

include s in
/-- The source estimate at the original critical path's component vertex two
steps before its endpoint. No point-core premise is needed. -/
theorem critical_radius_image_index_le_eight_general (hc : DistanceTwo.CentralLayer r)
    (hb : 2 < replacementDistance h r) {a a' : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) a a') :
    (Q r.radical (p.walk.getVert (p.walk.length-2))).relIndex (V r.radical a) ≤ 8 := by
  have hl : p.walk.length = replacementDistance h r := p.length_eq_b
  apply radius_image_index_le_eight_general s hc hb a _ p.start_color
  · apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have heven := replacementDistance_even h r
    rw [hl,Nat.even_iff]
    rw [Nat.even_iff] at heven
    omega
  · rw [p.dist_start (Nat.sub_le _ _),hl]
    omega


include s in
/-- The unconditional radius-image bound discharges the chief-factor index
premise. The displayed local commutator containment is the remaining source
premise; its discharge and final Section 5 assembly stay with this owner. -/
theorem critical_radius_central_of_commutator (hc : DistanceTwo.CentralLayer r)
    (hb : 2 < replacementDistance h r) {a' : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) (alpha r.radical) a')
    (hforward : 4 ≤ (Q r.radical a').relIndex (Z r.radical (alpha r.radical)))
    (hcomm : ⁅V r.radical (alpha r.radical) ⊓ Q r.radical (p.walk.getVert (p.walk.length-2)),
        Z r.radical a'⁆ ≤ Z r.radical (alpha r.radical)) :
    ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤
      centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  obtain ⟨a,haA,ha,heven⟩ :=
    exists_even_involution_reverse_critical_image s hc (replacementDistance_pos h r) p hforward
  apply radius_commutator_central_of_residual_dichotomy (h := h) (r := r) hb
  apply radius_residual_dichotomy_of_index s hb s.surjective
    (Z r.radical a') (Q r.radical (p.walk.getVert (p.walk.length-2)))
    (critical_Z_le_stabilizer r.radical (replacementGeometry h r) (alpha r.radical) rfl
      (replacementDistance_pos h r) p.critical)
    a ha heven haA hcomm
  exact critical_radius_image_index_le_eight_general s hc hb p

end General

section KnownSimple
variable {G : Type u} [Group G] [Finite G]
variable {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (r : Replacement L R) (hb : 2 < replacementDistance h r)

include e hz hn hb in
/-- MS93 (5.2)'s image bound on the minimum characteristic replacement of the
original MS2(a) radical. The action and central-layer premises are discharged. -/
theorem radius_image_index_le_eight_knownSimple (a c : Vertex r.radical)
    (ha : color r.radical a = false) (hc : color r.radical c = false)
    (hd : (cosetGraph r.radical).dist a c + 2 ≤ replacementDistance h r) :
    (Q r.radical c).relIndex (V r.radical a) ≤ 8 :=
  radius_image_index_le_eight_general (fullSymmetricAction_knownSimple h e hz hn r hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn r) hb a c ha hc hd

include e hz hn hb in
theorem critical_radius_image_index_le_eight_knownSimple {a a' : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) a a') :
    (Q r.radical (p.walk.getVert (p.walk.length-2))).relIndex (V r.radical a) ≤ 8 :=
  critical_radius_image_index_le_eight_general (fullSymmetricAction_knownSimple h e hz hn r hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn r) hb p

include e hz hn hb in
/-- Actual replacement application of the source chief-factor argument, with
only its local commutator containment and critical index left explicit. -/
theorem critical_radius_central_knownSimple_of_commutator {a' : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) (alpha r.radical) a')
    (hforward : 4 ≤ (Q r.radical a').relIndex (Z r.radical (alpha r.radical)))
    (hcomm : ⁅V r.radical (alpha r.radical) ⊓ Q r.radical (p.walk.getVert (p.walk.length-2)),
        Z r.radical a'⁆ ≤ Z r.radical (alpha r.radical)) :
    ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤
      centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) :=
  critical_radius_central_of_commutator (fullSymmetricAction_knownSimple h e hz hn r hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn r) hb p hforward hcomm

end KnownSimple

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
