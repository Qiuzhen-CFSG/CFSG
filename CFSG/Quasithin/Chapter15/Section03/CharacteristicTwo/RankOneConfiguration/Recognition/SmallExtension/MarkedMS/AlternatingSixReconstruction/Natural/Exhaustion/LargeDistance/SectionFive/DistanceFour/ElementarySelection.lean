module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.CubeSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEscape

/-!
# Initial selection for all elementary radical images

For the mixed-plane image, a strict forward slice has a nonabelian orbit
span. Indeed, an abelian span lies in the midpoint two-core. Transport the
forward seed to the generating edge supplied by the original Sylow
restriction. Its orbit under the actual relative edge normalizer stays in
that same span, so the mixed-plane trapped-orbit estimate bounds its slice
by two, contradicting strictness. This uses the whole relative normalizer,
not only the edge kernel, and keeps the full seed and its central attachment.

If initial selection were absent, both endpoint seeds of every critical
path would have large midpoint slices. The proved mixed-plane radius escape
constructs a reciprocal path whose midpoint is the original base. Its large
starting slice is precisely the strict forward slice just considered. This
gives initial nonabelian large-slice selection for the mixed image. The
two-transposition image is already excluded, so every order-four image is
covered.

For larger elementary images, the original Sylow restriction formula and
the elementary symmetric-six catalogue force one of the two full elementary
eights. Their existing selection theorems apply with the literal projection.
The original-replacement consumer therefore leaves only non-elementary
images of orders sixteen and eight, with restriction indices one and two.
It retains both moving covers and all central attachments. Initial selection
for these last two images, the independent selected terminal contradiction,
and unconditional DistanceFourInput assembly remain open.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.8), printed pp.919--920, and their use in (5.12), p.924.
The private MixedEscape import reuses its checked relative trapped-orbit
argument at distance greater than two, preserving its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
/-- A strict forward slice in the mixed-plane image has a nonabelian
full-seed orbit span on the original distance-four path. -/
theorem mixed_large_forward_span_nonabelian
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  by_cases hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))
  · exact large_image_selected_span_nonabelian s hc hb p hlarge
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph d.radical).dist (alpha d.radical) c = 2 := p.dist_start (by omega)
  have hPV : P ≤ V d.radical (alpha d.radical) :=
    localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hac])
  have hPG : P ≤ stabilizer d.radical c :=
    (hPV.trans (V_le_Q d.radical rfl hb2)).trans
      (Q_le_stabilizer_of_dist_two d.radical (alpha d.radical) c rfl hac)
  intro hzero
  have hPC : P ≤ Q d.radical c := by
    rw [←C_eq_Q s hc c hcCol]
    exact le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp hzero).trans
      (centralizer_le (Z_le_localZSpan d.radical c (alpha d.radical))))
  obtain ⟨T,hT⟩ := large_distance_mixed_original_sylow_knownSimple hb2 u him
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 T hT p
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  have hct : Adjacent d.radical (act d.radical g c) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hc1
  have hseed : Z d.radical (act d.radical g c) ≤ P := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan d.radical c (alpha d.radical))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical c (alpha d.radical)
        ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
  have htrap : conjugateSpanBy (Z d.radical (act d.radical g c))
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [hl]
    exact (conjugateSpanBy_le hseed
      (inf_le_right.trans (localZSpan_normalized d.radical c (alpha d.radical)))).trans hPC
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hi := MixedEscape.trapped_slice_bound s hc hb2 u hf p hsmall htrap hat hct hgen
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 _ rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hi
  exact (Nat.not_le_of_gt hstrict) hi

include e hz hn in
/-- Mixed-plane radius escape and the literal reciprocal path discharge
the strict-slice premise and supply initial selection on both covers. -/
theorem mixed_initial_selection_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  rcases initial_selection_or_large_midpoint_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb with hsel | hlarge
  · exact hsel
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hout := MixedEscape.mixed_radius_not_le_predecessor_knownSimple hb2 u him p
  rw [hl] at hout
  obtain ⟨w,q,hq⟩ := radius_escape_reciprocal_path s hc hb p hout
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
    simpa only [hq] using (hlarge _ _ q).1
  exact ⟨z,p,mixed_large_forward_span_nonabelian hb u him p hi,hi⟩

include e hz hn in
/-- Every radical image of order four supplies initial nonabelian
large-slice selection, with no additional original Sylow premise. -/
theorem four_image_initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨u,hu⟩ := PairExclusion.four_image_mixed_knownSimple (by omega) hfour
  exact mixed_initial_selection_knownSimple hb u hu

include e hz hn in
/-- Every elementary replacement image supplies initial selection. The
order-four alternatives use the mixed-plane result; larger elementary images
fill one of the two actual order-eight permutation subgroups. -/
theorem elementary_initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  by_cases hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)
  · exact nonsylow_initial_selection_knownSimple (e := e) (hz := hz) (hn := hn) hb hns
  push Not at hns
  obtain ⟨T,hT⟩ := hns
  let A := d.radical.map (SourceReduction.projection h e hz hn d)
  by_cases hfour : Nat.card A = 4
  · exact four_image_initial_selection_knownSimple hb hfour
  have hlarge : 8 ≤ Nat.card A := by
    obtain ⟨_,_,hprod,hidx⟩ := SylowRestriction.original_sylow_restriction_knownSimple
      (e := e) (hz := hz) (hn := hn) (d := d) (by omega) T hT
    change Nat.card A * _ = 16 at hprod
    rcases hidx with hi | hi | hi <;> rw [hi] at hprod <;> omega
  have he : Representation.BinaryOffender.IsElementaryTwo A := ⟨by
    intro hz
    rw [hz,card_bot] at hlarge
    omega,hel⟩
  obtain ⟨B,hB,hBD | hBE,hAB⟩ := exists_conjugate_le_D_or_exceptional he
  · have hDcard : Nat.card (D 6) = 8 := card_disjointTranspositions (3 : Fin 4)
    have hBfull : B = D 6 := eq_of_le_of_card_ge hBD (by
      rw [hDcard,←hAB.card_eq]
      exact hlarge)
    obtain ⟨u,hu⟩ := hAB
    apply cube_initial_selection_knownSimple hb u
    exact hu.trans (congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hBfull)
  · have hBfull : B = exceptional 6 (by decide) := eq_of_le_of_card_ge hBE (by
      rw [card_exceptional,←hAB.card_eq]
      exact hlarge)
    obtain ⟨u,hu⟩ := hAB
    apply full_point_initial_selection_knownSimple hb u
    change A = _
    rw [hu,hBfull,CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional]

include e hz hn in
/-- On the literal original replacement, only non-elementary images of order
eight or sixteen can remain without initial nonabelian selection. In that
alternative the original radical is Sylow, and the exact restriction index
is retained. No Sylow condition is imposed on the replacement radical. -/
theorem initial_selection_or_nonelementary_sylow_knownSimple
    (hb : replacementDistance h d = 4) :
    (∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2))) ∨
    ((∃ T : Sylow 2 (L ⊔ R : Subgroup G),
        (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) ∧
      (¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d))) ∧
      ((d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 1 ∧
          Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) ∨
        (d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 2 ∧
          Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8))) := by
  classical
  by_cases hsel : ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2))
  · exact Or.inl hsel
  have hs : ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R) := by
    by_contra hns
    exact hsel (nonsylow_initial_selection_knownSimple (e := e) (hz := hz) (hn := hn) hb hns)
  obtain ⟨T,hT⟩ := hs
  refine Or.inr ⟨⟨T,hT⟩,fun hel => hsel (elementary_initial_selection_knownSimple hb hel),?_⟩
  obtain ⟨_,_,hprod,hidx⟩ := SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) T hT
  rcases hidx with hi | hi | hi
  · exact Or.inl ⟨hi,by rw [hi,Nat.mul_one] at hprod; exact hprod⟩
  · exact Or.inr ⟨hi,by rw [hi] at hprod; omega⟩
  · have hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4 := by
      rw [hi] at hprod
      omega
    exact (hsel (four_image_initial_selection_knownSimple hb hfour)).elim


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
