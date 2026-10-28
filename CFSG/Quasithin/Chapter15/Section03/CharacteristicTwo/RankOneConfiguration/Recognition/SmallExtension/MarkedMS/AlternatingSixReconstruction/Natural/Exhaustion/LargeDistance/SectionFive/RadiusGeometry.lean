module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PointControl
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.NoncentralPair

/-!
# Radius images and noncentral critical-pair selection on the actual cover

Point-core containment bounds each edge image by eight. At distance four
this bounds the radius image at the penultimate vertex. Failure of radius
centrality selects a genuine critical pair with image at least four, by
normalization of an index-two subgroup and the two-group order constraint.

These steps retain the actual graph kernels and need no natural subgroup
or splitting of the central cover. They supply the geometric inputs of
MS93 (5.2), printed pp.914--915, following the corresponding native source
proofs in SymplecticSetup.RadiusImages and NoncentralPair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {r : Replacement L R} (s : FullSymmetricAction h e hz hn r)

theorem edge_kernel_index (a t : Vertex r.radical) (ha : color r.radical a = false)
    (hat : Adjacent r.radical a t) :
    (Q r.radical a).relIndex (Q r.radical t) = Nat.card (r.radical.map s.projection) := by
  have hbase : (Q r.radical (alpha r.radical)).relIndex (Q r.radical (beta r.radical)) =
      Nat.card (r.radical.map s.projection) := by
    rw [Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r),Q_beta,
      relIndex_map_map_of_injective _ _ (embedM_injective r.radical),
      ←s.projection_kernel,relIndex_ker]
  obtain ⟨g, hg | hg⟩ := edge_transitive r.radical hat (base_adjacent r.radical)
  · have he : (Q r.radical (act r.radical g a)).relIndex (Q r.radical (act r.radical g t)) =
        (Q r.radical a).relIndex (Q r.radical t) := by
      rw [Q_act,Q_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    rw [hg.1,hg.2] at he
    exact he.symm.trans hbase
  · have ht : color r.radical (beta r.radical) = false := by
      change color r.radical (hVertex r.radical 1) = false
      rw [←hg.1,action_preserves_color,ha]
    cases ht

theorem edge_kernel_index_le_eight (u : S)
    (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a t : Vertex r.radical) (ha : color r.radical a = false) (hat : Adjacent r.radical a t) :
    (Q r.radical a).relIndex (Q r.radical t) ≤ 8 := by
  rw [edge_kernel_index s a t ha hat]
  have hc := Nat.card_le_card_of_injective (inclusion hR) (inclusion_injective hR)
  have he : Nat.card (pointCore.map (MulAut.conj u).toMonoidHom) = 8 :=
    (card_map_of_injective (MulAut.conj u).injective).trans pointCore_card
  rwa [he] at hc

theorem radius_image_index_le_eight (u : S)
    (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 3 < (replacementGeometry h r).b r.radical) (a e : Vertex r.radical) (ha : color r.radical a = false)
    (hde : (cosetGraph r.radical).dist a e = 2) :
    (Q r.radical e).relIndex (V r.radical a) ≤ 8 := by
  obtain ⟨t,hat,het⟩ := exists_common_neighbor_of_dist_two r.radical a e hde
  have hd : (cosetGraph r.radical).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr hat)
  have hV : V r.radical a ≤ Q r.radical t := V_le_Q_of_dist_add_two_lt r.radical ha (by omega)
  have he : color r.radical e = false :=
    (color_eq_of_dist_even r.radical a e (by rw [hde]; decide)).symm.trans ha
  have hidx := edge_kernel_index s e t he het
  have hn : (Q r.radical e).relIndex (Q r.radical t) ≠ 0 := by
    rw [hidx]
    exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  exact (relIndex_le_of_le_right hV hn).trans
    (edge_kernel_index_le_eight s u hR e t he het)

/-- The order-eight estimate at the actual penultimate component vertex of a critical
path of length four. -/
theorem critical_radius_image_index_le_eight (u : S)
    (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : (replacementGeometry h r).b r.radical = 4) {a a' : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) a a') :
    (Q r.radical (p.walk.getVert (p.walk.length-2))).relIndex (V r.radical a) ≤ 8 := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  apply radius_image_index_le_eight s u hR (by omega) a _ p.start_color
  rw [p.dist_start (Nat.sub_le _ _),hl]


theorem noncentral_generator_image_four_le (hb : 2 < (replacementGeometry h r).b r.radical)
    (a d e : Vertex r.radical) (ha : color r.radical a = false)
    (hd : color r.radical d = false) (he : color r.radical e = false)
    (hda : (cosetGraph r.radical).dist d a ≤ 2) (hea : (cosetGraph r.radical).dist e a ≤ 2)
    (hne : ⁅⁅Z r.radical d,Q r.radical a⁆,Z r.radical e⁆ ≠ ⊥) :
    4 ≤ (Q r.radical e).relIndex (Z r.radical d) := by
  have hnZd : Q r.radical a ≤ normalizer (Z r.radical d : Set (FreeAmalgam r.radical)) :=
    (Q_le_stabilizer_of_dist_le_two a d ha hd
      (by rwa [SimpleGraph.dist_comm])).trans (Z_normalized r.radical d)
  have hnQe : Q r.radical a ≤ normalizer (Q r.radical e : Set (FreeAmalgam r.radical)) :=
    (Q_le_stabilizer_of_dist_le_two a e ha he
      (by rwa [SimpleGraph.dist_comm])).trans (Q_normalized r.radical e)
  have hout := CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.noncentral_generator_not_le r.radical (replacementGeometry h r) a d e ha he hea hne
  have hone : (Q r.radical e).relIndex (Z r.radical d) ≠ 1 := fun hh => hout (relIndex_eq_one.mp hh)
  have htwo : (Q r.radical e).relIndex (Z r.radical d) ≠ 2 := by
    intro hh
    have hnint : Q r.radical a ≤ normalizer ((Z r.radical d ⊓ Q r.radical e : Subgroup (FreeAmalgam r.radical)) : Set (FreeAmalgam r.radical)) := by
      intro q hq
      rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_inf _ _ _ (MulAut.conj q).injective,
        mem_normalizer_iff_map_conj_eq.mp (hnZd hq),
        mem_normalizer_iff_map_conj_eq.mp (hnQe hq)]
    have hc := commutator_le_of_normalized_index_two (Z r.radical d) (Z r.radical d ⊓ Q r.radical e)
      (Q r.radical a) inf_le_left (by rwa [inf_relIndex_left]) hnZd hnint
    apply hne
    apply le_bot_iff.mp
    exact (commutator_mono (hc.trans inf_le_right) le_rfl).trans (by
      rw [commutator_comm,(replacementGeometry h r).centralizes e he])
  have hZdV : Z r.radical d ≤ V r.radical a := le_iSup_of_le d (le_iSup_of_le hda le_rfl)
  have hp : IsPGroup 2 (Z r.radical d) :=
    (Q_isPGroup r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r) a ha).to_le (hZdV.trans (V_le_Q r.radical ha hb))
  let : Finite (stabilizer r.radical a) := finite_stabilizer r.radical a
  have hZa : Z r.radical d ≤ stabilizer r.radical a :=
    (hZdV.trans (V_le_Q r.radical ha hb)).trans (fun _ hx => hx.1)
  let : Finite (Z r.radical d) := Finite.of_injective (inclusion hZa) (inclusion_injective hZa)
  obtain ⟨n,hn⟩ := hp.index ((Q r.radical e).subgroupOf (Z r.radical d))
  change (Q r.radical e).relIndex (Z r.radical d) = 2^n at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp_all
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2

theorem exists_noncentral_critical_pair_large_image (hb : (replacementGeometry h r).b r.radical = 4)
    (a : Vertex r.radical) (ha : color r.radical a = false)
    (hn : ¬ ⁅V r.radical a,Q r.radical a⁆ ≤ centralizer (V r.radical a : Set (FreeAmalgam r.radical))) :
    ∃ d e, color r.radical d = false ∧ color r.radical e = false ∧
      (cosetGraph r.radical).dist d a = 2 ∧ (cosetGraph r.radical).dist e a = 2 ∧
      ⁅⁅Z r.radical d,Q r.radical a⁆,Z r.radical e⁆ ≠ ⊥ ∧ 4 ≤ (Q r.radical e).relIndex (Z r.radical d) ∧
      ∃ hd : color r.radical d = false,CriticalPair r.radical d e ((replacementGeometry h r).exists_critical d hd) := by
  obtain ⟨d,e,hd,he,hda,hea,ht,hcrit⟩ :=
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.exists_noncentral_critical_pair r.radical (replacementGeometry h r) hb a ha hn
  exact ⟨d,e,hd,he,hda,hea,ht,
    noncentral_generator_image_four_le (h := h) (r := r) (by omega) a d e ha hd he hda.le hea.le ht,hcrit⟩


/-- Noncentrality supplies a large-image critical path based at the original
vertex, using the actual graph conjugation. -/
theorem exists_base_large_critical_path
    (hb : (replacementGeometry h r).b r.radical = 4)
    (hn : ¬ ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤
      centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical))) :
    ∃ e, ∃ _p : CriticalPath r.radical (replacementGeometry h r) (alpha r.radical) e,
      4 ≤ (Q r.radical e).relIndex (Z r.radical (alpha r.radical)) := by
  obtain ⟨d,e,hd,_,_,_,_,hlarge,hd',hpair⟩ :=
    exists_noncentral_critical_pair_large_image (h := h) (r := r) hb (alpha r.radical) rfl hn
  obtain ⟨g,hdg⟩ := exists_mVertex_of_color r.radical hd
  have hf : act r.radical g⁻¹ d = alpha r.radical := by
    rw [hdg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hfcol : color r.radical (act r.radical g⁻¹ d) = false := by rw [hf]; rfl
  have hcrit : CriticalPair r.radical (alpha r.radical) (act r.radical g⁻¹ e)
      ((replacementGeometry h r).exists_critical (alpha r.radical) rfl) := by
    simpa only [hf] using (criticalPair_act_iff r.radical g⁻¹ d e
      ((replacementGeometry h r).exists_critical d hd')
      ((replacementGeometry h r).exists_critical (act r.radical g⁻¹ d) hfcol)).mpr hpair
  refine ⟨act r.radical g⁻¹ e,CriticalPath.ofPair rfl hcrit,?_⟩
  rw [←hf,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
  exact hlarge
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
