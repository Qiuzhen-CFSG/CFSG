module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Structure

/-!
# Radius image and endpoint commutator bounds for A₆

The unique even offender identifies all critical images along an edge.
Consequently the radius image at a critical midpoint lies in a conjugate
endpoint image and has order at most four. Its intersection with the
midpoint kernel centralizes the initial X-layer; the self-centralizing
opposite offender places that intersection in the endpoint join.
This proves the full X-endpoint commutator bound without a Frattini
hypothesis or an identification X = Z.

Source: MS93 (3.8), p.878, the radius-index paragraph. The image comparison
adapts Exclusion.MovingAbelian.Displacement.Index to the literal A₆ action.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

private theorem reverse_pair
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (a : Vertex r.radical) (ha : color r.radical a = false) (b : Vertex r.radical)
    (hc : CriticalPair r.radical a b ((replacementGeometry h r).exists_critical a ha)) :
    CriticalPair r.radical b a ((replacementGeometry h r).exists_critical b
      (critical_endpoint_color r.radical a ha _ hc)) := by
  apply critical_reverse r.radical (replacementGeometry h r)
    (edgeCentralizerCondition h m hz hn r himage) a ha _ b
      (critical_endpoint_color r.radical a ha _ hc) hc
  rw [(replacementGeometry h r).distance_constant a ha]
  exact replacementDistance_pos h r

private theorem endpoint_le_stabilizer
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (a : Vertex r.radical) (ha : color r.radical a = false) (b : Vertex r.radical)
    (hc : CriticalPair r.radical a b ((replacementGeometry h r).exists_critical a ha)) :
    X r.radical b ≤ stabilizer r.radical a := by
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one r.radical a b (by
    rw [hc.1,(replacementGeometry h r).distance_constant a ha]
    exact replacementDistance_pos h r)
  exact (Estimates.critical_edge_data h m hz hn r himage a ha b hc t hat ht).1.trans
    (CriticalCriterion.edge_le_stabilizer r.radical ha hat)

private theorem radius_le_critical_join (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a c : Vertex r.radical) (ha : color r.radical a = false) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist a c = 2)
    (t : Vertex r.radical) (hat : Adjacent r.radical a t) (hct : Adjacent r.radical c t)
    (d : Vertex r.radical) (hcd : CriticalPair r.radical c d ((replacementGeometry h r).exists_critical c hcColor))
    (htd : (cosetGraph r.radical).dist t d + 1 = (cosetGraph r.radical).dist c d) :
    V r.radical a ≤ X r.radical d ⊔ Q r.radical c := by
  let geometry := replacementGeometry h r
  have hfour : geometry.b r.radical = 4 := fg.distance
  have hta : (cosetGraph r.radical).dist t a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr (adjacent_symm r.radical hat))
  have hct1 : (cosetGraph r.radical).dist c t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr hct)
  apply radius_le_of_m_ball ha
  intro e he hea
  by_cases heQ : Z r.radical e ≤ Q r.radical c
  · exact heQ.trans le_sup_right
  have hmin := criticalDistance_le r.radical e ((replacementGeometry h r).exists_critical e he) heQ
  have hecrit : criticalDistance r.radical e ((replacementGeometry h r).exists_critical e he) = 4 :=
    (geometry.distance_constant e he).trans hfour
  rw [hecrit] at hmin
  have htri := (cosetGraph_connected r.radical).dist_triangle (u := e) (v := a) (w := c)
  have hec : (cosetGraph r.radical).dist e c = 4 := by omega
  have hpair : CriticalPair r.radical e c ((replacementGeometry h r).exists_critical e he) :=
    ⟨hec.trans hecrit.symm, heQ⟩
  have hrev := reverse_pair h m hz hn r himage e he c hpair
  have hte : (cosetGraph r.radical).dist t e + 1 = (cosetGraph r.radical).dist c e := by
    have h₁ := (cosetGraph_connected r.radical).dist_triangle (u := t) (v := a) (w := e)
    have h₂ := (cosetGraph_connected r.radical).dist_triangle (u := c) (v := t) (w := e)
    have hae : (cosetGraph r.radical).dist a e ≤ 2 := by simpa only [SimpleGraph.dist_comm] using hea
    have hce : (cosetGraph r.radical).dist c e = 4 := by rwa [SimpleGraph.dist_comm]
    omega
  have hj := Estimates.critical_join_common h m hz hn r himage c hcColor d hcd t hct htd e hrev hte
  have hZX := geometry.omega_bound e he (by rw [hecrit]; decide)
  exact hZX.trans (le_sup_left.trans hj.ge)

private theorem relIndex_join_of_normalizes {G : Type*} [Group G]
    (E N : Subgroup G) (hEN : E ≤ normalizer (N : Set G)) :
    N.relIndex (E ⊔ N) = N.relIndex E := by
  let := normal_subgroupOf_of_le_normalizer hEN
  let := normal_subgroupOf_sup_of_le_normalizer hEN
  exact Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN).toEquiv.symm


/-- Literal radius-image comparison, with all geometric premises discharged. -/
theorem radius_index_le_critical_image (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false)
    (a' : Vertex r.radical) (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist a c = 2) (hca' : (cosetGraph r.radical).dist c a' = 2)
 :
    (Q r.radical c).relIndex (V r.radical a) ≤ (Q r.radical a).relIndex (X r.radical a') := by
  let geometry := replacementGeometry h r
  have hfour : geometry.b r.radical = 4 := fg.distance
  have hd : (cosetGraph r.radical).dist a a' = 4 :=
    (hc.1.trans (geometry.distance_constant a ha)).trans hfour
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two r.radical a c hac
  have hta' : (cosetGraph r.radical).dist t a' + 1 = (cosetGraph r.radical).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj r.radical _ _).mpr (adjacent_symm r.radical hct))
    have h₁ := (cosetGraph_connected r.radical).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected r.radical).dist_triangle (u := t) (v := c) (w := a')
    omega
  obtain ⟨g, hgt, hga⟩ := stabilizer_transitive_neighbors r.radical t
    (adjacent_symm r.radical hat) (adjacent_symm r.radical hct)
  have hgt' : act r.radical g t = t := hgt
  have hcol : color r.radical (act r.radical g a) = false := by rw [hga]; exact hcColor
  have hcg : CriticalPair r.radical c (act r.radical g a') ((replacementGeometry h r).exists_critical c hcColor) := by
    simpa only [hga] using (criticalPair_act_iff r.radical g a a' ((replacementGeometry h r).exists_critical a ha)
      ((replacementGeometry h r).exists_critical (act r.radical g a) hcol)).mpr hc
  have htg : (cosetGraph r.radical).dist t (act r.radical g a') + 1 =
      (cosetGraph r.radical).dist c (act r.radical g a') := by
    rw [← hgt', ← hga, dist_act, dist_act]
    exact hta'
  have hV := radius_le_critical_join h m hz hn r himage fg a c ha hcColor hac
    t hat hct (act r.radical g a') hcg htg
  have hX : X r.radical (act r.radical g a') ≤ stabilizer r.radical c :=
    endpoint_le_stabilizer h m hz hn r himage c hcColor (act r.radical g a') hcg
  have hJ : X r.radical (act r.radical g a') ⊔ Q r.radical c ≤ stabilizer r.radical c :=
    sup_le hX (fun _ hx => hx.1)
  let := finite_stabilizer r.radical c
  let : Finite (X r.radical (act r.radical g a') ⊔ Q r.radical c : Subgroup (FreeAmalgam r.radical)) :=
    Finite.of_injective (inclusion hJ) (inclusion_injective hJ)
  calc
    (Q r.radical c).relIndex (V r.radical a) ≤ (Q r.radical c).relIndex (X r.radical (act r.radical g a') ⊔ Q r.radical c) :=
      relIndex_le_of_le_right hV
        ((Q r.radical c).subgroupOf (X r.radical (act r.radical g a') ⊔ Q r.radical c)).index_ne_zero_of_finite
    _ = (Q r.radical c).relIndex (X r.radical (act r.radical g a')) :=
      relIndex_join_of_normalizes _ _ (hX.trans (Q_normalized r.radical c))
    _ = (Q r.radical a).relIndex (X r.radical a') := by
      rw [← hga, Q_act, X_act]
      exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective

/-- Every actual critical X-image has order four, at any original-group vertex. -/
theorem critical_image_index_eq_four
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (a : Vertex r.radical) (ha : color r.radical a = false) (b : Vertex r.radical)
    (hc : CriticalPair r.radical a b ((replacementGeometry h r).exists_critical a ha)) :
    (Q r.radical a).relIndex (X r.radical b) = 4 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color r.radical ha
  let f := g⁻¹
  have hf : act r.radical f a = alpha r.radical := by
    rw [hg]
    simp only [f,act_mVertex,mul_inv_cancel]
    rfl
  have hfcol : color r.radical (act r.radical f a) = false := by rw [hf]; rfl
  have hc' : CriticalPair r.radical (alpha r.radical) (act r.radical f b)
      ((replacementGeometry h r).exists_critical (alpha r.radical) rfl) := by
    simpa only [hf] using
      (criticalPair_act_iff r.radical f a b ((replacementGeometry h r).exists_critical a ha)
        ((replacementGeometry h r).exists_critical (act r.radical f a) hfcol)).mpr hc
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one r.radical (alpha r.radical)
    (act r.radical f b) (by
      rw [hc'.1,(replacementGeometry h r).distance_constant (alpha r.radical) rfl]
      exact replacementDistance_pos h r)
  have hcard := (Estimates.critical_image_structure h m hz hn r himage
    (act r.radical f b) hc' t hat ht).1
  have hE := endpoint_le_stabilizer h m hz hn r himage
    (alpha r.radical) rfl (act r.radical f b) hc'
  have hEm : ((X r.radical (act r.radical f b)).comap (embedM r.radical)).map
      (embedM r.radical) = X r.radical (act r.radical f b) :=
    map_comap_eq_self (hE.trans_eq (stabilizer_m_base r.radical))
  rw [Estimates.criticalImage,← relIndex_ker,projection_kernel,
    ← relIndex_map_map_of_injective _ _ (embedM_injective r.radical),hEm,
    ← Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r)] at hcard
  rw [← hf,Q_act,X_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj f⁻¹).injective] at hcard
  exact hcard

/-- The radius image at a critical midpoint has order at most four. -/
theorem radius_index_le_four
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) (a' : Vertex r.radical)
    (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist a c = 2)
    (hca' : (cosetGraph r.radical).dist c a' = 2) :
    (Q r.radical c).relIndex (V r.radical a) ≤ 4 := by
  exact (radius_index_le_critical_image h m hz hn r himage fg a ha a' hc c hcColor hac hca').trans_eq
    (critical_image_index_eq_four h m hz hn r himage a ha a' hc)

/-- The full radius-intersection commutator bound on X at the far endpoint.
Self-centralization gives the endpoint join directly, without a Frattini premise. -/
theorem radius_intersection_X
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) (a' : Vertex r.radical)
    (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical)
    (hca' : (cosetGraph r.radical).dist c a' = 2) :
    ⁅V r.radical a ⊓ Q r.radical c,X r.radical a'⁆ ≤ ⁅X r.radical a,X r.radical a'⁆ := by
  have hb : 2 < replacementDistance h r := by rw [fg.distance]; decide
  obtain ⟨t,hct,ha't⟩ := exists_common_neighbor_of_dist_two r.radical c a' hca'
  have ha' := critical_endpoint_color r.radical a ha _ hc
  have ht : color r.radical t = true := by
    have hn := adjacent_color_ne r.radical ha't
    cases he : color r.radical t <;> simp_all
  let Y := V r.radical a ⊓ Q r.radical c
  have hYS : Y ≤ stabilizer r.radical a' :=
    (inf_le_right.trans (Q_le_adjacent_h r.radical ht hct)).trans
      (CriticalCriterion.edge_le_stabilizer r.radical ha' ha't)
  have hYC : Y ≤ centralizer (X r.radical a : Set (FreeAmalgam r.radical)) :=
    (inf_le_left.trans ((replacementGeometry h r).V_le_Q hb a ha)).trans
      (Q_le_centralizer_X r.radical a)
  have hr := reverse_pair h m hz hn r himage a ha a' hc
  have hYJ : Y ≤ X r.radical a ⊔ Q r.radical a' :=
    (le_inf hYS hYC).trans (Estimates.critical_centralizer_le_join h m hz hn r himage a' ha' a hr)
  have he : ⁅X r.radical a',X r.radical a⁆ =
      ⁅X r.radical a',X r.radical a ⊔ Q r.radical a'⁆ :=
    commutator_eq_of_centralizing_sup (sup_comm _ _) (Q_le_centralizer_X r.radical a')
      ((endpoint_le_stabilizer h m hz hn r himage a' ha' a hr).trans (X_normalized r.radical a'))
  rw [commutator_comm Y,commutator_comm (X r.radical a),he]
  exact commutator_mono le_rfl hYJ

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
