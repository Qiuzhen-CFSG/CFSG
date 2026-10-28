module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections

/-!
# Choosing the compatible incident frame for the second starred layer

The normalizer of R acts on the actual edge star. Its conjugation on R
agrees with an element of the holomorph stabilizer, so it permutes the
neighbor Z-layers. Normalization of B_alpha preserves the noncentral
selection condition; that condition also excludes alpha itself.

The genuine sections frame supplies the first intrinsic core. Incident
core coverage selects a second core crossed by the critical endpoint.
Choosing a representative in the first parabolic and changing the flag
preserves that parabolic and its intrinsic core. Together these arguments
construct all three fields of Seed.Compatible, without a selection or
normalization premise. The stronger constructor retains the literal first
parabolic equality for the supplied Sections.Frame.

The noncontainment of the second starred layer is a subsequent argument;
it is not asserted here. Source: Meierfrankenfeld--Stellmacher, Pushing up
weak BN-pairs of rank two (1993), flag selection on printed p.905 and
(4.6.12)(4), printed p.911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem holomorph_conjugation (g : normalizer (R : Set M)) :
    ∃ h ∈ stabilizer R (beta R), ∀ x ∈ (embedS R).range,
      h * x * h⁻¹ = embedM R g * x * (embedM R g)⁻¹ := by
  let a := R.normalizerMonoidHom g
  refine ⟨embedH R (SemidirectProduct.inr a), ?_, ?_⟩
  · rw [beta, stabilizer_h_base]
    exact ⟨SemidirectProduct.inr a, rfl⟩
  · rintro _ ⟨r, rfl⟩
    have hc := congrArg (embedH R) (SemidirectProduct.inl_aut a r)
    have hH (t : R) : embedH R (SemidirectProduct.inl t) = embedS R t :=
      DFunLike.congr_fun (embedH_comp_inl R) t
    have hM (t : R) : embedM R (t : M) = embedS R t :=
      DFunLike.congr_fun (embedM_comp_subtype R) t
    have ha : (a r : M) = (g : M) * r * (g : M)⁻¹ := rfl
    calc
      _ = embedS R (a r) := by
        simpa only [MonoidHom.id_apply, map_mul, map_inv, hH] using hc.symm
      _ = embedM R (a r : M) := (hM _).symm
      _ = _ := by rw [ha, map_mul, map_mul, map_inv, hM]

private theorem neighbor_Z_le_edge (common : CommonFacts R source geometry)
    {t : Vertex R} (ht : Adjacent R (beta R) t) :
    Z R t ≤ (embedS R).range := by
  have hZV : Z R t ≤ V R (beta R) := by
    rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  have h := hZV.trans ((Flags.RankOne.edgeRadius_le_radius (alpha R) (beta R) rfl
    (base_adjacent R)).trans (Flags.V_le_Q geometry common.large_distance _ rfl))
  have hQ := Q_le_adjacent_h R (show color R (beta R) = true from rfl) (base_adjacent R)
  exact (h.trans hQ).trans_eq (by
    change neighborhoodKernel R (hVertex R 1) = _
    rw [neighborhoodKernel_h_base_eq_Sbar]
    rfl)

/-- The first parabolic's ambient normalizer action preserves the actual edge star. -/
theorem edgeStar_normalized_by_edgeNormalizer
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry) :
    (normalizer (R : Set M)).map (embedM R) ≤
      normalizer (edgeStar R geometry (alpha R) (beta R)) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨g, hg, rfl⟩ x hx
  obtain ⟨h, hh, heq⟩ := holomorph_conjugation (⟨g, hg⟩ : normalizer (R : Set M))
  have hgm : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  have hB := Flags.B_map_conj geometry radius.toEarlyFacts (alpha R) rfl ⟨embedM R g, hgm⟩
  have hgen (t : Vertex R) (ht : nu R geometry (alpha R) t ∧ Adjacent R (beta R) t) :
      (Z R t).map (MulAut.conj (embedM R g)).toMonoidHom ≤
        edgeStar R geometry (alpha R) (beta R) := by
    have hZeq : (Z R t).map (MulAut.conj (embedM R g)).toMonoidHom =
        Z R (act R h⁻¹ t) := by
      rw [Z_act, inv_inv]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, heq w (neighbor_Z_le_edge common ht.2 hw)⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, (heq w (neighbor_Z_le_edge common ht.2 hw)).symm⟩
    have hbt : Adjacent R (beta R) (act R h⁻¹ t) := by
      have ha := (adjacent_act_iff R h⁻¹ (beta R) t).mpr ht.2
      have hfix : act R h⁻¹ (beta R) = beta R := (stabilizer R (beta R)).inv_mem hh
      rwa [hfix] at ha
    have hnc : ¬ Z R (act R h⁻¹ t) ≤ B R (alpha R) (geometry.Z_normal (alpha R)) := by
      rw [← hZeq, ← hB]
      exact fun hn => ht.1.2
        ((map_le_map_iff_of_injective (MulAut.conj (embedM R g)).injective).mp hn)
    have hne : act R h⁻¹ t ≠ alpha R := by
      intro he
      apply hnc
      rw [he]
      exact Flags.Z_le_B geometry _ (geometry.V_local _ rfl common.large_distance)
    have hcol : color R (act R h⁻¹ t) = false := by
      have hc := adjacent_color_ne R hbt
      have hb : color R (beta R) = true := rfl
      cases he : color R (act R h⁻¹ t) <;> simp_all
    have hdist : (cosetGraph R).dist (act R h⁻¹ t) (alpha R) = 2 := by
      have hb : (cosetGraph R).dist (beta R) (alpha R) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
        (adjacent_symm R (base_adjacent R)))
      have ht' : (cosetGraph R).dist (act R h⁻¹ t) (beta R) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
        (adjacent_symm R hbt))
      have htri := (cosetGraph_connected R).dist_triangle
        (u := act R h⁻¹ t) (v := beta R) (w := alpha R)
      have hn0 : (cosetGraph R).dist (act R h⁻¹ t) (alpha R) ≠ 0 :=
        fun hz => hne ((cosetGraph_connected R).dist_eq_zero_iff.mp hz)
      have hn1 : (cosetGraph R).dist (act R h⁻¹ t) (alpha R) ≠ 1 := by
        intro ho
        have ha := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp ho)
        exact adjacent_color_ne R ha hcol
      omega
    rw [hZeq]
    exact le_iSup_of_le _ (le_iSup_of_le ⟨⟨hdist, hnc⟩, hbt⟩ le_rfl)
  have hall : (edgeStar R geometry (alpha R) (beta R)).map
      (MulAut.conj (embedM R g)).toMonoidHom ≤ edgeStar R geometry (alpha R) (beta R) := by
    rw [edgeStar, Subgroup.map_iSup]
    apply iSup_le
    intro t
    rw [Subgroup.map_iSup]
    exact iSup_le (hgen t)
  exact hall (mem_map_of_mem _ hx)
open Flags.RankOne

/-- Identifying the intrinsic first core with Q_beta gives normalization of
the actual edge star by the entire first parabolic. -/
theorem flagParabolic_normalizes_edgeStar
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (i : Bool) (hi : flagKernel source i = Q R (beta R)) :
    flagParabolic source i ≤ normalizer (edgeStar R geometry (alpha R) (beta R)) := by
  have hcore : (parabolic source.projection source.flag i).pCoreIn 2 = R := by
    apply Subgroup.map_injective (embedM_injective R)
    exact hi.trans (Q_beta R)
  have hn : parabolic source.projection source.flag i ≤ normalizer (R : Set M) := by
    conv_rhs => rw [← hcore]
    exact (parabolic source.projection source.flag i).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _)
  exact (map_mono hn).trans (edgeStar_normalized_by_edgeNormalizer common radius)

omit [Finite M] in
private theorem parabolic_reflag (m : M) (i : Bool) :
    parabolic source.projection (source.projection m * source.flag) i =
      (parabolic source.projection source.flag i).map (MulAut.conj m).toMonoidHom := by
  have hmodel : modelParabolic (source.projection m * source.flag) i =
      (modelParabolic source.flag i).map (MulAut.conj (source.projection m)).toMonoidHom := by
    unfold modelParabolic
    rw [map_map]
    apply congrArg (fun q : SL →* SL =>
      (if i then Matrix.PSL3Two.lineParabolicSL else Matrix.PSL3Two.pointParabolicSL).map q)
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev]
    group
  unfold parabolic
  rw [hmodel]
  ext x
  simp only [mem_comap, mem_map_equiv]
  change (source.projection m)⁻¹ * source.projection x * source.projection m ∈
    modelParabolic source.flag i ↔
      source.projection (m⁻¹ * x * m) ∈ modelParabolic source.flag i
  simp only [map_mul, map_inv]

omit [Finite M] in
private theorem embedded_core_reflag (m : M) (i : Bool) :
    ((parabolic source.projection (source.projection m * source.flag) i).pCoreIn 2).map
        (embedM R) = localFlagKernel source i m := by
  rw [parabolic_reflag, ← map_pCoreIn_of_injective _ _ _ (MulAut.conj m).injective]
  change (((parabolic source.projection source.flag i).pCoreIn 2).map
    (MulAut.conj m).toMonoidHom).map (embedM R) =
    (((parabolic source.projection source.flag i).pCoreIn 2).map (embedM R)).map
      (MulAut.conj (embedM R m)).toMonoidHom
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

/-- Choose the incident flag while retaining the original first parabolic.
The endpoint crossing, intrinsic core identity and edge-star normalization
are proved on that same flag. -/
theorem exists_compatible_frame_of_frame
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (k : Sections.Frame source) :
    ∃ f : Seed.Frame source, Seed.Compatible f s ∧
      f.parabolic false = parabolic source.projection source.flag k.orientation := by
  have hc : color R s.endpoint = false :=
    (DistanceEight.PathCentrality.CriticalPath.ofPair
      (geometry := geometry) rfl s.critical).end_color
  have hn : ¬ Z R s.endpoint ≤ Q R (alpha R) :=
    (common.critical_reverse _ rfl _ hc s.critical).2
  have hQ : Z R s.endpoint ≤ Q R (beta R) := by
    apply Z_le_Q_of_dist_lt R s.endpoint (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc]
    change (cosetGraph R).dist s.endpoint (beta R) < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle
      (u := s.endpoint) (v := s.middle) (w := beta R)
    have hmb : (cosetGraph R).dist s.middle (beta R) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
        (adjacent_symm R hbc))
    have hem : (cosetGraph R).dist s.endpoint s.middle = 2 := by
      rw [SimpleGraph.dist_comm]; exact s.second_distance
    omega
  obtain ⟨a, ha, hcross⟩ := Incident.exists_incident_crossing source k.orientation
    (Z R s.endpoint) (hQ.trans_eq k.edge_kernel.symm) hn
  obtain ⟨m, hm, ham⟩ := (flagIncident_one_iff source k.orientation a).mp ha
  have hmcore : localFlagKernel source (!k.orientation) m =
      localFlagKernel source (!k.orientation) a := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source (!k.orientation) a (a⁻¹ * m) ham
  let f : Seed.Frame source := ⟨source.projection m * source.flag, k.orientation⟩
  have hfirst : f.parabolic false =
      parabolic source.projection source.flag k.orientation := by
    change parabolic source.projection (source.projection m * source.flag) k.orientation = _
    rw [parabolic_reflag]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((parabolic source.projection source.flag k.orientation).le_normalizer hm)
  refine ⟨f, ⟨?_, ?_, ?_⟩, hfirst⟩
  · change ((f.parabolic false).pCoreIn 2).map (embedM R) = _
    rw [hfirst]
    exact k.edge_kernel
  · change (f.parabolic false).map (embedM R) ≤ _
    rw [hfirst]
    exact flagParabolic_normalizes_edgeStar common radius k.orientation k.edge_kernel
  · change ¬ Z R s.endpoint ⊓
      ((parabolic source.projection (source.projection m * source.flag)
        (!k.orientation)).pCoreIn 2).map (embedM R) ≤ Q R (alpha R)
    rw [embedded_core_reflag, hmcore]
    exact hcross

/-- The compatible seed frame exists under the original distance-four source
hypotheses, with no extra selection or normalization input. -/
theorem exists_compatible_frame
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) :
    ∃ f : Seed.Frame source, Seed.Compatible f s := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  obtain ⟨f, hf, _⟩ := exists_compatible_frame_of_frame common radius hb s hbc k
  exact ⟨f, hf⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
