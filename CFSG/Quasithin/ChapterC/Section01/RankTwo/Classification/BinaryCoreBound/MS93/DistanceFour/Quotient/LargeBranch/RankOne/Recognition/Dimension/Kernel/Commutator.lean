module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.Commutator.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils

/-!
# The unstarred midpoint commutator and index two

Keep U_delta2 as the literal preimage of the unstarred second layer, and
X₁ = U_delta2 intersect Q_c. Re-marking the existing source at the supplied
compatible flag allows the earlier three-neighbor theorem to apply: both
U_delta2 and Z_c lie in its incident span, whose derived subgroup lies in
Z_delta2. Their commutator also lies in V_alpha' = U_alpha. The actual
natural fixed-subgroup calculation gives |U_alpha intersect Z_delta2| = 2.

The two opposite cores generate the incident parabolic intersection. The
first is Q_beta and normalizes Q_c; the second centralizes U_delta2 modulo
Z_alpha, which lies in X₁. Thus their whole overlap normalizes X₁.
The final consumer applies Kernel.Index's published theorem to obtain the
exact unstarred index two from the original starred escape.

No natural-copy coordinates, starred replacement of U_delta2, dimension-six
hypothesis, or finiteness of the free amalgam is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on p.905 and (4.6.12)(5), final paragraph on printed p.912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private def reframe (f : Seed.Frame source) (s : CriticalSegment geometry)
    (hf : Seed.Compatible f s) : LocalSource L R :=
  { source with
    flag := f.flag
    edge_in_borel := by
      have hc : f.core false = R := map_injective (embedM_injective R)
        (hf.first_core.trans (Q_beta R))
      intro x hx
      have hm := mem_map_of_mem source.projection (hc.symm ▸ hx)
      rw [Seed.frame_core_image, Seed.frame_parabolic_image] at hm
      exact CommutatorModel.core_le_borel f.flag f.first hm
    weakBN := binaryWeakBN f.flag
    rank_one_generation := (rankOne_parabolic_generation source.projection
      source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup) f.flag).trans source.residual }

private def reframeCommon (common : CommonFacts R source geometry)
    (f : Seed.Frame source) (s : CriticalSegment geometry) (hf : Seed.Compatible f s) :
    CommonFacts R (reframe f s hf) geometry := { common with }

private theorem reframe_core (f : Seed.Frame source) (s : CriticalSegment geometry)
    (hf : Seed.Compatible f s) :
    Flags.RankOne.flagKernel (reframe f s hf) f.first = Q R (beta R) :=
  hf.first_core

private theorem secondPreimage_le_incidentSpan (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (s : CriticalSegment geometry) (hf : Seed.Compatible f s) :
    secondPreimage d f ≤ Flags.RankOne.BinaryAuxiliary.Y (reframe f s hf) f.first 1 := by
  let src := reframe f s hf
  let Y := Flags.RankOne.BinaryAuxiliary.Y src f.first (1 : M)
  have hZ : Z R (alpha R) ≤ Y := Flags.RankOne.BinaryAuxiliary.Z_le_Y src f.first 1
  have hY : Y ≤ V R (alpha R) := Flags.RankOne.BinaryAuxiliary.Y_le_radius src f.first 1
  have he : d.preimage (d.subspace Y) = Y := by
    rw [Seed.LayerModule.preimage_subspace_eq d Y hY,
      inf_eq_left.mpr (show Z R (alpha R) ≤ V R (alpha R) from Z_le_VBall R _ 2), sup_eq_right.mpr hZ]
  change secondPreimage d f ≤ Y
  rw [← he]
  intro x hx
  obtain ⟨hxV, hxW⟩ := (d.mem_preimage_iff _ x).mp hx
  apply (d.mem_preimage_iff _ x).mpr
  refine ⟨hxV, ?_⟩
  have hl : secondLayer d f 1 ≤ d.subspace Y := by
    apply iSup_le
    intro p
    apply inf_le_left.trans
    apply d.subspace_mono
    apply Flags.RankOne.BinaryAuxiliary.first_le_Y src f.first (1 * (p : M)) 1
    refine ⟨p, ?_, ?_⟩
    · simp only [one_mul, inv_mul_cancel]; exact one_mem _
    · change (1 : M)⁻¹ * (p : M) ∈ f.parabolic true
      simpa only [inv_one, one_mul] using p.property
  exact hl hxW

private theorem midpoint_Z_le_incidentSpan (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    Z R s.middle ≤ Flags.RankOne.BinaryAuxiliary.Y (reframe f s hf) f.first 1 := by
  have hZ : Z R s.middle ≤ V R (beta R) := by
    rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le s.middle (le_iSup_of_le hbc le_rfl)
  have hy := Flags.RankOne.BinaryAuxiliary.first_le_Y (reframe f s hf)
    f.first (1 : M) 1 (⟨1, by simp, by simp⟩)
  rw [Flags.RankOne.firstFlagLayer, Flags.RankOne.localConjugate_one] at hy
  exact hZ.trans hy

/-- The p.912 containment for the actual unstarred layer follows from the incident-span derived bound. -/
theorem secondPreimage_commutator_le_secondCenter
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    ⁅secondPreimage d f, Z R s.middle⁆ ≤ secondCenter f := by
  have h := (commutator_mono (secondPreimage_le_incidentSpan d f s hf)
    (midpoint_Z_le_incidentSpan s hbc f hf)).trans
    (Flags.RankOne.BinaryAuxiliary.Y_commutator_le_localZ (reframe f s hf)
      geometry (reframeCommon common f s hf) radius.toEarlyFacts f.first
      (reframe_core f s hf) 1)
  simp only [Flags.RankOne.localFlagZ, Flags.RankOne.localFlagKernel,
    Flags.RankOne.localConjugate_one] at h
  change ⁅secondPreimage d f, Z R s.middle⁆ ≤ secondCenter f at h
  exact h


/-- The incident overlap is generated by the two actual intrinsic cores, including the original projection kernel. -/
theorem incident_overlap_eq_core_sup (f : Seed.Frame source)
    (s : CriticalSegment geometry) (hf : Seed.Compatible f s) :
    f.ambient false ⊓ f.ambient true =
      (f.core false).map (embedM R) ⊔ (f.core true).map (embedM R) := by
  let src := reframe f s hf
  have hcore (i : Bool) : f.core i =
      ((modelParabolic f.flag (if i then !f.first else f.first)).pCoreIn 2).comap
        source.projection :=
    Flags.RankOne.Incident.parabolic_core_eq_comap src _
  have hm : (modelParabolic f.flag f.first).pCoreIn 2 ⊔
      (modelParabolic f.flag (!f.first)).pCoreIn 2 =
      modelParabolic f.flag f.first ⊓ modelParabolic f.flag (!f.first) := by
    cases f.first
    · exact CommutatorModel.model_core_sup f.flag
    · simpa only [modelBorel, Bool.not_true, sup_comm, inf_comm] using CommutatorModel.model_core_sup f.flag
  change (f.parabolic false).map (embedM R) ⊓ (f.parabolic true).map (embedM R) = _
  rw [← map_inf _ _ _ (embedM_injective R), ← Subgroup.map_sup, hcore, hcore]
  congr 1
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [comap_sup_eq source.projection _ _ source.projection_surjective, hm]
  rfl

/-- The complete incident overlap normalizes the literal X₁, with relative normality at the midpoint. -/
theorem incident_overlap_normalizes_midpointKernel
    (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    f.ambient false ⊓ f.ambient true ≤ normalizer (midpointKernel d f s.middle) := by
  have hj := incident_overlap_eq_core_sup f s hf
  have hfirst : (f.core false).map (embedM R) ≤ f.ambient true := by
    exact le_sup_left.trans (hj.symm.le.trans inf_le_right)
  rw [hj]
  apply sup_le
  · change (f.core false).map (embedM R) ≤ normalizer (secondPreimage d f ⊓ Q R s.middle)
    apply le_normalizer_inf (hfirst.trans (secondPreimage_normalized d f))
    rw [hf.first_core]
    exact (show Q R (beta R) ≤ stabilizer R s.middle from fun _ hx => hx.2 _ hbc).trans
      (Q_normalized R s.middle)
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono inf_le_left le_rfl).trans
      ((secondPreimage_commutator_core_le_Z d f).trans (Z_le_midpointKernel common s d f))


open RankOnePairing.Incidence.FixedGeometry.ValueConstruction in
private theorem natural_fixed_card (src : LocalSource L R)
    (natural : NaturalU R src.projection) (i : Bool) :
    Nat.card (U R (alpha R) ⊓ Flags.RankOne.localFlagZ src i 1 : Subgroup (FreeAmalgam R)) =
      Nat.card (Flags.RankOne.Pencils.matrixFixed natural.marking src.flag i 1) := by
  let T : Subgroup (FreeAmalgam R) := U R (alpha R) ⊓ Flags.RankOne.localFlagZ src i 1
  let F := Flags.RankOne.Pencils.matrixFixed natural.marking src.flag i 1
  have hfix (u : U R (alpha R)) :
      (u : FreeAmalgam R) ∈ Flags.RankOne.localFlagZ src i 1 ↔ natural.equiv u ∈ F := by
    simpa only [map_one] using Flags.RankOne.Pencils.natural_mem_localFlagZ_iff src natural i 1 u
  let e : T ≃ F := {
    toFun u := ⟨natural.equiv ⟨u.val,u.property.1⟩, (hfix _).mp u.property.2⟩
    invFun v := ⟨(natural.equiv.symm v).val, (natural.equiv.symm v).property,
      (hfix _).mpr (by simpa only [natural.equiv.apply_symm_apply] using v.property)⟩
    left_inv u := by
      apply Subtype.ext
      change (natural.equiv.symm (natural.equiv ⟨u.val, u.property.1⟩)).val = u.val
      exact congrArg Subtype.val (natural.equiv.symm_apply_apply _)
    right_inv v := Subtype.ext (natural.equiv.apply_symm_apply _) }
  exact Nat.card_congr e

/-- Only the intersection with the actual natural U_alpha has order two; the central complement in Z_alpha is retained. -/
theorem natural_inf_secondCenter_card
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (f : Seed.Frame source) (hf : Seed.Compatible f s) :
    Nat.card (U R (alpha R) ⊓ secondCenter f : Subgroup (FreeAmalgam R)) = 2 := by
  let src := reframe f s hf
  let cmn := reframeCommon common f s hf
  have hfirst : Flags.RankOne.localFlagZ src f.first 1 = Z R (beta R) := by
    unfold Flags.RankOne.localFlagZ Flags.RankOne.localFlagKernel
    rw [Flags.RankOne.localConjugate_one, reframe_core f s hf]
    exact (Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)).symm
  have hfour : Nat.card (U R (alpha R) ⊓ Flags.RankOne.localFlagZ src f.first 1 : Subgroup (FreeAmalgam R)) = 4 := by
    rw [hfirst, ← Flags.RankOne.edge_natural_fixed_plane src geometry cmn radius.toEarlyFacts
      f.first (reframe_core f s hf)]
    exact radius.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)
  have hsecond : Flags.RankOne.localFlagZ src (!f.first) 1 = secondCenter f := by
    unfold Flags.RankOne.localFlagZ Flags.RankOne.localFlagKernel
    rw [Flags.RankOne.localConjugate_one]
    rfl
  have hp := CommutatorModel.fixed_core_pair common.natural.marking f.flag f.first
  have hc1 := natural_fixed_card src cmn.natural f.first
  have hc2 := natural_fixed_card src cmn.natural (!f.first)
  simp only [Flags.RankOne.Pencils.matrixFixed, Flags.RankOne.Pencils.matrixCore_one] at hc1 hc2
  dsimp only [cmn, src, reframeCommon, reframe] at hc1 hc2
  rw [← hc1, ← hc2] at hp
  change Nat.card (U R (alpha R) ⊓ Flags.RankOne.localFlagZ src f.first 1 : Subgroup (FreeAmalgam R)) *
    Nat.card (U R (alpha R) ⊓ Flags.RankOne.localFlagZ src (!f.first) 1 : Subgroup (FreeAmalgam R)) = 8 at hp
  rw [hfour, hsecond] at hp
  omega

/-- The unstarred commutator lies in the order-two natural centralizer intersection. -/
theorem secondPreimage_commutator_card_le_two
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    Nat.card (⁅secondPreimage d f, Z R s.middle⁆ : Subgroup (FreeAmalgam R)) ≤ 2 := by
  have hc := natural_inf_secondCenter_card common radius s f hf
  let : Finite (U R (alpha R) ⊓ secondCenter f : Subgroup (FreeAmalgam R)) := Nat.finite_of_card_ne_zero (by omega)
  have hle : ⁅secondPreimage d f, Z R s.middle⁆ ≤ U R (alpha R) ⊓ secondCenter f :=
    le_inf ((commutator_mono (secondPreimage_le_radius d f) (Seed.midpoint_Z_le_radius s)).trans_eq
      (radius.radius_derived (alpha R) rfl))
      (secondPreimage_commutator_le_secondCenter common radius s hbc d f hf)
  exact (card_le_of_le hle).trans_eq hc

/-- Clause (4) escape makes the proved commutator bound sharp for the literal unstarred kernel. -/
theorem midpointKernel_relIndex_eq_two
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    (midpointKernel d f s.middle).relIndex (secondPreimage d f) = 2 :=
  midpointKernel_relIndex_eq_two_of_commutator_card_le_two common radius s hbc d f hescape
    (secondPreimage_commutator_card_le_two common radius s hbc d f hf)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
