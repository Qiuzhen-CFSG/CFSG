module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.AdequateSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.Preliminary
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.KnownSimple
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound.OddMover

/-!
# Original rank-one characteristic-two component extraction

The corrected adequate B.5 theorem selects an escaping ordinary component
of the actual Thompson image. Genuine A.3.9 residual generation lifts it to
a C-component, and the proved orbit bound controls its normalizer. The
complete A.3.6 theorem then gives the intrinsic quasisimple two-core quotient.
All classifications are instantiated on the full known-simple catalogue.
Applying the same construction to every smaller outside overgroup supplies
the solvable-invariant control of 15.3.26(3).

Source: Aschbacher–Smith 15.3.26(1–3), printed p.1130.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem layer_eq_residual_knownSimple
    (h : IsSQTK KnownSimple.IsKnownSimple G) :
    cComponentLayer G = solvableResidual G := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  apply cComponentLayer_eq_residual_of_quotient (pCore 2 G)
  exact ChapterA.Section03.SourceComponents.generation
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    (StarSelection.Lifting.sqtk_twoCore_quotient h) (pCore_quotient_pCore_eq_bot 2)

private theorem cComponent_index_le_two_knownSimple
    (h : IsSQTK KnownSimple.IsKnownSimple G) {L : Subgroup G}
    (hL : L.IsCComponent) : (normalizer (L : Set G)).index ≤ 2 := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  have hb := cComponent_normal_or_index_two_of_quotient hL (pCore 2 G)
    (ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      (StarSelection.Lifting.sqtk_twoCore_quotient h)
      (pCore_quotient_pCore_eq_bot 2) (hL.map_quotient _))
  rcases hb with hn | hi
  · let _ := hn
    simp only [normalizer_eq_top, index_top]
    decide
  · exact hi.le

/-- Lift the literal star component using only proved earlier source theorems. -/
theorem exists_thompsonStar_component_lift
    (d : LocalData G) {I : Subgroup G} (hI : IsSQTK KnownSimple.IsKnownSimple I)
    (E : Subgroup (d.thompsonStar I))
    (hE : IsComponent (d.thompsonStar I) E) :
    ∃ L : Subgroup G, L ≤ Stellmacher.elementaryAbelianMaxJ I ∧
      (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent ∧
      d.starImage I L = E.map (d.thompsonStar I).subtype ∧
      (normalizer (L : Set G)).relIndex I ≤ 2 := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  have hJI : J ≤ I := sSup_le fun _ hA => hA.1
  let f : J →* d.thompsonStar I := d.componentStarMap hJI
  have hf : Function.Surjective f := d.componentStarMap_surjective hJI
  have hJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJI)).mp (hI.subgroup (J.subgroupOf I))
  obtain ⟨D, hD, hDE⟩ := exists_cComponent_map_eq_of_preimage_layer f hf hE.isCComponent
    (layer_eq_residual_knownSimple (hJ.subgroup (E.comap f)))
  let L := D.map J.subtype
  have hLJ : L ≤ J := map_subtype_le D
  have hL : (L.subgroupOf J).IsCComponent := by
    simpa only [L, subgroupOf, comap_map_eq_self_of_injective J.subtype_injective] using hD
  refine ⟨L, hLJ, hL, ?_, ?_⟩
  · rw [← hDE]
    change (L.subgroupOf I).map (d.starMap I) = _
    have he : L.subgroupOf I = D.map (inclusion hJI) := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le (hLJ.trans hJI), map_map, subtype_comp_inclusion]
    rw [he, map_map, map_map]
    rfl
  · have hLI := LocalData.thompson_component_in hLJ hL
    have hb := cComponent_index_le_two_knownSimple hI hLI
    rwa [← subgroupOf_normalizer_eq (hLJ.trans hJI)] at hb


/-- Corrected adequate B.5 constructs a candidate on the original star map. -/
theorem exists_starComponentCandidate
    (d : LocalData G) {I : Subgroup G}
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple I) (hI : I ∈ d.Hplus)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) (hθ : theta (d.MI I) = d.Yplus)
    (hN : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M) :
    ∃ c : StarComponentCandidate d I, (normalizer (c.L : Set G)).relIndex I ≤ 2 := by
  have hZS := d.Z_le_S hVT
  have hZI := hZS.trans (Chapter1.isSylowIn_iff.mp hS).2.1
  let _ := d.UI_subgroupOf_elementary hS hZS hf
  have hff := d.thompsonStarFFHypothesis hSQTK hZI hS hZS
  have hclass := FFAlternatives.SourceB5.classification.general _ _ _ hff
  have hcore := FFAlternatives.SourceB5.classification.threePrimeCore_eq_bot _ hff
    (d.thompsonStarAction_isFFModule I hZI hJ)
  obtain ⟨P, hP⟩ := d.exists_starSylow hS
  obtain ⟨E, hE, houtside⟩ := AdequateSelection.exists_component_outside
    (d.thompsonStar I) (d.starImage I d.Yplus) (d.starImage I d.M) P
    (d.starYplus_twoPerfect hI hθ)
    (by rw [hP]; exact map_mono (comap_mono (inf_le_left.trans d.sylow_le)))
    hN hJ (d.thompsonStarAction I hZI) (d.thompsonStarAction_generated I hZI) hclass
  obtain ⟨L, hLJ, hL, himage, horbit⟩ := exists_thompsonStar_component_lift d hSQTK E hE
  exact d.exists_starComponentCandidate_of_lift E hE houtside hcore hLJ hL himage horbit

private theorem yplus_twoCore_quotient_three
    (d : LocalData G) {I : Subgroup G} (h : OutsideStructure.Conclusions d I)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) := by
  have hne : d.Yplus ≠ ⊥ := by
    intro he
    apply h.action_normalizer.2.2
    simp [LocalData.starImage, localActionImage, he]
  have hi := RankOne.index_three_of_shadow hshadow
    (by rw [h.theta_eq, theta_idempotent]) hne
  exact IsPGroup.of_card (n := 1) hi

/-- Both genuine preliminary alternatives have a three-group two-core quotient.
This retains the rank-two case for the separate source15.3.13 argument. -/
theorem source_yplus_twoCore_quotient_isThreeGroup
    (d : LocalData G) {I : Subgroup G} (h : OutsideStructure.Conclusions d I) :
    IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) := by
  rcases h.local_structure with ht | ho
  · have hcubic : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus) := ht.1
    rcases hcubic with he | ⟨_, hc, _⟩
    · obtain ⟨e⟩ := he
      apply IsPGroup.of_card (n := 2)
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod 3) = 3 ^ 2
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    · exact IsPGroup.of_card (n := 3) hc
  · exact yplus_twoCore_quotient_three d h ho.2.1

/-- The actual S₃ shadow selects every clause of15.3.26(1), without rank-two elimination. -/
theorem source_lemma_15_3_26_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.Hplus) :
    RankOneConfiguration.Parabolics.RankOneFacts d I := by
  have h := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hne : d.Yplus ≠ ⊥ := by
    intro he
    apply h.action_normalizer.2.2
    simp [LocalData.starImage, localActionImage, he]
  have hi : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 3 :=
    RankOne.index_three_of_shadow hshadow
      (by rw [h.theta_eq, theta_idempotent]) hne
  rcases h.local_structure with htwo | hone
  · have hcubic : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus) := htwo.1
    rcases hcubic with he | ⟨_, hc, _⟩
    · obtain ⟨e⟩ := he
      have hc := Nat.card_congr e.toEquiv
      have hh : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
        change Nat.card (Fin 2 → ZMod 3) = 9
        norm_num only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rw [hh, hi] at hc
      omega
    · omega
  · exact ⟨hone.1, hone.2.1, hone.2.2.1, hone.2.2.2⟩

/-- Original15.3.26(2), without any remaining B.5 or component-selection premise. -/
theorem source_lemma_15_3_26_2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I) :
    Nonempty (ComponentWitness d I) := by
  have h := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hS : Chapter1.IsSylowIn 2 d.S I := h.sylow
  have hSQTK := OutsideStructure.outside_sqtk hG d hI
  have hVT := d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  obtain ⟨c,hindex⟩ := exists_starComponentCandidate d hSQTK hI hVT hS hf
    h.theta_eq.symm h.action_normalizer.1 h.thompson_outside
  exact ⟨c.componentWitness_of_source
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    hSQTK hI h.theta_eq.symm hindex h.centralizer_le h.action_normalizer.1
    (source_yplus_twoCore_quotient_isThreeGroup d h)⟩

/-- Original15.3.26(3), using extraction uniformly on the actual smaller outside groups. -/
theorem source_lemma_15_3_26_3
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (X : Subgroup G) (hXI : X ≤ I) (hX : Group.IsSolvable X)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (X : Set G)) : X ≤ d.MI I := by
  have h := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  exact d.solvable_invariant_le_of_components hI h.sylow hf
    (d.join_isSolvable_of_three_quotient hI h.theta_eq.symm
      (source_yplus_twoCore_quotient_isThreeGroup d h))
    (fun K _ hK hfK => source_lemma_15_3_26_2 hG d hempty hM hu hmany hK hfK)
    hXI hX hn

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
