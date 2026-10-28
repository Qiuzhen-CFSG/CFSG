module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Solvability
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import Theory.GroupTheory.GeneralizedFitting.LayerRankOrbit
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.OriginalSource

/-!
# Original source inputs for the rank-one component reduction

The selected local datum supplies the complete 15.3.7, 15.3.9 and 15.3.11
conclusions. The actual marked component theorem and the layer rank bound
supply the chosen component's orbit, center, positive rank and invariant
subgroup control. Only the earlier characteristic-two exclusion remains.

Source: Aschbacher--Smith 15.3.25, 15.3.33--34 and 15.3.43, pp.1130--1140.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_alternatives_of_original (d : CharacteristicTwo.LocalData G)
    (h : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    PlaneGeometry.SourceQuotientAlternatives d.Y d.V := by
  rcases OutsideStructure.earlier_three_alternatives_of_source d h with h | ⟨h, _, _⟩
  · obtain ⟨e⟩ := h.quotient_equiv
    let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro x
        apply Multiplicative.toAdd.injective
        change 3 • x.toAdd = 0
        funext i
        exact (by decide : ∀ a : ZMod 3, 3 • a = 0) _ }
    refine Or.inl ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  · refine Or.inr ⟨h.extraspecial, h.quotient_card, ?_⟩
    have hc := congrArg (fun K : Subgroup G => K.subgroupOf d.Y) h.centralizer_eq
    rw [inf_subgroupOf_left, FusionCore.CosetSetup.ExtraspecialLocal.twoCenter,
      subgroupOf_map_subtype_eq] at hc
    rw [hc, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- The source rank bound alone controls every ordinary component orbit. -/
theorem original_component_orbit_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : IsComponent I (L.subgroupOf I)) :
    (normalizer (L : Set G)).relIndex I ≤ 2 := by
  have hr := OutsideStructure.outside_stronglyQuasithin hG.quasithin d.Yplus d.S d.M I hI
  have ho := hL.normal_or_index_two_of_layer_odd_rank_le_two
    (fun p hp ho => (hr.subgroup (componentLayer I)) p hp ho)
  change ((normalizer (L : Set G)).subgroupOf I).index ≤ 2
  rw [subgroupOf_normalizer_eq hLI]
  rcases ho with hn | hi
  · let := hn
    rw [normalizer_eq_top, index_top]
    decide
  · exact hi.le

/-- Original local data supplies the reduction inputs once 15.3.25 and
its chosen component's marked 15.3.33 conclusion have been established. -/
theorem reduction_inputs_of_original_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (h25 : ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A)
    {I L : Subgroup G} (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : IsComponent I (L.subgroupOf I)) {z : G}
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z) :
    ReductionSourceInputs d I L := by
  have h11 (A : Subgroup G) (hA : A ∈ d.Hplus) :=
    OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany A hA
  have h11I := h11 I hI
  obtain ⟨hne, _, _⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨himage, _, _, _, _, hcore, hquot⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have h9 := source_lemma_15_3_9_of_orthogonal_action
    hG d.T hempty d.action hM hu hmany hne
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hYLne : d.Yplus ≠ ⊥ := by
    intro he
    apply h11I.action_normalizer.2.2
    simp [CharacteristicTwo.LocalData.starImage, localActionImage, he]
  have hindex := index_three_of_shadow hshadow
    (by rw [h11I.theta_eq, theta_idempotent]) hYLne
  have hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [pow_one, ← Subgroup.index_eq_card] using hindex
  have hSylow : OutsideSylowControl d.Yplus d.S d.M := fun A hA => (h11 A hA).sylow
  have hodd : ∀ A ∈ d.Hplus, pPrimeCore 2 A = ⊥ := fun A hA => (h11 A hA).odd_core
  have horbit := original_component_orbit_bound hG d hI hLI hL
  have hrank := (Candidates.SuzukiExclusion.lemma_15_3_34 hI hSylow h25 hodd hSM
    h11I.normalizer_eq hY h11I.theta_eq hLI hL h33 horbit).2
  let eL := subgroupOfEquivOfLe hLI
  have hc : (center (L.subgroupOf I)).map eL.toMonoidHom = center L := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr eL ⟨x, hx⟩).property
    · intro x hx
      exact ⟨eL.symm x, ((Subgroup.centerCongr eL).symm ⟨x, hx⟩).property,
        eL.apply_symm_apply x⟩
  have hZ : center L = pCore 2 L := by
    rw [← hc, component_center_eq_twoCore hL h11I.odd_core, pCore_map_iso]
  refine {
    characteristic_two := hG.evenCharacteristic d.T d.M hM.1.1 d.sylow_le
    residual_image := himage
    residual_core := hcore
    residual_quotient := quotient_alternatives_of_original d hquot
    not_alternating_square := h9.2
    outside_structure := h11I
    outside_not_characteristic_two := h25
    component_le := hLI
    component := hL
    component_center := by rw [hZ]; rfl
    component_outside := by simpa only [map_subgroupOf_eq_of_le hLI] using h33.outside
    component_rank := hrank
    overgroup_rank := OutsideStructure.outside_stronglyQuasithin
      hG.quasithin d.Yplus d.S d.M I hI 3 Nat.prime_three (by decide)
    component_orbit := horbit
    invariant_subgroup := ?_ }
  intro D hD hDN hDF
  have hspan : localSpan L d.S ≤ I :=
    conjugateSpanBy_le hLI ((le_sup_right.trans hI.1.2).trans I.le_normalizer)
  exact lemma_15_3_33_1_of_threeGroup_quotient hI hSylow h25 hodd hSM
    h11I.normalizer_eq hY (hD.trans hspan) hDN hDF

/-- Choose an actual ordinary component and construct every reduction input
from the original source data and the preceding characteristic-two exclusion. -/
theorem exists_reduction_inputs_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (h25 : ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A)
    {I : Subgroup G} (hI : I ∈ d.Hplus) :
    ∃ (L : Subgroup G) (z : G), ReductionSourceInputs d I L ∧
      Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨K, hK⟩ := exists_ordinary_component_of_fstar_ne_twoCore h11.odd_core (h25 I hI)
  obtain ⟨z, _, _, _, h33⟩ :=
    Candidates.ComponentStructure.ordinary_component_structure_from_selection
      hG d hempty hM hu hmany hI hK
  let L := K.map I.subtype
  have hLI : L ≤ I := map_subtype_le K
  have hrel : L.subgroupOf I = K := subgroupOf_map_subtype_eq K
  have hL : IsComponent I (L.subgroupOf I) := hrel.symm ▸ hK
  have h33L : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z :=
    hrel.symm ▸ h33
  exact ⟨L, z, reduction_inputs_of_original_component hG d hempty hM hu hmany
    hshadow h25 hI hLI hL h33L, h33L⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne
