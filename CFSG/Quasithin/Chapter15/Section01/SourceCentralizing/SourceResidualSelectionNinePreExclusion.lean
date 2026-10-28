module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMarkedControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMarkedNormalization
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Nine

/-!
# The original Nine exchanged source without global residual centralization

The maximal-overgroup pair and normalization of the marked centralizer
supply the core and residual normalizer controls used in component selection.
The original marker, faithful residual, component and exchanged planes are
preserved. In the Nine row the four-element fixed subgroup gives the marked
normalization, independently of the global residual conclusion.

Source: Aschbacher--Smith 15.1.16(b)--20 and 15.1.24--25,
printed pp.1092--1094 and 1101--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the actual outside component for any of the three source
markers. The supplied marker is preserved literally, including its prime. -/
theorem PreparedChosenModule.component_of_preExclusionMarker_of_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hTn : (T : Subgroup G) ≤ normalizer (centralizer (m.Z1 : Set G) ⊓ Mc : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc := by
  let := h.elementary
  let Z1 := m.Z1
  let G1 := centralizer (Z1 : Set G)
  let R := (pResidual 2 (M ⊓ G1 : Subgroup G)).map (M ⊓ G1).subtype
  let V2 := ⁅V,R⁆
  have hZ := m.marked_fixed
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hNMc : M ⊓ centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact inf_le_right.trans (localModule_centralizer_le_partner T M hu)
  have hMnot : ¬ M ≤ Mc := fun hm => hne (hM.1.1.eq_of_le hMc.1.1 hm)
  have hI := caseI_residual_intersection T M Mc V Z1 h.normalized
    (hZ.trans inf_le_left) hNMc hTMc hMnot m.generates m.local_sylow (by
      let := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      rw [m.residual_card]
      exact m.prime_prime)
  have hSylG := h.caseI_centralizer_sylow hG T hM hJ hZ (by
    rw [inf_comm (centralizer (Z1 : Set G)) M]
    exact m.local_sylow)
  obtain ⟨P,hP⟩ := hSylG
  have hZelem : IsElementaryAbelian 2 Z1 := IsElementaryAbelian.of_le (hZ.trans inf_le_left)
  have h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z := by
    intro z hz hzne
    exact CaseIMarkedSubgroup.central_involution_hypotheses hG hu m.marked_nontrivial
      hZelem P (hP.le.trans inf_le_left) hz hzne
  have hmove : V2 ≤ V ∧ ⁅V2,R⁆ = V2 := marked_residual_movement h.normalized Z1
  have hplus : centralInvolutions T ⊓ (Z1 ⊔ V2) ≠ ⊥ := by
    have hseed : centralInvolutions T ⊓ V ≠ ⊥ := by
      intro hz
      apply h.nontrivial
      rw [h.seed_span,hz]
      exact bot_unique (conjugateSpanBy_le bot_le (by
        change M ≤ normalizer (⊥ : Subgroup G)
        rw [normalizer_eq_top]
        exact le_top))
    intro he
    exact hseed (bot_unique ((le_inf inf_le_left m.seed_bound).trans_eq he))
  have ho := h.caseI_oddCore_eq_bot hG Z1 V2 hZ hmove.1 P hmove.2 hplus h115
  obtain ⟨hcontrol,hn⟩ := h.marked_core_normalizer_control_of_pair
    hG T hempty hM hmany hJ hu htwo hZ m.marked_nontrivial hTn
  have hQne := CaseIMarkedSubgroup.core_nontrivial hZ m.marked_nontrivial hM hu h
  have hescape : ¬ M ⊓ G1 ≤ G1 ⊓ Mc := by
    intro hc
    apply hMnot
    rw [m.generates]
    exact sup_le (hc.trans inf_le_right) hTMc
  have hresN := h.marked_residual_normalizer_control_of_pair
    hG T hempty hM hmany hJ hu htwo hZ m.marked_nontrivial hTn ⟨P,hP⟩
  obtain ⟨L,hLG1,hLc,hq,hout⟩ := source_caseI_15_1_19_6_of_global_control hG M Mc Z1
    m.marked_nontrivial (by let := hZelem; exact IsElementaryAbelian.isPGroup 2 Z1)
    hQne hcontrol hn ho hescape (inf_le_inf_left _ hresN)
  let d : CaseIComponentData T M Mc V := {
    row := m.row, Z1 := Z1, Z1_le_fixed := hZ, Z1_ne_bot := m.marked_nontrivial,
    M_eq_centralizer_sup_sylow := m.generates, L := L,
    L_component := ⟨hLG1,hLc⟩, L_not_le_MZ := hout }
  have hV2G : V2 ≤ G1 := hmove.1.trans
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left)))
  have hm := source_caseI_component_movement hG T M Mc Z1 V2 L P
    hV2G hmove.2 hplus h115 ⟨hLG1,hLc⟩ hout
  have hH : G1 ∈ Chapter1.H G := by
    obtain ⟨z,hz,hzne⟩ := (centralInvolutions T ⊓ (Z1 ⊔ V2)).bot_or_exists_ne_one.resolve_left hplus
    exact (h115 z hz.1 hzne).mem_H
  have hloc := ComponentModels.source20_mem_L_of_cComponent hH ⟨P,hP⟩ hLG1 hLc
  refine ⟨d,rfl,rfl,?_,hresN⟩
  exact {
    prime_prime := m.prime_prime
    residual_card := m.residual_card
    odd_core := ho
    quasisimple := hq
    local_component := hloc
    component_sylow := ComponentModels.source20_sylow_intersection hloc
    centralizer_sylow := ⟨P,hP⟩
    outside_M := d.L_not_le_M hG T hempty hM hu
    ordinary := d.ordinarySource hG hu h hM.1.2 ⟨P,hP⟩ ho
    sylow_normal := m.sylow_normal
    residual_intersection := hI
    residual_normalizes := hm.1
    seed_bound := m.seed_bound
    moving_noncentral := hm.2
    core_nontrivial := hQne
    characteristic_control := hcontrol
    core_normalizer := hn
    sylow_normalizes_MZ := hTn
    sylow_normalizes_Q1 := d.T_normalizes_Q1_of_T_normalizes_MZ hTn }


/-- The actual Nine marker produces the full original component source and
its marked residual-normalizer control without global residual centralization. -/
theorem PreparedChosenModule.nine_preExclusion_component_without_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      d.PreExclusionSource h.normalized 3 ∧ d.ExchangedPlaneGeometry ∧
      normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc := by
  let := h.elementary
  obtain ⟨m,hr,hp,hc,hplanes⟩ := chosen_nine_preExclusionMarker T hM.1.2 h.normalized h9
  have hpair := h.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hTn : (T : Subgroup G) ≤ normalizer (centralizer (m.Z1 : Set G) ⊓ Mc : Set G) := by
    simpa only [inf_comm] using h.nine_marked_partner_centralizer_normalized
      hG T hempty hM hmany hJ hu hne hfull h9 hstrict m.marked_fixed
  obtain ⟨d,hZ,hd,s,hn⟩ := h.component_of_preExclusionMarker_of_pair
    hG T hempty hM hmany hJ hu hne hfull m hpair hTn
  exact ⟨d,hd.trans hr,by simpa only [hZ] using hc,hp ▸ s,hplanes d hZ hd,hn⟩

/-- The coherent original Nine component carries both the earlier source
and the exchanged-source conclusion, with its marked residual normalizer. -/
theorem PreparedChosenModule.nine_exchanged_without_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      d.PreExclusionSource h.normalized 3 ∧ d.ExchangedPlaneGeometry ∧
      d.ExchangedSource ∧
      normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc := by
  obtain ⟨d,hr,hc,s,g,hn⟩ := h.nine_preExclusion_component_without_residual
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict
  exact ⟨d,hr,hc,s,g,s.exchangedSource hG h g,hn⟩

end CFSG.Quasithin.Chapter15.Section01
