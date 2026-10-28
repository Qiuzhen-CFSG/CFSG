module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Marker

/-!
# Component construction before eliminating source rows

For any original action marker, the local Sylow and prime residual give
the residual intersection and T-invariance of M_Z. A central seed kills
the odd core. The C.2.6 and A.4.4 extraction then constructs an outside
C-component; the source two-perfect action normalizes and moves it.
No surviving-row or component-model hypothesis is used.

Source: Aschbacher--Smith 15.1.18--20, printed pp.1092--1094.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the actual outside component for any of the three source
markers. The supplied marker is preserved literally, including its prime. -/
theorem PreparedChosenModule.component_of_preExclusionMarker
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime := by
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
  have hTn := h.caseI_T_normalizes_MZ_from_source hG T hempty hM hJ hu hZ
    m.local_sylow m.sylow_normal hI hres
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
  obtain ⟨hcontrol,hn⟩ := CaseIMarkedSubgroup.core_normalizer_control
    hZ m.marked_nontrivial m.generates hM hu hne h hres hTn
  have hQne := CaseIMarkedSubgroup.core_nontrivial hZ m.marked_nontrivial hM hu h
  have hescape := (CaseIMarkedSubgroup.residual_and_uniqueness
    hZ m.generates hM hu hne hres).2.1
  have hresN := CaseIMarkedSubgroup.residual_normalizer_control hG
    hZ m.marked_nontrivial m.generates hM hu hne h hmany hres hTn ⟨P,hP⟩
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
  refine ⟨d,rfl,rfl,{
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
    sylow_normalizes_Q1 := d.T_normalizes_Q1_of_T_normalizes_MZ hTn }⟩

end CFSG.Quasithin.Chapter15.Section01
