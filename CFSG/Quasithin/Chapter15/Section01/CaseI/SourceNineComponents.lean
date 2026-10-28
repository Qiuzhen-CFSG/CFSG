module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineMovement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OddCoreMovement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.LocalEvenSetup
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentModels
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Source Case-I components in the elementary-nine row

The same orthogonal marking supplies the residual intersection, Sylow
centralizer and normalizer controls. Its moved subgroup is idempotent under
the literal centralizer residual, and the fixed-space calculation places a
nontrivial central seed in its join with the marked line. A.1.26 and 1.1.5
then kill the odd core of the original centralizer. The existing C.2.6 and
A.4.4 argument constructs an outside C-component with quasisimple two-core
quotient, and the residual and moved subgroup normalize and move it.

The immediate local-family and Sylow conclusions of 15.1.20 use this same
component. No odd-core, component, marked normality or finite model witness
is assumed. The genuine earlier 15.1.14(1) residual-centralization premise
remains explicit for the Chapter15 assembly owner.

Source: Aschbacher--Smith 15.1.16(b)--19 and the opening of 15.1.20,
printed pp.1092--1094.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the source component from a prescribed actual image marker.
The equality for Z1 keeps later plane and residual calculations attached
to exactly this component. -/
theorem PreparedChosenModule.caseI_component_of_marked_image
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
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∀ (v : Additive V) (K : Subgroup (internalActionImage M V h.normalized)),
      v ≠ 0 →
      v ∈ fixedSpace (imageRepresentation M V h.normalized)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict) →
      (∀ d, d ∈ K ↔ imageRepresentation M V h.normalized d v = v) →
      K ⊔ (((T : Subgroup G).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict) = ⊤ →
      Nat.card K = 6 →
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
        (((T : Subgroup G).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict) ⊓ K) →
      (fixedSpace (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) ≤
        Submodule.span (ZMod 2) {v} ⊔ subspaceCommutator (imageRepresentation M V h.normalized)
          ⊤ ((pResidual 2 K).map K.subtype)) →
      ∃ d : CaseIComponentData T M Mc V, d.Z1 = zpowers (v.toMul : G) ∧
        d.row = .four ∧ Nat.card d.Z1 = 2 ∧
        pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
        d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
        let V2 := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
        V2 ≤ V ∧ (pResidual 2 (M ⊓ normalizer (d.Z1 : Set G) : Subgroup G)).map
          (M ⊓ normalizer (d.Z1 : Set G)).subtype ⊔ V2 ≤
          normalizer (d.L : Set G) ∧ ⁅d.L,V2⁆ ≠ ⊥ := by
  let := h.elementary
  intro v K hv hfixed hK hgen hc hSyl hb
  let Z1 := zpowers (v.toMul : G)
  let G1 := centralizer (Z1 : Set G)
  let R := (pResidual 2 (M ⊓ G1 : Subgroup G)).map (M ⊓ G1).subtype
  let V2 := ⁅V,R⁆
  obtain ⟨hZ,hZne,hgenZ,hSylZ⟩ :=
    marked_zpowers_and_sylow_of_image_stabilizer T hM.1.2 h.normalized v hv hfixed K hK hgen hSyl
  have hprime : letI := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      Nat.card (pResidual 2 ((M ⊓ G1 : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ G1))) = 3 := by
    let := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
    apply card_twoResidual_of_card_six
    exact (marked_quotient_card M V h.normalized v K hK (zpowers_le.mpr v.toMul.property)).trans hc
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
    (hZ.trans inf_le_left) hNMc hTMc hMnot hgenZ hSylZ (by
      let := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      rw [hprime]
      decide)
  have hSnT := chosen_nine_centralizer_normal T hM.1.2 h.normalized
    (hZ.trans inf_le_left) h9
  have hTn := h.caseI_T_normalizes_MZ_from_source hG T hempty hM hJ hu hZ hSylZ hSnT hI hres
  have hSylG := h.caseI_centralizer_sylow hG T hM hJ hZ
    (by
      rw [inf_comm (centralizer (Z1 : Set G)) M]
      exact hSylZ)
  obtain ⟨P,hP⟩ := hSylG
  have hZelem : IsElementaryAbelian 2 Z1 := IsElementaryAbelian.of_le (hZ.trans inf_le_left)
  have h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z := by
    intro z hz hzne
    exact CaseIMarkedSubgroup.central_involution_hypotheses hG hu hZne hZelem P
      (hP.le.trans inf_le_left) hz hzne
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
    have hbound := marked_fixedSpace_seed_bound T h.normalized v K hK hb
    intro he
    apply hseed
    exact bot_unique ((le_inf inf_le_left hbound).trans_eq he)
  have ho := h.caseI_oddCore_eq_bot hG Z1 V2 hZ hmove.1 P hmove.2 hplus h115
  obtain ⟨hcontrol,hn⟩ := CaseIMarkedSubgroup.core_normalizer_control
    hZ hZne hgenZ hM hu hne h hres hTn
  have hQne := CaseIMarkedSubgroup.core_nontrivial hZ hZne hM hu h
  have hescape := (CaseIMarkedSubgroup.residual_and_uniqueness hZ hgenZ hM hu hne hres).2.1
  have hresN := CaseIMarkedSubgroup.residual_normalizer_control hG
    hZ hZne hgenZ hM hu hne h hmany hres hTn ⟨P,hP⟩
  obtain ⟨L,hLG1,hLc,hq,hout⟩ := source_caseI_15_1_19_6_of_global_control hG M Mc Z1
    hZne (by let := hZelem; exact IsElementaryAbelian.isPGroup 2 Z1)
    hQne hcontrol hn ho hescape (inf_le_inf_left _ hresN)
  let d : CaseIComponentData T M Mc V := {
    row := .four, Z1 := Z1, Z1_le_fixed := hZ, Z1_ne_bot := hZne,
    M_eq_centralizer_sup_sylow := hgenZ, L := L,
    L_component := ⟨hLG1,hLc⟩, L_not_le_MZ := hout }
  have hZcard : Nat.card Z1 = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property)
    intro he
    apply hv
    apply Additive.toMul.injective
    exact Subtype.ext he
  have hNZ : normalizer (Z1 : Set G) = G1 :=
    le_antisymm (normalizer_le_centralizer_of_card_two Z1 hZcard)
      (Subgroup.centralizer_le_normalizer _)
  have hV2G : V2 ≤ G1 := hmove.1.trans
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left)))
  have hm := source_caseI_component_movement hG T M Mc Z1 V2 L P hV2G hmove.2 hplus h115
    ⟨hLG1,hLc⟩ hout
  have hH : G1 ∈ Chapter1.H G := by
    obtain ⟨z,hz,hzne⟩ := (centralInvolutions T ⊓ (Z1 ⊔ V2)).bot_or_exists_ne_one.resolve_left hplus
    exact (h115 z hz.1 hzne).mem_H
  have hloc := ComponentModels.source20_mem_L_of_cComponent hH ⟨P,hP⟩ hLG1 hLc
  refine ⟨d,rfl,rfl,hZcard,ho,hq,hloc,ComponentModels.source20_sylow_intersection hloc,?_⟩
  refine ⟨hmove.1,?_,hm.2⟩
  change (pResidual 2 (M ⊓ normalizer (Z1 : Set G) : Subgroup G)).map
    (M ⊓ normalizer (Z1 : Set G)).subtype ⊔ V2 ≤ normalizer (L : Set G)
  rw [hNZ]
  exact hm.1
/-- Original 15.1.19(1),(6),(7) in the Nine row, including the immediate
15.1.20 local-family and Sylow conclusions. The marked subgroup, original
centralizer, component and residual maps are constructed from the source
module. Only the earlier 15.1.14(1) residual centralization remains explicit. -/
theorem PreparedChosenModule.source_caseI_nine_components
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
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      let V2 := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
      V2 ≤ V ∧ (pResidual 2 (M ⊓ normalizer (d.Z1 : Set G) : Subgroup G)).map
        (M ⊓ normalizer (d.Z1 : Set G)).subtype ⊔ V2 ≤ normalizer (d.L : Set G) ∧
        ⁅d.L,V2⁆ ≠ ⊥ := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,_,hd⟩ := h.caseI_component_of_marked_image
    hG T hempty hM hmany hJ hu hne hfull h9 hres
    v K hv hfixed hK hgen hcard hSyl hbound
  exact ⟨d,hd⟩

end CFSG.Quasithin.Chapter15.Section01
