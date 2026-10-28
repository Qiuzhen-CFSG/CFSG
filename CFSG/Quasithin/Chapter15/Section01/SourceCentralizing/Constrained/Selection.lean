module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.FullSelection
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsControl
/-!
# One Nine marker with the original constrained-source controls

The marked image is chosen once. Its component, radical, cubic actor and
exchanged planes are retained together, so C.2.7 and the later module
comparison concern the original source objects.

Source: Aschbacher--Smith 15.1.16--19, 15.1.27--29, pp.1091--1104.
The earlier 15.1.14 residual input remains explicit.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
@[expose] def nineResidual (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
@[expose] def nineCubic (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
@[expose] def nineFixedPlane (d : CaseIComponentData T M Mc V) : Subgroup G :=
  V ⊓ centralizer (d.nineResidual : Set G)
@[expose] def nineMovingPlane (d : CaseIComponentData T M Mc V) : Subgroup G :=
  ⁅V,d.nineResidual⁆
/-- Literal same-marker data for the ordinary and constrained source branches. -/
structure NineSource (d : CaseIComponentData T M Mc V) : Prop where
  row : d.row = .four
  marked_card : Nat.card d.Z1 = 2
  odd_core : pPrimeCore 2 d.G1 = ⊥
  quasisimple : IsQuasisimple (d.L ⧸ pCore 2 d.L)
  local_component : d.L ∈ Chapter1.L G d.S
  component_sylow : Chapter1.IsSylowIn 2 d.SL d.L
  centralizer_sylow : Chapter1.IsSylowIn 2 d.S d.G1
  outside_M : ¬ d.L ≤ M
  ordinary : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinarySource
  fixed_card : Nat.card d.nineFixedPlane = 4
  moving_card : Nat.card d.nineMovingPlane = 4
  planes_sup : d.nineFixedPlane ⊔ d.nineMovingPlane = V
  planes_inf : d.nineFixedPlane ⊓ d.nineMovingPlane = ⊥
  marked_le_fixed : d.Z1 ≤ d.nineFixedPlane
  index : d.S.relIndex (T : Subgroup G) = 2
  sylow_normal : (d.S.subgroupOf (T : Subgroup G)).Normal
  fixes_planes : d.S ≤ normalizer (d.nineFixedPlane : Set G) ∧
    d.S ≤ normalizer (d.nineMovingPlane : Set G)
  fixed_centralizer_index : (centralizer (d.nineFixedPlane : Set G)).relIndex d.S = 2
  exchanges : ∀ t ∈ (T : Subgroup G), t ∉ d.S →
    d.nineFixedPlane.map (MulAut.conj t).toMonoidHom = d.nineMovingPlane ∧
    d.nineMovingPlane.map (MulAut.conj t).toMonoidHom = d.nineFixedPlane
  exchange_exists : ∃ t ∈ (T : Subgroup G), t ∉ d.S
  cubic_escape : ¬ d.nineCubic ≤ d.MZ
  cubic_idempotent : (primeToResidual 3 d.nineCubic).map d.nineCubic.subtype = d.nineCubic
  cubic_two_perfect : IsPPerfect 2 d.nineCubic
  cubic_normalizes : d.nineCubic ≤ normalizer (V : Set G)
  cubic_commutator : ⁅V,d.nineCubic⁆ = d.nineMovingPlane
  cubic_moving : ⁅d.nineMovingPlane,d.nineCubic⁆ = d.nineMovingPlane
  fixed_noncentral : Facts (d.L ⧸ pCore 2 d.L) →
    ¬ d.nineFixedPlane ≤ centralizer (d.L : Set G)
  seed_bound : centralInvolutions T ⊓ V ≤ d.Z1 ⊔ d.nineMovingPlane
  moving_noncentral : ⁅d.L,d.nineMovingPlane⁆ ≠ ⊥
  core_nontrivial : d.Q1 ≠ ⊥
  characteristic_control : d.Q1.characteristicNormalizerClosure ≤ Mc
  core_normalizer : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ
  sylow_normalizes_MZ : (T : Subgroup G) ≤ normalizer (d.MZ : Set G)
  sylow_normalizes_Q1 : (T : Subgroup G) ≤ normalizer (d.Q1 : Set G)
end CaseIComponentData
theorem PreparedChosenModule.source_caseI_nine_source_selection
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
    ∃ d : CaseIComponentData T M Mc V, d.NineSource := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  obtain ⟨hZ,_,_,hSylZ⟩ := marked_zpowers_and_sylow_of_image_stabilizer
    T hM.1.2 h.normalized v hv hfixed K hK hgen hSyl
  have hSylG : Chapter1.IsSylowIn 2 d.S d.G1 := by
    change Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (d.Z1 : Set G))
      (centralizer (d.Z1 : Set G))
    rw [hdZ]
    apply h.caseI_centralizer_sylow hG T hM hJ hZ
    rw [inf_comm (centralizer (zpowers (v.toMul : G) : Set G)) M]
    exact hSylZ
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let V1 := V ⊓ centralizer (R : Set G)
  let V2 := ⁅V,R⁆
  let Y := (primeToResidual 3 C).map C.subtype
  have hC : C = M ⊓ centralizer (zpowers (v.toMul : G) : Set G) := by
    change M ⊓ centralizer (d.Z1 : Set G) = _
    rw [hdZ]
  have hplanes : Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧
      V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 := by
    let P (Z : Subgroup G) : Prop :=
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 4 ∧ Nat.card (⁅V,R⁆ : Subgroup G) = 4 ∧
        (V ⊓ centralizer (R : Set G)) ⊔ ⁅V,R⁆ = V ∧
        (V ⊓ centralizer (R : Set G)) ⊓ ⁅V,R⁆ = ⊥ ∧
        Z ≤ V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp
  have haction : d.S.relIndex (T : Subgroup G) = 2 ∧
      d.S ≤ normalizer (V1 : Set G) ∧ d.S ≤ normalizer (V2 : Set G) ∧
      (centralizer (V1 : Set G)).relIndex d.S = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ d.S →
        V1.map (MulAut.conj t).toMonoidHom = V2 ∧
        V2.map (MulAut.conj t).toMonoidHom = V1 := by
    let P (Z : Subgroup G) : Prop :=
      let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      S.relIndex (T : Subgroup G) = 2 ∧ S ≤ normalizer (V1 : Set G) ∧
        S ≤ normalizer (V2 : Set G) ∧ (centralizer (V1 : Set G)).relIndex S = 2 ∧
        ∀ t ∈ (T : Subgroup G), t ∉ S →
          V1.map (MulAut.conj t).toMonoidHom = V2 ∧
          V2.map (MulAut.conj t).toMonoidHom = V1
    have hp : P (zpowers (v.toMul : G)) :=
      source_nine_plane_action T hM.1.2 h.normalized h9 v K hv hK hcard hSyl
    exact (congrArg P hdZ).mpr hp
  have hV2ne : V2 ≠ ⊥ := by
    intro he
    have hc := hplanes.2.1
    rw [he,card_bot] at hc
    omega
  have hYid : (primeToResidual 3 Y).map Y.subtype = Y := by
    rw [←map_embedded_primeToResidual_of_hom 3 (primeToResidual 3 C) C.subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 C) le_rfl]
  have he : ⁅V,Y⁆ = V2 := by
    dsimp only [Y,V2,R]
    rw [hC]
    exact marked_primeToResidual_commutator M V h.normalized v K hK hcard
  have hYp : IsPPerfect 2 Y := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hYV : Y ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  have hV2Y : ⁅V2,Y⁆ = V2 := by
    rw [←he]
    exact commutator_isPPerfect_idempotent Y V hYp (IsElementaryAbelian.isPGroup 2 V) hYV
  have hYnon : ¬ Y ≤ centralizer (V : Set G) := by
    intro hc
    have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [commutator_comm,he] at hh
    exact hV2ne hh
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMnot : ¬ M ≤ Mc := fun hm => hne (hM.1.1.eq_of_le hMc.1.1 hm)
  have hNMc : M ⊓ centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact inf_le_right.trans (localModule_centralizer_le_partner T M hu)
  obtain ⟨hZ,hZne,hgenZ,hSylZ⟩ := marked_zpowers_and_sylow_of_image_stabilizer
    T hM.1.2 h.normalized v hv hfixed K hK hgen hSyl
  have hprime : letI := caseI_module_centralizer_normal (Z1 := zpowers (v.toMul : G)) h.normalized
      (Nat.card (pResidual 2 ((M ⊓ centralizer (zpowers (v.toMul : G) : Set G) : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf
          (M ⊓ centralizer (zpowers (v.toMul : G) : Set G))))).Prime := by
    let := caseI_module_centralizer_normal (Z1 := zpowers (v.toMul : G)) h.normalized
    have hh := marked_quotient_card M V h.normalized v K hK (zpowers_le.mpr v.toMul.property)
    rw [card_twoResidual_of_card_six (hh.trans hcard)]
    decide
  have hI := caseI_residual_intersection T M Mc V (zpowers (v.toMul : G))
    h.normalized (zpowers_le.mpr v.toMul.property) hNMc hTMc hMnot hgenZ hSylZ hprime
  have hYout : ¬ Y ≤ d.MZ := by
    intro hb
    have hYH : Y ≤ M ⊓ Mc ⊓ centralizer (zpowers (v.toMul : G) : Set G) := by
      intro y hy
      have hc : y ∈ C := map_subtype_le _ hy
      exact ⟨⟨hc.1,(hb hy).2⟩,by simpa only [CaseIComponentData.G1,hdZ] using hc.2⟩
    have hh := embedded_pResidual_mono 2 hYH
    rw [(pResidual_eq_top_iff 2 Y).mpr hYp,
      ←MonoidHom.range_eq_map,range_subtype,hI] at hh
    exact hYnon (hh.trans ((map_subtype_le _).trans inf_le_right))
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ d.S := by
    by_contra! hh
    have he := relIndex_eq_one.mpr hh
    rw [haction.1] at he
    contradiction
  have hSnT := chosen_nine_centralizer_normal T hM.1.2 h.normalized
    (hZ.trans inf_le_left) h9
  have hTn := h.caseI_T_normalizes_MZ_from_source hG T hempty hM hJ hu hZ hSylZ hSnT hI hres
  obtain ⟨hcontrol,hcoreN⟩ := CaseIMarkedSubgroup.core_normalizer_control
    hZ hZne hgenZ hM hu hne h hres hTn
  have hQne := CaseIMarkedSubgroup.core_nontrivial hZ hZne hM hu h
  have hTn' : (T : Subgroup G) ≤ normalizer (d.MZ : Set G) := by
    change (T : Subgroup G) ≤ normalizer (centralizer (d.Z1 : Set G) ⊓ Mc : Set G)
    rw [hdZ]
    exact hTn
  refine ⟨d,{
    row := hdrow
    marked_card := hdcard
    odd_core := hodd
    quasisimple := hq
    local_component := hL
    component_sylow := hSL
    centralizer_sylow := hSylG
    outside_M := d.L_not_le_M hG T hempty hM hu
    ordinary := d.ordinarySource hG hu h hM.1.2 hSylG hodd
    fixed_card := hplanes.1
    moving_card := hplanes.2.1
    planes_sup := hplanes.2.2.1
    planes_inf := hplanes.2.2.2.1
    marked_le_fixed := hplanes.2.2.2.2
    index := haction.1
    sylow_normal := ?_
    fixes_planes := ⟨haction.2.1,haction.2.2.1⟩
    fixed_centralizer_index := haction.2.2.2.1
    exchanges := haction.2.2.2.2
    exchange_exists := ⟨t,ht,htS⟩
    cubic_escape := hYout
    cubic_idempotent := hYid
    cubic_two_perfect := hYp
    cubic_normalizes := hYV
    cubic_commutator := he
    cubic_moving := hV2Y
    fixed_noncentral := ?_
    seed_bound := ?_
    moving_noncentral := hmove
    core_nontrivial := ?_
    characteristic_control := ?_
    core_normalizer := ?_
    sylow_normalizes_MZ := hTn'
    sylow_normalizes_Q1 := d.T_normalizes_Q1_of_T_normalizes_MZ hTn' }⟩
  · simpa only [CaseIComponentData.S,hdZ] using hSnT
  · intro hf
    let := hq
    exact d.fixed_plane_not_centralizes hG hf V1 V2 Y hplanes.2.2.2.2
      ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) hV2ne hYid hV2Y t
      ((haction.2.2.2.2 t ht htS).2)
  · have hh := marked_fixedSpace_seed_bound T h.normalized v K hK hbound
    change centralInvolutions T ⊓ V ≤ d.Z1 ⊔
      ⁅V,(pResidual 2 (M ⊓ centralizer (d.Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (d.Z1 : Set G)).subtype⁆
    rw [hdZ]
    exact hh
  · simpa only [CaseIComponentData.Q1,CaseIComponentData.MZ,CaseIComponentData.G1,hdZ] using hQne
  · simpa only [CaseIComponentData.Q1,CaseIComponentData.MZ,CaseIComponentData.G1,hdZ] using hcontrol
  · simpa only [CaseIComponentData.Q1,CaseIComponentData.MZ,CaseIComponentData.G1,hdZ] using hcoreN
end CFSG.Quasithin.Chapter15.Section01
